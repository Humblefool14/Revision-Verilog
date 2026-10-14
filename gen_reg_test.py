#!/usr/bin/env python3
"""
gen_reg_test.py

Parses a register header file that defines registers using the convention:

    #define <PREFIX>__<REGNAME>__OFFSET      <value>
    #define <PREFIX>__<REGNAME>__WRITEMASK   <value>
    #define <PREFIX>__<REGNAME>__READMASK    <value>

e.g.
    #define DV__CAR__PLL0_CFG0__OFFSET       0x00000010U
    #define DV__CAR__PLL0_CFG0__WRITEMASK    0xFFFFFFFFU
    #define DV__CAR__PLL0_CFG0__READMASK     0xFFFFFFFFU

For each register it classifies it as:
    - RO (read-only)   : WRITEMASK == 0
    - WO (write-only)  : READMASK  == 0
    - RW (read/write)  : both non-zero
    - SKIP              : neither writable nor readable (both masks 0) -- unusual, flagged

It then emits a .c file that, for every register:
    - RW : writes a masked test pattern, reads it back, and checks it
    - RO : reads and prints the value only
    - WO : writes a masked test pattern only (no read-back, since HW can't be read)

The base address macro is derived from the register key by dropping the last
"__segment" and appending "__BASE", e.g.

    DV__CAR__PLL0_CFG0   ->   DV__CAR__BASE

Usage:
    python3 gen_reg_test.py <input_header.h> [-o output.c] [-p 0xA5A5A5A5]
"""

import re
import sys
import argparse
from collections import OrderedDict

DEFINE_RE = re.compile(
    r'^\s*#\s*define\s+(\S+)\s+(.+?)\s*(?://.*|/\*.*\*/\s*)?$'
)

SUFFIX_MAP = {
    'OFFSET': 'offset',
    'WRITEMASK': 'writemask',
    'READMASK': 'readmask',
}


def extract_numeric(value_str):
    """Best-effort extraction of an integer value from a #define RHS."""
    m = re.search(r'0[xX][0-9a-fA-F]+', value_str)
    if m:
        return int(m.group(0), 16)
    m = re.search(r'-?\d+', value_str)
    if m:
        return int(m.group(0))
    return None


def parse_header(path):
    regs = OrderedDict()  # key -> {'offset': (name,val,raw), 'writemask':..., 'readmask':...}

    with open(path, 'r') as f:
        for line in f:
            m = DEFINE_RE.match(line)
            if not m:
                continue
            name, raw_val = m.group(1), m.group(2).strip()

            matched_suffix = None
            for suf in ('OFFSET', 'WRITEMASK', 'READMASK'):
                if name.endswith('__' + suf):
                    matched_suffix = suf
                    break
            if matched_suffix is None:
                continue

            key = name[: -(len('__' + matched_suffix))]
            val = extract_numeric(raw_val)

            regs.setdefault(key, {})
            regs[key][SUFFIX_MAP[matched_suffix]] = {
                'macro': name,
                'raw': raw_val,
                'val': val,
            }

    return regs


def base_macro_for(key):
    parts = key.split('__')
    if len(parts) < 2:
        return key + '__BASE'
    return '__'.join(parts[:-1]) + '__BASE'


def classify(reg):
    wm = reg.get('writemask', {}).get('val')
    rm = reg.get('readmask', {}).get('val')

    has_offset = 'offset' in reg
    if not has_offset:
        return 'INVALID'

    writable = wm is not None and wm != 0
    readable = rm is not None and rm != 0

    # If a mask macro wasn't found at all, assume permissive (treat as fully
    # writable/readable) rather than silently skipping the register.
    if 'writemask' not in reg:
        writable = True
    if 'readmask' not in reg:
        readable = True

    if writable and readable:
        return 'RW'
    if writable and not readable:
        return 'WO'
    if readable and not writable:
        return 'RO'
    return 'SKIP'  # both masks present and zero -- unusual, flag it


def c_ident(key):
    return re.sub(r'[^A-Za-z0-9_]', '_', key)


def generate_c(regs, header_path, test_pattern, out_path):
    lines = []
    lines.append('/*')
    lines.append(' * Auto-generated register read/write test.')
    lines.append(f' * Source header : {header_path}')
    lines.append(' * Generator     : gen_reg_test.py')
    lines.append(' *')
    lines.append(' * Classification rules:')
    lines.append(' *   WRITEMASK == 0            -> read-only  (RO): read only, no write')
    lines.append(' *   READMASK  == 0             -> write-only (WO): write only, no read')
    lines.append(' *   both non-zero              -> read/write (RW): write, read back, check')
    lines.append(' *   both zero (or missing)      -> flagged SKIP, not exercised')
    lines.append(' *')
    lines.append(' * Writes are masked with WRITEMASK; read-back checks are masked with')
    lines.append(' * (WRITEMASK & READMASK) so reserved / non-writable / non-readable bits')
    lines.append(' * are never compared.')
    lines.append(' */')
    lines.append('')
    lines.append(f'#include "{header_path}"')
    lines.append('#include <stdint.h>')
    lines.append('#include <stdio.h>')
    lines.append('')
    lines.append('/* Provided by the platform / test environment. */')
    lines.append('extern void     regWrite(uint32_t addr, uint32_t data);')
    lines.append('extern uint32_t regRead(uint32_t addr);')
    lines.append('')
    lines.append(f'#define TEST_PATTERN {test_pattern}U')
    lines.append('')
    lines.append('static int g_fail_count = 0;')
    lines.append('')

    counts = {'RW': 0, 'RO': 0, 'WO': 0, 'SKIP': 0, 'INVALID': 0}

    body = []
    for key, reg in regs.items():
        cls = classify(reg)
        counts[cls] += 1
        if cls == 'INVALID':
            continue  # no offset -- can't do anything

        ident = c_ident(key)
        base_macro = base_macro_for(key)
        offset_macro = reg['offset']['macro']
        addr_expr = f'({base_macro} + {offset_macro})'

        body.append(f'    /* {key}  [{cls}] */')
        body.append('    {')
        body.append(f'        const uint32_t addr = {addr_expr};')

        if cls == 'RW':
            wm_macro = reg['writemask']['macro']
            rm_macro = reg['readmask']['macro']
            body.append(f'        const uint32_t write_data = TEST_PATTERN & {wm_macro};')
            body.append('        uint32_t read_data;')
            body.append('')
            body.append('        regWrite(addr, write_data);')
            body.append('        read_data = regRead(addr);')
            body.append('')
            body.append(f'        if ((read_data & {rm_macro} & {wm_macro}) != (write_data & {rm_macro})) {{')
            body.append(f'            printf("[FAIL] {key}: wrote 0x%08X, read 0x%08X (addr 0x%08X)\\n",')
            body.append('                   write_data, read_data, addr);')
            body.append('            g_fail_count++;')
            body.append('        } else {')
            body.append(f'            printf("[PASS] {key}: wrote 0x%08X, read 0x%08X (addr 0x%08X)\\n",')
            body.append('                   write_data, read_data, addr);')
            body.append('        }')

        elif cls == 'RO':
            body.append('        uint32_t read_data = regRead(addr);')
            body.append(f'        printf("[INFO] {key}: read-only, read 0x%08X (addr 0x%08X)\\n",')
            body.append('               read_data, addr);')

        elif cls == 'WO':
            wm_macro = reg['writemask']['macro']
            body.append(f'        const uint32_t write_data = TEST_PATTERN & {wm_macro};')
            body.append('        regWrite(addr, write_data);')
            body.append(f'        printf("[INFO] {key}: write-only, wrote 0x%08X (addr 0x%08X, not read back)\\n",')
            body.append('               write_data, addr);')

        elif cls == 'SKIP':
            body.append(f'        (void)addr; /* {key}: WRITEMASK and READMASK both 0 -- not exercised */')
            body.append(f'        printf("[SKIP] {key}: neither readable nor writable\\n");')

        body.append('    }')
        body.append('')

    lines.append('int main(void)')
    lines.append('{')
    lines.append(f'    printf("Register test: %d RW, %d RO, %d WO, %d SKIP, %d INVALID\\n\\n",')
    lines.append(f'           {counts["RW"]}, {counts["RO"]}, {counts["WO"]}, {counts["SKIP"]}, {counts["INVALID"]});')
    lines.append('')
    lines.extend(body)
    lines.append('    printf("\\n%d failure(s)\\n", g_fail_count);')
    lines.append('    return g_fail_count ? 1 : 0;')
    lines.append('}')
    lines.append('')

    with open(out_path, 'w') as f:
        f.write('\n'.join(lines))

    return counts


def main():
    ap = argparse.ArgumentParser(description='Generate a C register read/write test from a register header.')
    ap.add_argument('header', help='Path to the input header file (e.g. x.h)')
    ap.add_argument('-o', '--output', default='reg_test.c', help='Output .c file path (default: reg_test.c)')
    ap.add_argument('-p', '--pattern', default='0xA5A5A5A5',
                     help='32-bit test pattern used for writes, hex (default: 0xA5A5A5A5)')
    args = ap.parse_args()

    regs = parse_header(args.header)
    if not regs:
        print(f'No OFFSET/WRITEMASK/READMASK-style #defines found in {args.header}', file=sys.stderr)
        sys.exit(1)

    counts = generate_c(regs, args.header, args.pattern, args.output)

    print(f'Parsed {len(regs)} register(s) from {args.header}')
    print(f'  RW={counts["RW"]}  RO={counts["RO"]}  WO={counts["WO"]}  '
          f'SKIP={counts["SKIP"]}  INVALID(no offset)={counts["INVALID"]}')
    print(f'Wrote {args.output}')


if __name__ == '__main__':
    main()
