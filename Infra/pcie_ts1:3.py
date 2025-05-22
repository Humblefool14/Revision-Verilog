#!/usr/bin/env python3
"""
TS1/TS2 Ordered Set Parser
Parses training sequence ordered sets and displays information in a concise format.
Each ordered set is 16 symbols (bytes) for Gen1/2, with some variations for Gen3+.
Updated to handle equalization and coefficient fields for Gen3+ (8.0 GT/s and 16.0 GT/s).
"""

import sys
from typing import List, Dict, Tuple, Optional

class TSParser:
    def __init__(self):
        # TS1 and TS2 identifiers 
        self.TS1_ID = 0x1E  # TS1 identifier (symbol 0) - COM (K28.3) for Gen1/2, 8'h1E for Gen3
        self.TS2_ID = 0x2D  # TS2 identifier (symbol 0) - COM (K28.3) for Gen1/2, different for Gen3
        
        # TS1/TS2 identifiers for later symbols (generation dependent)
        # Gen1/2 uses D10.2 and D5.2, Gen3 uses different values
        self.TS1_ID_GEN12 = 0x4A  # D10.2 = 4Ah for Gen1/2
        self.TS2_ID_GEN12 = 0x45  # D5.2 = 45h for Gen1/2
        self.TS1_ID_GEN3 = 0x4A   # 8'h4A for Gen3
        self.TS2_ID_GEN3 = 0x45   # 8'h45 for Gen3
        
        # DC balance control symbols
        self.DC_BALANCE_SYMBOLS = {
            0xDF: "DFh (reduce 0s - high imbalance)",
            0xF7: "F7h (PAD/reduce 0s)",
            0x20: "20h (reduce 1s - high imbalance)", 
            0x08: "08h (reduce 1s)"
        }
        
        # Symbol definitions for TS ordered sets
        self.PAD_SYMBOL = 0xF7
        self.STP_SYMBOL = 0xFB  # Start of Packet
        self.SDP_SYMBOL = 0x5C  # Start of Data Packet
        self.END_SYMBOL = 0xFD  # End
        self.EDB_SYMBOL = 0xFE  # End Bad
        
        # Link/Lane numbers
        self.LINK_NUMBERS = {
            0x00: "PAD", 0x01: "L01", 0x02: "L02", 0x03: "L03", 0x04: "L04",
            0x05: "L05", 0x06: "L06", 0x07: "L07", 0x08: "L08", 0x09: "L09",
            0x0A: "L10", 0x0B: "L11", 0x0C: "L12", 0x0D: "L13", 0x0E: "L14",
            0x0F: "L15", 0x10: "L16", 0x11: "L17", 0x12: "L18", 0x13: "L19",
            0x14: "L20", 0x15: "L21", 0x16: "L22", 0x17: "L23", 0x18: "L24",
            0x19: "L25", 0x1A: "L26", 0x1B: "L27", 0x1C: "L28", 0x1D: "L29",
            0x1E: "L30", 0x1F: "L31"
        }
        
        # Rate identifiers (symbol 4 - bits 2:0)
        self.RATES = {
            0x00: "2.5GT/s (Gen1)", 0x01: "5.0GT/s (Gen2)", 0x02: "8.0GT/s (Gen3)", 
            0x03: "16.0GT/s (Gen4)", 0x04: "32.0GT/s (Gen5)", 0x05: "64.0GT/s (Gen6)"
        }
        
        # Symbol 4 bit field definitions
        self.SYMBOL4_SPEED_CHANGE_BIT = 0x80    # Bit 7: Speed Change
        self.SYMBOL4_AUTO_DEEMPH_BIT = 0x40     # Bit 6: Autonomous Change Deemphasis
        # Bits 5:3 are Reserved
        # Bits 2:0 are Data Rate
        
        # Training control bits (symbol 5)
        self.TRAINING_CTRL = {
            0x01: "Hot Reset",
            0x02: "Disable Link", 
            0x04: "Loopback",
            0x08: "Disable Scrambling",
            0x10: "Compliance Receive",
            0x20: "Autonomous Change"
        }
        
        # Equalization Control values (Symbol 6, bits 1:0 for Gen3+)
        self.EQ_CONTROL = {
            0x00: "00b - Must be used in all LTSSM states except Recovery.Equalization and Loopback",
            0x01: "01b - Phase 2/3 Equalization (FS/LF evaluation)",
            0x02: "10b - Reserved",
            0x03: "11b - Reserved"
        }

    def parse_file(self, filename: str) -> None:
        """Parse TS ordered sets from a binary file."""
        try:
            with open(filename, 'rb') as file:
                data = file.read()
                self.parse_data(data)
        except FileNotFoundError:
            print(f"Error: File '{filename}' not found.")
        except Exception as e:
            print(f"Error reading file: {e}")

    def parse_data(self, data: bytes) -> None:
        """Parse binary data containing TS ordered sets."""
        if len(data) % 16 != 0:
            print(f"Warning: Data length ({len(data)}) is not a multiple of 16 symbols")
        
        print("=" * 80)
        print("TS1/TS2 Ordered Set Parser Results")
        print("=" * 80)
        
        os_count = 0
        pos = 0
        
        while pos + 16 <= len(data):
            symbols = data[pos:pos+16]
            os_count += 1
            
            print(f"\nOrdered Set #{os_count} (Position: {pos}-{pos+15}):")
            print("-" * 50)
            
            # Display raw symbols
            hex_str = ' '.join(f'{b:02X}' for b in symbols)
            print(f"Raw Data: {hex_str}")
            
            # Parse the ordered set
            self.parse_ordered_set(symbols, os_count)
            
            # Add DC balance analysis
            self.analyze_dc_balance(symbols, os_count)
            
            pos += 16
        
        if pos < len(data):
            remaining = len(data) - pos
            print(f"\nWarning: {remaining} remaining bytes (incomplete ordered set)")
            hex_str = ' '.join(f'{b:02X}' for b in data[pos:])
            print(f"Remaining: {hex_str}")

    def get_generation_from_rate(self, rate_val: int) -> int:
        """Determine PCIe generation from rate value (bits 2:0 of symbol 4)."""
        rate_bits = rate_val & 0x07  # Extract only the rate bits
        if rate_bits <= 1:
            return 2  # Gen1/2
        elif rate_bits == 2:
            return 3  # Gen3
        else:
            return 4  # Gen4+

    def is_gen3_plus_rate(self, rate: int) -> bool:
        """Check if the rate requires Gen3+ equalization handling (8.0 GT/s or 16.0 GT/s)."""
        return rate >= 2  # 8.0 GT/s (0x02) or higher

    def calculate_parity(self, symbol6: int, symbol7: int, symbol8: int, symbol9: int) -> bool:
        """Calculate even parity for symbols 6-9 (Gen3+ TS1 only)."""
        # Combine all bits from symbols 6, 7, 8 and bits 6:0 of symbol 9
        all_bits = (symbol6 << 16) | (symbol7 << 8) | symbol8 | (symbol9 & 0x7F)
        
        # Count number of 1s
        ones_count = bin(all_bits).count('1')
        
        # Even parity: total number of 1s (including parity bit) should be even
        expected_parity = ones_count % 2
        actual_parity = (symbol9 >> 7) & 1
        
        return expected_parity == actual_parity

    def parse_ordered_set(self, symbols: bytes, os_num: int) -> None:
        """Parse a single 16-symbol ordered set."""
        if len(symbols) != 16:
            print("Error: Ordered set must be exactly 16 symbols")
            return
        
        # Symbol 0: TS identifier
        ts_id = symbols[0]
        if ts_id == self.TS1_ID:
            ts_type = "TS1"
        elif ts_id == self.TS2_ID:
            ts_type = "TS2"
        else:
            ts_type = f"Unknown (0x{ts_id:02X})"
        
        print(f"Type: {ts_type}")
        
        # Symbol 1: Link number
        link_num = symbols[1]
        link_str = self.LINK_NUMBERS.get(link_num, f"Unknown (0x{link_num:02X})")
        print(f"Link Number: {link_str}")
        
        # Symbol 2: Lane number  
        lane_num = symbols[2]
        lane_str = self.LINK_NUMBERS.get(lane_num, f"Unknown (0x{lane_num:02X})")
        print(f"Lane Number: {lane_str}")
        
        # Symbol 3: N_FTS (Number of Fast Training Sequences)
        n_fts = symbols[3]
        print(f"N_FTS: {n_fts} (0x{n_fts:02X})")
        
        # Symbol 4: Data rate identifier with additional fields
        symbol_4 = symbols[4]
        
        # Extract individual fields from Symbol 4
        speed_change = bool(symbol_4 & self.SYMBOL4_SPEED_CHANGE_BIT)
        auto_deemph = bool(symbol_4 & self.SYMBOL4_AUTO_DEEMPH_BIT)
        reserved_bits = (symbol_4 >> 3) & 0x07  # Bits 5:3
        rate = symbol_4 & 0x07  # Bits 2:0
        
        rate_str = self.RATES.get(rate, f"Unknown (0x{rate:02X})")
        print(f"Symbol 4 Analysis (0x{symbol_4:02X}):")
        print(f"  Data Rate: {rate_str}")
        print(f"  Speed Change: {'Yes' if speed_change else 'No'}")
        print(f"  Auto Change Deemphasis: {'Yes' if auto_deemph else 'No'}")
        if reserved_bits != 0:
            print(f"  Reserved bits (5:3): 0x{reserved_bits:X} (should be 0)")
        
        # Determine generation and equalization mode
        generation = self.get_generation_from_rate(rate)
        gen3_plus_eq_mode = self.is_gen3_plus_rate(rate)
        
        # Symbol 5: Training control
        training_ctrl = symbols[5]
        ctrl_bits = []
        for bit_val, description in self.TRAINING_CTRL.items():
            if training_ctrl & bit_val:
                ctrl_bits.append(description)
        
        if ctrl_bits:
            print(f"Training Control: {', '.join(ctrl_bits)} (0x{training_ctrl:02X})")
        else:
            print(f"Training Control: No Action (0x{training_ctrl:02X})")
        
        # Symbols 6-9: Parse based on generation and data rate
        if gen3_plus_eq_mode:
            self.parse_gen3_plus_equalization(symbols, ts_type, rate)
        else:
            self.parse_gen1_gen2_symbols(symbols, ts_type, generation)
        
        # Symbols 10-13: TS identifiers (consistent across generations)
        symbols_10_13 = symbols[10:14]
        
        if ts_type == "TS1":
            expected_id = self.TS1_ID_GEN12 if generation <= 2 else self.TS1_ID_GEN3
            expected_name = "TS1 ID"
        elif ts_type == "TS2":
            expected_id = self.TS2_ID_GEN12 if generation <= 2 else self.TS2_ID_GEN3
            expected_name = "TS2 ID"
        else:
            expected_id = None
            expected_name = "Unknown"
        
        print(f"Symbols 10-13: {expected_name} identifiers")
        
        if expected_id is not None:
            correct_count = sum(1 for b in symbols_10_13 if b == expected_id)
            if correct_count == 4:
                rate_desc = self.RATES.get(rate & 0x07, f"0x{rate & 0x07:02X}")
                gen_desc = f"Gen{generation}" if generation <= 3 else f"Gen{generation}+"
                print(f"  All correct (0x{expected_id:02X}) for {rate_desc} {gen_desc} - OK")
            else:
                print(f"  Expected: 0x{expected_id:02X} ({expected_name})")
                print(f"  Actual: {' '.join(f'0x{b:02X}' for b in symbols_10_13)}")
                print(f"  Correct: {correct_count}/4 symbols")
        else:
            print(f"  Values: {' '.join(f'0x{b:02X}' for b in symbols_10_13)}")
        
        # Symbols 14-15: TS ID or DC balance control (generation dependent)
        symbol_14 = symbols[14]
        symbol_15 = symbols[15]
        
        print(f"Symbol 14: Analysis")
        if symbol_14 in self.DC_BALANCE_SYMBOLS:
            print(f"  DC Balance Control: {self.DC_BALANCE_SYMBOLS[symbol_14]} (0x{symbol_14:02X})")
        elif generation >= 3 and symbol_14 in [self.TS1_ID_GEN3, self.TS2_ID_GEN3]:
            ts_name = "TS1" if symbol_14 == self.TS1_ID_GEN3 else "TS2"
            print(f"  {ts_name} ID for Gen3+ (0x{symbol_14:02X})")
        elif symbol_14 == self.PAD_SYMBOL:
            print(f"  PAD symbol (0x{symbol_14:02X}) - Normal")
        else:
            print(f"  Custom/Unknown value (0x{symbol_14:02X})")
        
        print(f"Symbol 15: Analysis")
        if symbol_15 in self.DC_BALANCE_SYMBOLS:
            print(f"  DC Balance Control: {self.DC_BALANCE_SYMBOLS[symbol_15]} (0x{symbol_15:02X})")
        elif generation >= 3 and symbol_15 in [self.TS1_ID_GEN3, self.TS2_ID_GEN3]:
            ts_name = "TS1" if symbol_15 == self.TS1_ID_GEN3 else "TS2"
            print(f"  {ts_name} ID for Gen3+ (0x{symbol_15:02X})")
        elif symbol_15 == self.PAD_SYMBOL:
            print(f"  PAD symbol (0x{symbol_15:02X}) - Normal")
        else:
            print(f"  Custom/Unknown value (0x{symbol_15:02X})")
        
        # Validation summary
        is_valid = self.validate_ordered_set(symbols, ts_type, generation)
        status = "✓ VALID" if is_valid else "✗ INVALID"
        print(f"Validation: {status}")

    def parse_gen3_plus_equalization(self, symbols: bytes, ts_type: str, rate: int) -> None:
        """Parse symbols 6-9 for Gen3+ (8.0 GT/s and 16.0 GT/s) equalization."""
        symbol_6 = symbols[6]
        symbol_7 = symbols[7]
        symbol_8 = symbols[8]
        symbol_9 = symbols[9]
        
        print(f"Gen3+ Equalization Mode ({self.RATES.get(rate, 'Unknown')})")
        
        # Symbol 6 analysis
        print(f"Symbol 6 Analysis (0x{symbol_6:02X}):")
        
        # Bits 1:0 - Equalization Control (EC)
        ec = symbol_6 & 0x03
        ec_desc = self.EQ_CONTROL.get(ec, f"Unknown EC value: {ec}")
        print(f"  Equalization Control (EC): {ec_desc}")
        
        # Bit 2 - Reset EIEOS Interval Count (for Recovery.Equalization state only)
        reset_eieos = bool(symbol_6 & 0x04)
        print(f"  Reset EIEOS Interval Count: {'Yes' if reset_eieos else 'No'} (bit 2)")
        
        # Bits 6:3 - Transmitter Preset
        tx_preset = (symbol_6 >> 3) & 0x0F
        print(f"  Transmitter Preset: {tx_preset} (bits 6:3)")
        
        # Bit 7 - Use Preset/Equalization Redo
        use_preset_redo = bool(symbol_6 & 0x80)
        print(f"  Use Preset/Equalization Redo: {'Yes' if use_preset_redo else 'No'} (bit 7)")
        
        # Symbol 7 analysis (depends on EC field and TS type)
        print(f"Symbol 7 Analysis (0x{symbol_7:02X}):")
        if ts_type == "TS1":
            if ec == 0x01:  # Phase 2/3 Equalization
                fs = symbol_7 & 0x3F  # Bits 5:0
                reserved_bit6 = bool(symbol_7 & 0x40)
                retimer_eq_extend = bool(symbol_7 & 0x80) if rate == 0x03 else False  # Only for 16.0 GT/s
                
                print(f"  FS (Figure of merit for Sum): {fs} (bits 5:0)")
                if reserved_bit6:
                    print(f"  Reserved bit 6: 1 (should be 0)")
                if rate == 0x03:  # 16.0 GT/s
                    print(f"  Retimer Equalization Extend: {'Yes' if retimer_eq_extend else 'No'} (bit 7)")
                elif symbol_7 & 0x80:
                    print(f"  Bit 7: 1 (reserved for this data rate)")
            else:
                # Pre-cursor Coefficient
                pre_cursor = symbol_7 & 0x3F  # Bits 5:0
                reserved_bit6 = bool(symbol_7 & 0x40)
                retimer_eq_extend = bool(symbol_7 & 0x80) if rate == 0x03 else False
                
                print(f"  Pre-cursor Coefficient: {pre_cursor} (bits 5:0)")
                if reserved_bit6:
                    print(f"  Reserved bit 6: 1 (should be 0)")
                if rate == 0x03:
                    print(f"  Retimer Equalization Extend: {'Yes' if retimer_eq_extend else 'No'} (bit 7)")
        else:  # TS2
            print(f"  TS2 Symbol 7: 0x{symbol_7:02X} (TS2-specific encoding)")
        
        # Symbol 8 analysis
        print(f"Symbol 8 Analysis (0x{symbol_8:02X}):")
        if ts_type == "TS1":
            if ec == 0x01:  # Phase 2/3 Equalization
                lf = symbol_8 & 0x3F  # Bits 5:0
                reserved_bits = (symbol_8 >> 6) & 0x03  # Bits 7:6
                
                print(f"  LF (Figure of merit for Low Frequency): {lf} (bits 5:0)")
                if reserved_bits != 0:
                    print(f"  Reserved bits 7:6: 0x{reserved_bits:X} (should be 0)")
            else:
                # Cursor Coefficient
                cursor = symbol_8 & 0x3F  # Bits 5:0
                reserved_bits = (symbol_8 >> 6) & 0x03  # Bits 7:6
                
                print(f"  Cursor Coefficient: {cursor} (bits 5:0)")
                if reserved_bits != 0:
                    print(f"  Reserved bits 7:6: 0x{reserved_bits:X} (should be 0)")
        else:  # TS2
            print(f"  TS2 Symbol 8: 0x{symbol_8:02X} (TS2-specific encoding)")
        
        # Symbol 9 analysis  
        print(f"Symbol 9 Analysis (0x{symbol_9:02X}):")
        if ts_type == "TS1":
            # Bits 5:0 - Post-cursor Coefficient
            post_cursor = symbol_9 & 0x3F
            print(f"  Post-cursor Coefficient: {post_cursor} (bits 5:0)")
            
            # Bit 6 - Reject Coefficient Values
            reject_coeff = bool(symbol_9 & 0x40)
            print(f"  Reject Coefficient Values: {'Yes' if reject_coeff else 'No'} (bit 6)")
            
            # Bit 7 - Parity
            parity_bit = bool(symbol_9 & 0x80)
            parity_valid = self.calculate_parity(symbol_6, symbol_7, symbol_8, symbol_9)
            parity_status = "✓" if parity_valid else "✗"
            print(f"  Parity: {parity_bit} {parity_status} (bit 7)")
            
            if not parity_valid:
                print("    Warning: Parity check failed - TS1 may be corrupted")
        else:  # TS2
            print(f"  TS2 Symbol 9: 0x{symbol_9:02X} (TS2-specific encoding)")

    def parse_gen1_gen2_symbols(self, symbols: bytes, ts_type: str, generation: int) -> None:
        """Parse symbols 6-9 for Gen1/Gen2 (2.5 GT/s and 5.0 GT/s)."""
        print(f"Gen1/Gen2 Mode")
        
        # Symbol 6: Generation-specific content
        symbol_6 = symbols[6]
        if ts_type == "TS1":
            print(f"Symbol 6: TS1 ID with Equalization Info (0x{symbol_6:02X})")
            # Could contain transmitter preset, receiver preset hint, etc.
        else:
            print(f"Symbol 6: TS2 ID with EQ Request (0x{symbol_6:02X})")
        
        # Symbols 7-9: TS identifiers with embedded data
        for i in range(7, 10):
            sym_val = symbols[i]
            if ts_type == "TS1":
                expected_base = self.TS1_ID_GEN12
                print(f"Symbol {i}: TS1 ID with embedded data (0x{sym_val:02X})")
            else:
                expected_base = self.TS2_ID_GEN12  
                print(f"Symbol {i}: TS2 ID with embedded data (0x{sym_val:02X})")

    def calculate_dc_balance(self, byte_val: int) -> int:
        """Calculate DC balance for a single byte (number of 1s - number of 0s)."""
        ones = bin(byte_val).count('1')
        zeros = 8 - ones
        return ones - zeros

    def analyze_dc_balance(self, symbols: bytes, os_num: int) -> None:
        """Analyze DC balance and validate symbols 14-15 based on PCIe spec."""
        print(f"\nDC Balance Analysis for Ordered Set #{os_num}:")
        print("-" * 50)
        
        running_balance = 0
        
        # Calculate running DC balance through symbol 13 (since we now have 16 symbols)
        for i in range(14):  # Symbols 0-13
            symbol_balance = self.calculate_dc_balance(symbols[i])
            running_balance += symbol_balance
            print(f"Symbol {i:2d}: 0x{symbols[i]:02X} -> Balance: {symbol_balance:+3d}, Running: {running_balance:+4d}")
        
        print(f"\nDC Balance at end of Symbol 13: {running_balance:+d}")
        
        # Analyze symbols 14-15 based on DC balance
        symbol_14 = symbols[14]
        symbol_15 = symbols[15]
        
        # Analyze according to PCIe specification
        if abs(running_balance) > 31:
            print(f"High DC imbalance (|{running_balance}| > 31):")
            if running_balance > 31:
                # Too many 1s, need to reduce 1s
                expected_14 = 0x20  # 20h to reduce 1s
                expected_15 = 0x08  # 08h to reduce 1s
                print("  Expected: Symbol 14=20h, Symbol 15=08h (reduce 1s)")
            else:
                # Too many 0s, need to reduce 0s  
                expected_14 = 0xDF  # DFh to reduce 0s
                expected_15 = 0xF7  # F7h to reduce 0s
                print("  Expected: Symbol 14=DFh, Symbol 15=F7h (reduce 0s)")
            
            # Check actual values
            status_14 = "✓" if symbol_14 == expected_14 else "✗"
            print(f"  Actual Symbol 14: 0x{symbol_14:02X} {status_14}")
            
            status_15 = "✓" if symbol_15 == expected_15 else "✗"
            print(f"  Actual Symbol 15: 0x{symbol_15:02X} {status_15}")
                
        elif abs(running_balance) > 15:
            print(f"Medium DC imbalance (|{running_balance}| > 15):")
            # Symbol 14 should be normal TS identifier
            ts_type = "TS1" if symbols[0] == self.TS1_ID else "TS2"
            expected_14 = self.TS1_ID_GEN12 if ts_type == "TS1" else self.TS2_ID_GEN12
            
            if running_balance > 15:
                # Too many 1s, need to reduce 1s in symbol 15
                expected_15 = 0x08  # 08h to reduce 1s
                print(f"  Expected: Symbol 14={expected_14:02X}h (normal {ts_type}), Symbol 15=08h (reduce 1s)")
            else:
                # Too many 0s, need to reduce 0s in symbol 15
                expected_15 = 0xF7  # F7h to reduce 0s
                print(f"  Expected: Symbol 14={expected_14:02X}h (normal {ts_type}), Symbol 15=F7h (reduce 0s)")
            
            # Check actual values
            status_14 = "✓" if symbol_14 == expected_14 else "✗"
            print(f"  Actual Symbol 14: 0x{symbol_14:02X} {status_14}")
            
            status_15 = "✓" if symbol_15 == expected_15 else "✗"  
            print(f"  Actual Symbol 15: 0x{symbol_15:02X} {status_15}")
                
        else:
            print(f"Low DC imbalance (|{running_balance}| ≤ 15):")
            print("  Expected: Normal TS symbols (no DC balance correction needed)")
            ts_type = "TS1" if symbols[0] == self.TS1_ID else "TS2"
            expected_14 = self.TS1_ID_GEN12 if ts_type == "TS1" else self.TS2_ID_GEN12
            expected_15 = self.PAD_SYMBOL  # F7h
            
            status_14 = "✓" if symbol_14 == expected_14 else "✗"
            print(f"  Actual Symbol 14: 0x{symbol_14:02X} {status_14}")
            
            status_15 = "✓" if symbol_15 == expected_15 else "✗"
            print(f"  Actual Symbol 15: 0x{symbol_15:02X} {status_15}")
        
        # Calculate final balance including symbols 14-15
        final_balance = running_balance
        for i in range(14, 16):
            symbol_balance = self.calculate_dc_balance(symbols[i])
            final_balance += symbol_balance
        
        print(f"\nFinal DC Balance (all symbols): {final_balance:+d}")
        
        # Assess balance correction effectiveness
        if abs(final_balance) < abs(running_balance):
            print("✓ DC balance correction is effective")
        elif abs(final_balance) == abs(running_balance):
            print("→ DC balance unchanged")
        else:
            print("✗ DC balance correction made imbalance worse")

    def validate_ordered_set(self, symbols: bytes, ts_type: str, generation: int) -> bool:
        """Validate an ordered set according to PCIe specifications."""
        errors = []
        
        # Check symbol 0 (TS identifier)
        ts_id = symbols[0]
        if ts_type == "TS1" and ts_id != self.TS1_ID:
            errors.append(f"Symbol 0: Expected TS1 ID (0x{self.TS1_ID:02X}), got 0x{ts_id:02X}")
        elif ts_type == "TS2" and ts_id != self.TS2_ID:
            errors.append(f"Symbol 0: Expected TS2 ID (0x{self.TS2_ID:02X}), got 0x{ts_id:02X}")
        
        # Check link/lane numbers (symbols 1-2) - should be valid values
        link_num = symbols[1]
        if link_num > 0x1F:
            errors.append(f"Symbol 1: Invalid link number 0x{link_num:02X} (max 0x1F)")
        
        lane_num = symbols[2]
        if lane_num > 0x1F:
            errors.append(f"Symbol 2: Invalid lane number 0x{lane_num:02X} (max 0x1F)")
        
        # Check symbol 4 reserved bits
        symbol_4 = symbols[4]
        reserved_bits = (symbol_4 >> 3) & 0x07
        if reserved_bits != 0:
            errors.append(f"Symbol 4: Reserved bits 5:3 should be 0, got 0x{reserved_bits:X}")
        
        # Check data rate validity
        rate = symbol_4 & 0x07
        if rate > 0x05:
            errors.append(f"Symbol 4: Invalid data rate 0x{rate:X} (max 0x05)")
        
        # Check symbols 10-13 consistency
        expected_id = self.TS1_ID_GEN12 if ts_type == "TS1" else self.TS2_ID_GEN12
        if generation >= 3:
            expected_id = self.TS1_ID_GEN3 if ts_type == "TS1" else self.TS2_ID_GEN3
        
        symbols_10_13 = symbols[10:14]
        incorrect_count = sum(1 for b in symbols_10_13 if b != expected_id)
        if incorrect_count > 0:
            errors.append(f"Symbols 10-13: {incorrect_count}/4 symbols incorrect for {ts_type}")
        
        # Gen3+ specific validation
        if self.is_gen3_plus_rate(rate) and ts_type == "TS1":
            # Check parity for TS1 in Gen3+
            if not self.calculate_parity(symbols[6], symbols[7], symbols[8], symbols[9]):
                errors.append("Gen3+ TS1: Parity check failed in symbol 9")
        
        if errors:
            print("Validation Errors:")
            for error in errors:
                print(f"  • {error}")
            return False
        
        return True

    def parse_hex_string(self, hex_string: str) -> None:
        """Parse TS ordered sets from a hex string (space-separated or continuous)."""
        # Remove spaces and convert to uppercase
        hex_clean = hex_string.replace(' ', '').replace('\n', '').replace('\t', '').upper()
        
        # Validate hex characters
        if not all(c in '0123456789ABCDEF' for c in hex_clean):
            print("Error: Invalid hex characters in input")
            return
        
        # Convert to bytes
        if len(hex_clean) % 2 != 0:
            print("Error: Hex string must have even number of characters")
            return
        
        try:
            data = bytes.fromhex(hex_clean)
            self.parse_data(data)
        except ValueError as e:
            print(f"Error parsing hex string: {e}")

    def generate_summary_report(self, data: bytes) -> None:
        """Generate a summary report of all ordered sets in the data."""
        if len(data) % 16 != 0:
            print(f"Warning: Data length ({len(data)}) is not a multiple of 16 symbols")
        
        print("\n" + "=" * 80)
        print("SUMMARY REPORT")
        print("=" * 80)
        
        os_count = len(data) // 16
        ts1_count = 0
        ts2_count = 0
        invalid_count = 0
        rate_counts = {}
        generation_counts = {}
        
        pos = 0
        while pos + 16 <= len(data):
            symbols = data[pos:pos+16]
            
            # Identify TS type
            ts_id = symbols[0]
            if ts_id == self.TS1_ID:
                ts1_count += 1
                ts_type = "TS1"
            elif ts_id == self.TS2_ID:
                ts2_count += 1
                ts_type = "TS2"
            else:
                invalid_count += 1
                ts_type = "Invalid"
            
            # Count rates and generations
            if ts_type != "Invalid":
                rate = symbols[4] & 0x07
                generation = self.get_generation_from_rate(rate)
                
                rate_str = self.RATES.get(rate, f"Unknown-0x{rate:02X}")
                rate_counts[rate_str] = rate_counts.get(rate_str, 0) + 1
                
                gen_str = f"Gen{generation}" if generation <= 6 else f"Gen{generation}+"
                generation_counts[gen_str] = generation_counts.get(gen_str, 0) + 1
            
            pos += 16
        
        print(f"Total Ordered Sets: {os_count}")
        print(f"TS1 Count: {ts1_count}")
        print(f"TS2 Count: {ts2_count}")
        if invalid_count > 0:
            print(f"Invalid/Unknown Count: {invalid_count}")
        
        if rate_counts:
            print("\nData Rates:")
            for rate, count in sorted(rate_counts.items()):
                print(f"  {rate}: {count} ordered sets")
        
        if generation_counts:
            print("\nPCIe Generations:")
            for gen, count in sorted(generation_counts.items()):
                print(f"  {gen}: {count} ordered sets")


def main():
    """Main function to handle command line arguments and run the parser."""
    parser = TSParser()
    
    if len(sys.argv) < 2:
        print("TS1/TS2 Ordered Set Parser")
        print("Usage:")
        print("  python3 pcie_ts_parser.py <binary_file>")
        print("  python3 pcie_ts_parser.py --hex <hex_string>")
        print("  python3 pcie_ts_parser.py --summary <binary_file>")
        print("\nExamples:")
        print("  python3 pcie_ts_parser.py ts_data.bin")
        print("  python3 pcie_ts_parser.py --hex '1E 00 01 02 03 04 05 06 07 08 4A 4A 4A 4A 4A F7'")
        print("  python3 pcie_ts_parser.py --summary ts_data.bin")
        sys.exit(1)
    
    if sys.argv[1] == "--hex":
        if len(sys.argv) < 3:
            print("Error: Hex string required after --hex")
            sys.exit(1)
        hex_string = ' '.join(sys.argv[2:])
        parser.parse_hex_string(hex_string)
    
    elif sys.argv[1] == "--summary":
        if len(sys.argv) < 3:
            print("Error: Filename required after --summary")
            sys.exit(1)
        filename = sys.argv[2]
        try:
            with open(filename, 'rb') as file:
                data = file.read()
                parser.generate_summary_report(data)
        except FileNotFoundError:
            print(f"Error: File '{filename}' not found.")
        except Exception as e:
            print(f"Error reading file: {e}")
    
    else:
        filename = sys.argv[1]
        parser.parse_file(filename)


if __name__ == "__main__":
    main()