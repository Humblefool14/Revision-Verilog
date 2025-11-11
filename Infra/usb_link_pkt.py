#!/usr/bin/env python3
"""
USB Link Command Parser
Parses USB Link Command packets according to Table 7-4 specifications
Supports: LGOOD_n, LRTY, LBAD, LCRD_x, LCRD1_x, LCRD2_x, LGO_Ux, LAU, LXU, LPMA, LDN, LUP
"""

import csv
import sys
from dataclasses import dataclass
from typing import List, Optional
from enum import Enum


class LinkCommandClass(Enum):
    """Link Command Classes"""
    LGOOD_LCRD = "00"  # LGOOD_n, LRTY, LBAD, LCRD_x, LCRD1_x, LCRD2_x
    LGO_LAU_LXU_LPMA = "01"  # LGO_Ux, LAU, LXU, LPMA
    LDN_LUP = "10"  # LDN, LUP
    RESERVED = "11"  # Reserved


class USBGeneration(Enum):
    """USB Generation for Link Commands"""
    SUPERSPEED = "SuperSpeed"  # Gen 1x1
    SUPERSPEEDPLUS_GEN1X2 = "SuperSpeedPlus Gen1x2"
    SUPERSPEEDPLUS_GEN2X1 = "SuperSpeedPlus Gen2x1"
    SUPERSPEEDPLUS_GEN2X2 = "SuperSpeedPlus Gen2x2"


@dataclass
class LinkCommand:
    """Represents a decoded USB Link Command"""
    raw_value: str
    bit_string: str
    cmd_class: str
    cmd_type: str
    sub_type: str
    description: str
    generation: Optional[USBGeneration] = None
    
    def __str__(self):
        result = [
            f"Raw Value: {self.raw_value}",
            f"Binary: {self.bit_string}",
            f"Class (b10-9): {self.cmd_class}",
            f"Type (b8-7): {self.cmd_type}",
            f"Sub-Type (b6-0): {self.sub_type}",
            f"Description: {self.description}"
        ]
        if self.generation:
            result.append(f"Generation: {self.generation.value}")
        return "\n".join(result)


class USBLinkCommandParser:
    """Parser for USB Link Command packets"""
    
    def __init__(self):
        self.commands: List[LinkCommand] = []
    
    @staticmethod
    def hex_to_binary(hex_str: str) -> str:
        """Convert hex string to 11-bit binary string"""
        # Remove 'h' suffix and '0x' prefix if present
        clean_hex = hex_str.replace('h', '').replace('0x', '').strip()
        try:
            value = int(clean_hex, 16)
            # Return 11-bit binary string
            return format(value, '011b')
        except ValueError:
            return '00000000000'
    
    def decode_lgood_lcrd(self, bits: str, hex_val: str) -> LinkCommand:
        """Decode LGOOD_n, LRTY, LBAD, LCRD_x, LCRD1_x, LCRD2_x commands"""
        b8_7 = bits[3:5]  # Type bits
        b6_4 = bits[5:8]  # Sub-type field
        b3_0 = bits[7:11]  # Lower bits
        
        # Type 00: LGOOD_n
        if b8_7 == "00":
            b3 = bits[7]
            b2_0 = bits[8:11]
            hp_seq = int(b2_0, 2)
            
            # Determine generation
            if b3 == '0':  # SuperSpeed
                gen = USBGeneration.SUPERSPEED
                desc = f"LGOOD_{hp_seq} (HP Sequence Number: {hp_seq})"
            else:  # SuperSpeedPlus
                hp_seq_full = int(b3_0, 2)
                gen = USBGeneration.SUPERSPEEDPLUS_GEN1X2  # Default to Gen1x2
                desc = f"LGOOD_{hp_seq_full} (HP Sequence Number: {hp_seq_full})"
            
            return LinkCommand(
                raw_value=hex_val,
                bit_string=bits,
                cmd_class="00 (Link Command)",
                cmd_type="00 (LGOOD_n)",
                sub_type=b3_0,
                description=desc,
                generation=gen
            )
        
        # Type 01: LCRD_x, LCRD1_x, LCRD2_x
        elif b8_7 == "01":
            b3 = bits[7]
            b2 = bits[8]
            b1_0 = bits[9:11]
            
            credit_series = "LCRD2_x" if b2 == '1' else "LCRD_x or LCRD1_x"
            
            # Determine generation from b3
            if b3 == '0':  # Gen 1x1, Gen 1x2, Gen 2x1
                gen = USBGeneration.SUPERSPEED
                b1_0_val = int(b1_0, 2)
                credit_map = {
                    0: "LCRD_A/LCRD1_A/LCRD2_A",
                    1: "LCRD_B/LCRD1_B/LCRD2_B",
                    2: "LCRD_C/LCRD1_C/LCRD2_C",
                    3: "LCRD_D/LCRD1_D/LCRD2_D"
                }
                credit_type = credit_map.get(b1_0_val, "Unknown")
                desc = f"Link Credit: {credit_type}"
            else:  # Gen 2x2
                gen = USBGeneration.SUPERSPEEDPLUS_GEN2X2
                b2_0_val = int(bits[8:11], 2)
                credit_map = {
                    0: "LCRD1_A/LCRD2_A",
                    1: "LCRD1_B/LCRD2_B",
                    2: "LCRD1_C/LCRD2_C",
                    3: "LCRD1_D/LCRD2_D",
                    4: "LCRD1_E/LCRD2_E",
                    5: "LCRD1_F/LCRD2_F",
                    6: "LCRD1_G/LCRD2_G"
                }
                credit_series_bit = b2
                if credit_series_bit == '0':
                    credit_prefix = "LCRD1"
                else:
                    credit_prefix = "LCRD2"
                credit_type = credit_map.get(b2_0_val, "Reserved")
                desc = f"Link Credit ({credit_prefix}): {credit_type}"
            
            return LinkCommand(
                raw_value=hex_val,
                bit_string=bits,
                cmd_class="00 (Link Command)",
                cmd_type="01 (LCRD_x/LCRD1_x/LCRD2_x)",
                sub_type=b3_0,
                description=desc,
                generation=gen
            )
        
        # Type 10: LRTY
        elif b8_7 == "10":
            return LinkCommand(
                raw_value=hex_val,
                bit_string=bits,
                cmd_class="00 (Link Command)",
                cmd_type="10 (LRTY)",
                sub_type="0000 (Reserved)",
                description="Link Retry (LRTY)"
            )
        
        # Type 11: LBAD
        elif b8_7 == "11":
            return LinkCommand(
                raw_value=hex_val,
                bit_string=bits,
                cmd_class="00 (Link Command)",
                cmd_type="11 (LBAD)",
                sub_type="0000 (Reserved)",
                description="Link Bad (LBAD)"
            )
        
        return LinkCommand(
            raw_value=hex_val,
            bit_string=bits,
            cmd_class="00 (Link Command)",
            cmd_type="Unknown",
            sub_type="",
            description="Unknown command"
        )
    
    def decode_lgo_lau_lxu_lpma(self, bits: str, hex_val: str) -> LinkCommand:
        """Decode LGO_Ux, LAU, LXU, LPMA commands"""
        b8_7 = bits[3:5]  # Type bits
        b3_0 = bits[7:11]  # Sub-type bits
        
        # Type 00: LGO_Ux
        if b8_7 == "00":
            b3_0_val = int(b3_0, 2)
            lgo_map = {
                1: "LGO_U1",
                2: "LGO_U2",
                3: "LGO_U3"
            }
            lgo_type = lgo_map.get(b3_0_val, "Reserved")
            return LinkCommand(
                raw_value=hex_val,
                bit_string=bits,
                cmd_class="01 (Link Command)",
                cmd_type="00 (LGO_Ux)",
                sub_type=b3_0,
                description=f"Link Go to U state: {lgo_type}"
            )
        
        # Type 01: LAU
        elif b8_7 == "01":
            return LinkCommand(
                raw_value=hex_val,
                bit_string=bits,
                cmd_class="01 (Link Command)",
                cmd_type="01 (LAU)",
                sub_type="0000 (Reserved)",
                description="Link Accept U (LAU)"
            )
        
        # Type 10: LXU
        elif b8_7 == "10":
            return LinkCommand(
                raw_value=hex_val,
                bit_string=bits,
                cmd_class="01 (Link Command)",
                cmd_type="10 (LXU)",
                sub_type="0000 (Reserved)",
                description="Link Reject U (LXU)"
            )
        
        # Type 11: LPMA
        elif b8_7 == "11":
            return LinkCommand(
                raw_value=hex_val,
                bit_string=bits,
                cmd_class="01 (Link Command)",
                cmd_type="11 (LPMA)",
                sub_type="0000 (Reserved)",
                description="Link Port Capability Mismatch (LPMA)"
            )
        
        return LinkCommand(
            raw_value=hex_val,
            bit_string=bits,
            cmd_class="01 (Link Command)",
            cmd_type="Unknown",
            sub_type="",
            description="Unknown command"
        )
    
    def decode_ldn_lup(self, bits: str, hex_val: str) -> LinkCommand:
        """Decode LDN, LUP commands"""
        b8_7 = bits[3:5]  # Type bits
        
        # Type 00: LUP
        if b8_7 == "00":
            return LinkCommand(
                raw_value=hex_val,
                bit_string=bits,
                cmd_class="10 (Link Command)",
                cmd_type="00 (LUP)",
                sub_type="0000 (Reserved)",
                description="Link U Port Capability (LUP)"
            )
        
        # Type 11: LDN
        elif b8_7 == "11":
            return LinkCommand(
                raw_value=hex_val,
                bit_string=bits,
                cmd_class="10 (Link Command)",
                cmd_type="11 (LDN)",
                sub_type="0000 (Reserved)",
                description="Link Down (LDN)"
            )
        
        # Others: Reserved
        else:
            return LinkCommand(
                raw_value=hex_val,
                bit_string=bits,
                cmd_class="10 (Link Command)",
                cmd_type=f"{b8_7} (Reserved)",
                sub_type="0000 (Reserved)",
                description="Reserved"
            )
    
    def decode_link_command(self, value: str) -> LinkCommand:
        """Decode a link command from hex value"""
        # Convert to binary
        bits = self.hex_to_binary(value)
        
        # Extract class bits (b10-9)
        b10_9 = bits[1:3]
        
        # Decode based on class
        if b10_9 == "00":
            return self.decode_lgood_lcrd(bits, value)
        elif b10_9 == "01":
            return self.decode_lgo_lau_lxu_lpma(bits, value)
        elif b10_9 == "10":
            return self.decode_ldn_lup(bits, value)
        elif b10_9 == "11":
            return LinkCommand(
                raw_value=value,
                bit_string=bits,
                cmd_class="11 (Reserved)",
                cmd_type="Reserved",
                sub_type="Reserved",
                description="Reserved class"
            )
        
        return LinkCommand(
            raw_value=value,
            bit_string=bits,
            cmd_class="Unknown",
            cmd_type="Unknown",
            sub_type="Unknown",
            description="Unable to decode"
        )
    
    def parse_csv(self, filename: str) -> List[LinkCommand]:
        """Parse link commands from CSV file"""
        self.commands = []
        
        try:
            with open(filename, 'r', encoding='utf-8') as csvfile:
                reader = csv.reader(csvfile)
                
                for row_num, row in enumerate(reader, 1):
                    # Skip empty rows
                    if not row or all(not cell.strip() for cell in row):
                        continue
                    
                    # Skip header rows
                    first_cell = row[0].strip().upper()
                    if any(keyword in first_cell for keyword in ['COMMAND', 'VALUE', 'HEX', 'LINK']):
                        continue
                    
                    # Extract hex value from row
                    hex_value = None
                    for cell in row:
                        cell = cell.strip()
                        # Look for hex values (with or without 'h' suffix, '0x' prefix)
                        if cell and (cell.endswith('h') or cell.startswith('0x') or 
                                   all(c in '0123456789ABCDEFabcdef' for c in cell)):
                            hex_value = cell
                            break
                    
                    if hex_value:
                        cmd = self.decode_link_command(hex_value)
                        self.commands.append(cmd)
        
        except FileNotFoundError:
            print(f"Error: File '{filename}' not found")
            sys.exit(1)
        except Exception as e:
            print(f"Error parsing file: {e}")
            import traceback
            traceback.print_exc()
            sys.exit(1)
        
        return self.commands
    
    def print_summary(self):
        """Print a summary of parsed commands"""
        print(f"\n{'='*80}")
        print(f"USB Link Command Parser - Summary")
        print(f"{'='*80}")
        print(f"Total commands parsed: {len(self.commands)}")
        
        # Count by type
        type_counts = {}
        for cmd in self.commands:
            cmd_type = cmd.cmd_type.split('(')[0].strip()
            type_counts[cmd_type] = type_counts.get(cmd_type, 0) + 1
        
        print("\nCommand Type Distribution:")
        for cmd_type, count in sorted(type_counts.items()):
            print(f"  {cmd_type}: {count}")
        
        print(f"{'='*80}\n")
    
    def export_report(self, output_filename: str):
        """Export parsed data to a text report"""
        with open(output_filename, 'w', encoding='utf-8') as f:
            f.write("USB Link Command Parser Report\n")
            f.write("="*80 + "\n\n")
            
            for i, cmd in enumerate(self.commands, 1):
                f.write(f"Command #{i}\n")
                f.write("-" * 80 + "\n")
                f.write(str(cmd) + "\n")
                f.write("\n")
            
            f.write("\n" + "="*80 + "\n")
            f.write(f"Total commands: {len(self.commands)}\n")
        
        print(f"Report exported to: {output_filename}")


def main():
    """Main entry point"""
    if len(sys.argv) < 2:
        print("Usage: python usb_link_cmd_parser.py <csv_file> [output_report.txt]")
        print("\nSupported Link Commands:")
        print("  Class 00: LGOOD_n, LRTY, LBAD, LCRD_x, LCRD1_x, LCRD2_x")
        print("  Class 01: LGO_Ux, LAU, LXU, LPMA")
        print("  Class 10: LDN, LUP")
        print("\nExpected CSV format:")
        print("  Each row should contain a hex value (e.g., '045h', '0x045', '045')")
        print("\nExample CSV:")
        print("  Command")
        print("  045h")
        print("  046h")
        print("  200h")
        print("  401h")
        sys.exit(1)
    
    input_file = sys.argv[1]
    output_file = sys.argv[2] if len(sys.argv) > 2 else None
    
    # Create parser and parse file
    parser = USBLinkCommandParser()
    commands = parser.parse_csv(input_file)
    
    if not commands:
        print("No valid link commands found in file")
        sys.exit(1)
    
    # Print summary
    parser.print_summary()
    
    # Print all commands
    for i, cmd in enumerate(commands, 1):
        print(f"\nCommand #{i}")
        print("-" * 80)
        print(cmd)
    
    # Export report if requested
    if output_file:
        parser.export_report(output_file)


if __name__ == "__main__":
    main()
