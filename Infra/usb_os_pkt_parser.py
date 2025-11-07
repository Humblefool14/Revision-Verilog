#!/usr/bin/env python3
"""
USB Gen 1 TS1/TS2 Ordered Set Parser
Parses USB Ordered Set packets from CSV files according to Gen 1 specifications
"""

import csv
import sys
from dataclasses import dataclass
from typing import List, Dict, Optional
from enum import Enum


class OSType(Enum):
    """Ordered Set Types"""
    TS1 = "TS1"
    TS2 = "TS2"


@dataclass
class LinkConfiguration:
    """Link Configuration decoded from Symbol 5"""
    bit0_reset: bool
    bit1_reserved: bool
    bit2_loopback: bool
    bit3_disable_scrambling: bool
    bit4_local_loopback_repeater: bool
    bit5_bit_level_retimer: bool
    bits67_reserved: int
    
    def __str__(self):
        return (
            f"  Bit 0 (Reset): {'Reset' if self.bit0_reset else 'Normal Training'}\n"
            f"  Bit 1: {'Reserved' if self.bit1_reserved else 'Set to 0'}\n"
            f"  Bit 2 (Loopback): {'Asserted' if self.bit2_loopback else 'De-asserted'}\n"
            f"  Bit 3 (Disable Scrambling): {'Asserted' if self.bit3_disable_scrambling else 'De-asserted'}\n"
            f"  Bit 4 (Local Loopback): {'Asserted' if self.bit4_local_loopback_repeater else 'De-asserted'}\n"
            f"  Bit 5 (Bit-level Re-timer): {'Asserted' if self.bit5_bit_level_retimer else 'De-asserted'}\n"
            f"  Bits 6-7: Reserved (Set to 0)"
        )


@dataclass
class Symbol:
    """Represents a single symbol in an Ordered Set"""
    number: str
    raw_value: str
    field: str
    description: str
    link_config: Optional[LinkConfiguration] = None
    
    def __str__(self):
        result = f"Symbol {self.number:6s} | {self.raw_value:10s} | {self.field:20s} | {self.description}"
        if self.link_config:
            result += f"\n{self.link_config}"
        return result


@dataclass
class OrderedSet:
    """Represents a complete Ordered Set packet"""
    os_type: OSType
    symbols: List[Symbol]
    packet_number: int
    
    def __str__(self):
        header = f"\n{'='*80}\n{self.os_type.value} Ordered Set - Packet #{self.packet_number}\n{'='*80}"
        symbols_str = "\n".join(str(symbol) for symbol in self.symbols)
        return f"{header}\n{symbols_str}\n"


class USBOSParser:
    """Parser for USB Ordered Set packets"""
    
    def __init__(self):
        self.packets: List[OrderedSet] = []
    
    @staticmethod
    def decode_link_configuration(value: str) -> LinkConfiguration:
        """Decode Symbol 5 - Link Configuration"""
        # Remove K or D prefix and convert hex to int
        clean_value = value.replace('K', '').replace('D', '').replace('.', '')
        try:
            # Parse as hex
            if any(c in clean_value.upper() for c in 'ABCDEF'):
                bin_value = int(clean_value, 16)
            else:
                bin_value = int(clean_value)
        except ValueError:
            bin_value = 0
        
        return LinkConfiguration(
            bit0_reset=bool(bin_value & 0x01),
            bit1_reserved=bool(bin_value & 0x02),
            bit2_loopback=bool(bin_value & 0x04),
            bit3_disable_scrambling=bool(bin_value & 0x08),
            bit4_local_loopback_repeater=bool(bin_value & 0x10),
            bit5_bit_level_retimer=bool(bin_value & 0x20),
            bits67_reserved=(bin_value >> 6) & 0x03
        )
    
    def decode_symbol(self, symbol_num: str, value: str, os_type: OSType) -> Symbol:
        """Decode a symbol based on its number and value"""
        # Parse symbol number range
        if '-' in symbol_num:
            start, end = map(int, symbol_num.split('-'))
            num = start
        else:
            num = int(symbol_num)
        
        # Decode based on symbol number
        if 0 <= num <= 3:
            return Symbol(
                number=symbol_num,
                raw_value=value,
                field="COM",
                description="Comma (K28.5)"
            )
        elif num == 4:
            return Symbol(
                number=symbol_num,
                raw_value=value,
                field="Reserved",
                description="Reserved for future use (D0.0)"
            )
        elif num == 5:
            link_config = self.decode_link_configuration(value)
            return Symbol(
                number=symbol_num,
                raw_value=value,
                field="Link Functionality",
                description="Link Configuration (See Table 6-6)",
                link_config=link_config
            )
        elif 6 <= num <= 15:
            identifier_type = "TS1 Identifier" if os_type == OSType.TS1 else "TS2 Identifier"
            expected_value = "D10.2" if os_type == OSType.TS1 else "D5.2"
            return Symbol(
                number=symbol_num,
                raw_value=value,
                field=identifier_type,
                description=f"{identifier_type} (Expected: {expected_value})"
            )
        else:
            return Symbol(
                number=symbol_num,
                raw_value=value,
                field="Unknown",
                description="Unknown symbol number"
            )
    
    def parse_csv(self, filename: str) -> List[OrderedSet]:
        """Parse USB OS packets from CSV file"""
        self.packets = []
        current_packet = None
        packet_count = 0
        
        try:
            with open(filename, 'r', encoding='utf-8') as csvfile:
                # Try to detect delimiter
                sample = csvfile.read(1024)
                csvfile.seek(0)
                
                # Use csv.Sniffer to detect format
                try:
                    dialect = csv.Sniffer().sniff(sample)
                    reader = csv.reader(csvfile, dialect)
                except csv.Error:
                    reader = csv.reader(csvfile)
                
                for row_num, row in enumerate(reader, 1):
                    # Skip empty rows
                    if not row or all(not cell.strip() for cell in row):
                        continue
                    
                    # Skip header rows
                    first_cell = row[0].strip().upper()
                    if any(keyword in first_cell for keyword in ['SYMBOL', 'TYPE', 'NUMBER', 'VALUE']):
                        continue
                    
                    # Parse row based on format
                    os_type_str, symbol_num, value = self._parse_row(row)
                    
                    if not symbol_num or not value:
                        continue
                    
                    # Determine OS type
                    try:
                        os_type = OSType.TS1 if 'TS1' in os_type_str.upper() else OSType.TS2
                    except:
                        os_type = OSType.TS1
                    
                    # Start new packet on symbol 0 or type change
                    if symbol_num.startswith('0') or current_packet is None or current_packet.os_type != os_type:
                        if current_packet and current_packet.symbols:
                            self.packets.append(current_packet)
                        packet_count += 1
                        current_packet = OrderedSet(
                            os_type=os_type,
                            symbols=[],
                            packet_number=packet_count
                        )
                    
                    # Decode and add symbol
                    symbol = self.decode_symbol(symbol_num, value, os_type)
                    current_packet.symbols.append(symbol)
                
                # Add final packet
                if current_packet and current_packet.symbols:
                    self.packets.append(current_packet)
        
        except FileNotFoundError:
            print(f"Error: File '{filename}' not found")
            sys.exit(1)
        except Exception as e:
            print(f"Error parsing file: {e}")
            sys.exit(1)
        
        return self.packets
    
    def _parse_row(self, row: List[str]) -> tuple:
        """Parse a CSV row and extract OS type, symbol number, and value"""
        row = [cell.strip() for cell in row]
        
        # Format 1: Type, Symbol#, Value
        if len(row) >= 3 and ('TS' in row[0].upper() or row[0].isalpha()):
            return row[0], row[1], row[2]
        
        # Format 2: Symbol#, Value, Type
        elif len(row) >= 3:
            return row[2], row[0], row[1]
        
        # Format 3: Symbol#, Value (default to TS1)
        elif len(row) >= 2:
            return 'TS1', row[0], row[1]
        
        return '', '', ''
    
    def print_summary(self):
        """Print a summary of parsed packets"""
        print(f"\n{'='*80}")
        print(f"USB Ordered Set Parser - Summary")
        print(f"{'='*80}")
        print(f"Total packets parsed: {len(self.packets)}")
        
        ts1_count = sum(1 for p in self.packets if p.os_type == OSType.TS1)
        ts2_count = sum(1 for p in self.packets if p.os_type == OSType.TS2)
        
        print(f"TS1 packets: {ts1_count}")
        print(f"TS2 packets: {ts2_count}")
        print(f"{'='*80}\n")
    
    def export_report(self, output_filename: str):
        """Export parsed data to a text report"""
        with open(output_filename, 'w', encoding='utf-8') as f:
            f.write("USB Ordered Set Parser Report\n")
            f.write("="*80 + "\n\n")
            
            for packet in self.packets:
                f.write(str(packet))
                f.write("\n")
            
            f.write("\n" + "="*80 + "\n")
            f.write(f"Total packets: {len(self.packets)}\n")
        
        print(f"Report exported to: {output_filename}")


def main():
    """Main entry point"""
    if len(sys.argv) < 2:
        print("Usage: python usb_os_parser.py <csv_file> [output_report.txt]")
        print("\nExpected CSV format:")
        print("  Format 1: Type,Symbol#,Value")
        print("  Format 2: Symbol#,Value,Type")
        print("  Format 3: Symbol#,Value (defaults to TS1)")
        print("\nExample:")
        print("  TS1,0-3,K28.5")
        print("  TS1,4,D0.0")
        print("  TS1,5,00")
        print("  TS1,6-15,D10.2")
        sys.exit(1)
    
    input_file = sys.argv[1]
    output_file = sys.argv[2] if len(sys.argv) > 2 else None
    
    # Create parser and parse file
    parser = USBOSParser()
    packets = parser.parse_csv(input_file)
    
    if not packets:
        print("No valid packets found in file")
        sys.exit(1)
    
    # Print summary
    parser.print_summary()
    
    # Print all packets
    for packet in packets:
        print(packet)
    
    # Export report if requested
    if output_file:
        parser.export_report(output_file)


if __name__ == "__main__":
    main()
