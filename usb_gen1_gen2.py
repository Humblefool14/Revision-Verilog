#!/usr/bin/env python3
"""
USB Gen 1 and Gen 2 Ordered Set Parser
Parses USB Ordered Set packets from CSV files according to Gen 1 and Gen 2 specifications
Supports: TS1, TS2, TSEQ, SYNC, and SDS Ordered Sets
"""

import csv
import sys
from dataclasses import dataclass
from typing import List, Dict, Optional
from enum import Enum


class Generation(Enum):
    """USB Generation"""
    GEN1 = "Gen 1"
    GEN2 = "Gen 2"


class OSType(Enum):
    """Ordered Set Types"""
    TS1 = "TS1"
    TS2 = "TS2"
    TSEQ = "TSEQ"
    SYNC = "SYNC"
    SDS = "SDS"


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
    generation: Generation
    os_type: OSType
    symbols: List[Symbol]
    packet_number: int
    
    def __str__(self):
        header = f"\n{'='*80}\n{self.generation.value} {self.os_type.value} Ordered Set - Packet #{self.packet_number}\n{'='*80}"
        symbols_str = "\n".join(str(symbol) for symbol in self.symbols)
        return f"{header}\n{symbols_str}\n"


class USBOSParser:
    """Parser for USB Ordered Set packets"""
    
    def __init__(self, generation: Generation = Generation.GEN1):
        self.packets: List[OrderedSet] = []
        self.generation = generation
    
    @staticmethod
    def decode_link_configuration(value: str) -> LinkConfiguration:
        """Decode Symbol 5 - Link Configuration"""
        # Remove K or D prefix and convert hex to int
        clean_value = value.replace('K', '').replace('D', '').replace('.', '').replace('h', '').strip()
        try:
            # Parse as hex
            if any(c in clean_value.upper() for c in 'ABCDEF'):
                bin_value = int(clean_value, 16)
            else:
                bin_value = int(clean_value, 16) if clean_value else 0
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
    
    def decode_symbol_gen1(self, symbol_num: str, value: str, os_type: OSType) -> Symbol:
        """Decode a Gen 1 symbol based on its number and value"""
        # Parse symbol number range
        if '-' in symbol_num:
            start, end = map(int, symbol_num.split('-'))
            num = start
        else:
            num = int(symbol_num)
        
        # Gen 1 decoding
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
    
    def decode_symbol_gen2(self, symbol_num: str, value: str, os_type: OSType) -> Symbol:
        """Decode a Gen 2 symbol based on its number and value"""
        # Parse symbol number range or list
        if ',' in symbol_num:
            # Handle comma-separated lists like "0,2,4,6,8,10,12,14"
            nums = [int(n.strip()) for n in symbol_num.split(',')]
            num = nums[0]
        elif '-' in symbol_num:
            start, end = map(int, symbol_num.split('-'))
            num = start
        else:
            num = int(symbol_num)
        
        # TSEQ Ordered Set
        if os_type == OSType.TSEQ:
            if 0 <= num <= 3:
                return Symbol(
                    number=symbol_num,
                    raw_value=value,
                    field="TSEQ Identifier",
                    description="TSEQ Identifier (Expected: 87h)"
                )
            elif 4 <= num <= 5:
                return Symbol(
                    number=symbol_num,
                    raw_value=value,
                    field="Reserved",
                    description="Reserved for future use (00h)"
                )
            elif 6 <= num <= 13:
                return Symbol(
                    number=symbol_num,
                    raw_value=value,
                    field="TSEQ Identifier",
                    description="TSEQ Identifier (Expected: 87h)"
                )
            elif 14 <= num <= 15:
                return Symbol(
                    number=symbol_num,
                    raw_value=value,
                    field="TSEQ Identifier or DC Balance",
                    description="TSEQ Identifier (87h) or DC Balance Symbol"
                )
        
        # SYNC Ordered Set
        elif os_type == OSType.SYNC:
            if num in [0, 2, 4, 6, 8, 10, 12, 14]:
                return Symbol(
                    number=symbol_num,
                    raw_value=value,
                    field="Symbol 0 SYNC Identifier",
                    description="Symbol 0 SYNC identifier (Expected: 00h)"
                )
            else:  # num in [1, 3, 5, 7, 9, 11, 13, 15]
                return Symbol(
                    number=symbol_num,
                    raw_value=value,
                    field="Symbol 1 SYNC Identifier",
                    description="Symbol 1 SYNC identifier (Expected: FFh)"
                )
        
        # SDS Ordered Set
        elif os_type == OSType.SDS:
            if 0 <= num <= 3:
                return Symbol(
                    number=symbol_num,
                    raw_value=value,
                    field="SDS Identifier",
                    description="SDS Ordered Set Identifier (Expected: E1h)"
                )
            elif 4 <= num <= 15:
                return Symbol(
                    number=symbol_num,
                    raw_value=value,
                    field="SDS Body",
                    description="Body of SDS Ordered Set (Expected: 55h)"
                )
        
        # TS1/TS2 Ordered Sets
        else:
            if 0 <= num <= 3:
                identifier_type = "TS1 Identifier" if os_type == OSType.TS1 else "TS2 Identifier"
                expected_value = "1Eh" if os_type == OSType.TS1 else "2Dh"
                return Symbol(
                    number=symbol_num,
                    raw_value=value,
                    field=identifier_type,
                    description=f"{identifier_type} (Expected: {expected_value})"
                )
            elif num == 4:
                return Symbol(
                    number=symbol_num,
                    raw_value=value,
                    field="Reserved",
                    description="Reserved for future use (00h)"
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
            elif 6 <= num <= 13:
                identifier_type = "TS1 Identifier" if os_type == OSType.TS1 else "TS2 Identifier"
                expected_value = "1Eh" if os_type == OSType.TS1 else "2Dh"
                return Symbol(
                    number=symbol_num,
                    raw_value=value,
                    field=identifier_type,
                    description=f"{identifier_type} (Expected: {expected_value})"
                )
            elif 14 <= num <= 15:
                identifier_type = "TS1 Identifier" if os_type == OSType.TS1 else "TS2 Identifier"
                expected_value = "1Eh" if os_type == OSType.TS1 else "2Dh"
                return Symbol(
                    number=symbol_num,
                    raw_value=value,
                    field=f"{identifier_type} or DC Balance",
                    description=f"{identifier_type} ({expected_value}) or DC Balance Symbol"
                )
        
        return Symbol(
            number=symbol_num,
            raw_value=value,
            field="Unknown",
            description="Unknown symbol number"
        )
    
    def decode_symbol(self, symbol_num: str, value: str, os_type: OSType) -> Symbol:
        """Decode a symbol based on generation, number and value"""
        if self.generation == Generation.GEN1:
            return self.decode_symbol_gen1(symbol_num, value, os_type)
        else:
            return self.decode_symbol_gen2(symbol_num, value, os_type)
    
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
                    if any(keyword in first_cell for keyword in ['SYMBOL', 'TYPE', 'NUMBER', 'VALUE', 'GEN']):
                        # Check if this header specifies generation
                        row_text = ' '.join(row).upper()
                        if 'GEN2' in row_text or 'GEN 2' in row_text:
                            self.generation = Generation.GEN2
                        elif 'GEN1' in row_text or 'GEN 1' in row_text:
                            self.generation = Generation.GEN1
                        continue
                    
                    # Parse row based on format
                    os_type_str, symbol_num, value, gen_str = self._parse_row(row)
                    
                    # Update generation if specified in row
                    if gen_str:
                        if 'GEN2' in gen_str.upper() or 'GEN 2' in gen_str.upper():
                            self.generation = Generation.GEN2
                        elif 'GEN1' in gen_str.upper() or 'GEN 1' in gen_str.upper():
                            self.generation = Generation.GEN1
                    
                    if not symbol_num or not value:
                        continue
                    
                    # Determine OS type
                    try:
                        os_type_upper = os_type_str.upper()
                        if 'TSEQ' in os_type_upper:
                            os_type = OSType.TSEQ
                        elif 'SYNC' in os_type_upper:
                            os_type = OSType.SYNC
                        elif 'SDS' in os_type_upper:
                            os_type = OSType.SDS
                        elif 'TS2' in os_type_upper:
                            os_type = OSType.TS2
                        else:
                            os_type = OSType.TS1
                    except:
                        os_type = OSType.TS1
                    
                    # Start new packet on symbol 0 or type change
                    symbol_start = symbol_num.split(',')[0].split('-')[0]
                    if symbol_start == '0' or current_packet is None or current_packet.os_type != os_type:
                        if current_packet and current_packet.symbols:
                            self.packets.append(current_packet)
                        packet_count += 1
                        current_packet = OrderedSet(
                            generation=self.generation,
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
            import traceback
            traceback.print_exc()
            sys.exit(1)
        
        return self.packets
    
    def _parse_row(self, row: List[str]) -> tuple:
        """Parse a CSV row and extract OS type, symbol number, value, and generation"""
        row = [cell.strip() for cell in row]
        
        # Format 1: Gen, Type, Symbol#, Value
        if len(row) >= 4:
            return row[1], row[2], row[3], row[0]
        
        # Format 2: Type, Symbol#, Value, Gen
        elif len(row) >= 3:
            # Check if first or last column contains generation info
            if 'GEN' in row[0].upper():
                return row[1], row[2], row[3] if len(row) > 3 else '', row[0]
            elif len(row) > 3 and 'GEN' in row[3].upper():
                return row[0], row[1], row[2], row[3]
            # Check if it's Type, Symbol#, Value
            elif any(kw in row[0].upper() for kw in ['TS1', 'TS2', 'TSEQ', 'SYNC', 'SDS']) or row[0].isalpha():
                return row[0], row[1], row[2], ''
            # Or Symbol#, Value, Type
            else:
                return row[2], row[0], row[1], ''
        
        # Format 3: Symbol#, Value (default to TS1)
        elif len(row) >= 2:
            return 'TS1', row[0], row[1], ''
        
        return '', '', '', ''
    
    def print_summary(self):
        """Print a summary of parsed packets"""
        print(f"\n{'='*80}")
        print(f"USB Ordered Set Parser - Summary")
        print(f"{'='*80}")
        print(f"Total packets parsed: {len(self.packets)}")
        
        gen1_count = sum(1 for p in self.packets if p.generation == Generation.GEN1)
        gen2_count = sum(1 for p in self.packets if p.generation == Generation.GEN2)
        ts1_count = sum(1 for p in self.packets if p.os_type == OSType.TS1)
        ts2_count = sum(1 for p in self.packets if p.os_type == OSType.TS2)
        tseq_count = sum(1 for p in self.packets if p.os_type == OSType.TSEQ)
        sync_count = sum(1 for p in self.packets if p.os_type == OSType.SYNC)
        sds_count = sum(1 for p in self.packets if p.os_type == OSType.SDS)
        
        print(f"Gen 1 packets: {gen1_count}")
        print(f"Gen 2 packets: {gen2_count}")
        print(f"TS1 packets: {ts1_count}")
        print(f"TS2 packets: {ts2_count}")
        print(f"TSEQ packets: {tseq_count}")
        print(f"SYNC packets: {sync_count}")
        print(f"SDS packets: {sds_count}")
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
        print("Usage: python usb_os_parser.py <csv_file> [output_report.txt] [--gen1|--gen2]")
        print("\nSupported Ordered Sets:")
        print("  Gen 1: TS1, TS2")
        print("  Gen 2: TS1, TS2, TSEQ, SYNC, SDS")
        print("\nExpected CSV format:")
        print("  Format 1: Gen,Type,Symbol#,Value")
        print("  Format 2: Type,Symbol#,Value,Gen")
        print("  Format 3: Type,Symbol#,Value")
        print("  Format 4: Symbol#,Value,Type")
        print("  Format 5: Symbol#,Value (defaults to Gen1 TS1)")
        print("\nGen 2 TSEQ Example:")
        print("  Gen2,TSEQ,0-3,87h")
        print("  Gen2,TSEQ,4-5,00h")
        print("  Gen2,TSEQ,6-13,87h")
        print("  Gen2,TSEQ,14-15,87h")
        print("\nGen 2 SYNC Example:")
        print("  Gen2,SYNC,0,2,4,6,8,10,12,14,00h")
        print("  Gen2,SYNC,1,3,5,7,9,11,13,15,FFh")
        print("\nGen 2 SDS Example:")
        print("  Gen2,SDS,0-3,E1h")
        print("  Gen2,SDS,4-15,55h")
        sys.exit(1)
    
    input_file = sys.argv[1]
    output_file = None
    generation = Generation.GEN1
    
    # Parse command line arguments
    for arg in sys.argv[2:]:
        if arg == '--gen1':
            generation = Generation.GEN1
        elif arg == '--gen2':
            generation = Generation.GEN2
        elif not arg.startswith('--'):
            output_file = arg
    
    # Create parser and parse file
    parser = USBOSParser(generation)
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
