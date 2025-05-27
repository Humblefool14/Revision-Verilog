#!/usr/bin/env python3
"""
PCIe EIEOS and EIOS Packet Parser

This module provides parsing capabilities for PCIe Electrical Idle Exit Ordered Set (EIEOS)
and Electrical Idle Ordered Set (EIOS) packets, regardless of current link state and speed.

EIEOS: Used to exit electrical idle state and prepare for data transmission
EIOS: Used to enter electrical idle state when no data needs to be transmitted

Both are critical for PCIe link power management and speed transitions.
"""

import struct
import binascii
from enum import Enum
from dataclasses import dataclass
from typing import List, Optional, Tuple, Union
import logging

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

class PCIeGen(Enum):
    """PCIe Generation enumeration"""
    GEN1 = 1  # 2.5 GT/s
    GEN2 = 2  # 5.0 GT/s  
    GEN3 = 3  # 8.0 GT/s
    GEN4 = 4  # 16.0 GT/s
    GEN5 = 5  # 32.0 GT/s
    GEN6 = 6  # 64.0 GT/s

class OrderedSetType(Enum):
    """Ordered Set Type enumeration"""
    EIEOS = "EIEOS"
    EIOS = "EIOS"
    UNKNOWN = "UNKNOWN"

@dataclass
class OrderedSetHeader:
    """Represents the header of a PCIe Ordered Set"""
    symbol_0: int  # K28.5 for most ordered sets
    symbol_1: int  # Identifies the specific ordered set type
    symbol_2: int  # Additional identifier or data
    symbol_3: int  # Additional identifier or data

@dataclass
class ParsedOrderedSet:
    """Represents a parsed PCIe Ordered Set"""
    type: OrderedSetType
    header: OrderedSetHeader
    data_symbols: List[int]
    raw_data: bytes
    generation: Optional[PCIeGen] = None
    lane_number: Optional[int] = None
    timestamp: Optional[float] = None

class PCIeOrderedSetParser:
    """Parser for PCIe EIEOS and EIOS packets"""
    
    # Standard K-codes (comma symbols) used in PCIe
    K28_5 = 0xBC  # Standard comma symbol
    K28_0 = 0x1C  # Alternative comma
    K28_1 = 0x3C  # Alternative comma
    K28_2 = 0x5C  # Alternative comma
    K28_3 = 0x7C  # Alternative comma
    K28_4 = 0x9C  # Alternative comma
    K28_6 = 0xDC  # Alternative comma
    K28_7 = 0xFC  # Alternative comma
    
    # EIEOS identifiers (second symbol after K28.5)
    EIEOS_IDENTIFIERS = {
        0x00: "EIEOS_Gen1_2",    # Gen 1/2 EIEOS
        0xFF: "EIEOS_Gen3_Plus", # Gen 3+ EIEOS
        0x55: "EIEOS_Custom",    # Custom EIEOS pattern
    }
    
    # EIOS identifiers
    EIOS_IDENTIFIERS = {
        0x00: "EIOS_Standard",   # Standard EIOS
        0xFF: "EIOS_Enhanced",   # Enhanced EIOS
    }
    
    def __init__(self):
        self.parsed_packets = []
        
    def _detect_ordered_set_type(self, header: OrderedSetHeader) -> OrderedSetType:
        """Detect the type of ordered set based on header pattern"""
        
        # Check for EIEOS patterns
        if header.symbol_0 == self.K28_5:
            if header.symbol_1 in self.EIEOS_IDENTIFIERS:
                return OrderedSetType.EIEOS
            elif header.symbol_1 in self.EIOS_IDENTIFIERS:
                return OrderedSetType.EIOS
            elif header.symbol_1 == 0x00 and header.symbol_2 == 0x00:
                return OrderedSetType.EIOS
                
        # Pattern matching for common EIEOS sequences
        eieos_patterns = [
            (0xBC, 0x00, 0x00, 0x00),  # Standard EIEOS
            (0xBC, 0xFF, 0xFF, 0xFF),  # Gen3+ EIEOS
            (0xBC, 0x55, 0xAA, 0x55),  # Training EIEOS
        ]
        
        header_tuple = (header.symbol_0, header.symbol_1, header.symbol_2, header.symbol_3)
        if header_tuple in eieos_patterns:
            return OrderedSetType.EIEOS
            
        # Pattern matching for EIOS
        eios_patterns = [
            (0xBC, 0x00, 0x00, 0x00),  # Standard EIOS (same as some EIEOS)
            (0xBC, 0xFF, 0x00, 0x00),  # Enhanced EIOS
        ]
        
        # Additional context-based detection would be needed for disambiguation
        return OrderedSetType.UNKNOWN
    
    def _extract_generation_info(self, ordered_set: ParsedOrderedSet) -> Optional[PCIeGen]:
        """Extract PCIe generation information from ordered set"""
        
        if ordered_set.type == OrderedSetType.EIEOS:
            # Gen 3+ typically uses different patterns
            if ordered_set.header.symbol_1 == 0xFF:
                return PCIeGen.GEN3  # Could be 3, 4, 5, or 6
            elif ordered_set.header.symbol_1 == 0x00:
                return PCIeGen.GEN1  # Could be Gen 1 or 2
                
        return None
    
    def parse_raw_data(self, data: bytes, lane_number: Optional[int] = None) -> List[ParsedOrderedSet]:
        """Parse raw binary data for EIEOS and EIOS packets"""
        
        parsed_sets = []
        offset = 0
        
        while offset + 4 <= len(data):
            # Extract potential header (4 symbols)
            try:
                symbols = struct.unpack('BBBB', data[offset:offset+4])
                header = OrderedSetHeader(*symbols)
                
                # Detect ordered set type
                os_type = self._detect_ordered_set_type(header)
                
                if os_type != OrderedSetType.UNKNOWN:
                    # Extract additional data symbols if available
                    data_symbols = []
                    data_offset = offset + 4
                    
                    # EIEOS typically has additional data symbols
                    if os_type == OrderedSetType.EIEOS and data_offset + 12 <= len(data):
                        additional_data = struct.unpack('BBBBBBBBBBBB', 
                                                      data[data_offset:data_offset+12])
                        data_symbols = list(additional_data)
                        packet_size = 16
                    else:
                        packet_size = 4
                    
                    # Create parsed ordered set
                    parsed_set = ParsedOrderedSet(
                        type=os_type,
                        header=header,
                        data_symbols=data_symbols,
                        raw_data=data[offset:offset+packet_size],
                        lane_number=lane_number
                    )
                    
                    # Extract generation info
                    parsed_set.generation = self._extract_generation_info(parsed_set)
                    
                    parsed_sets.append(parsed_set)
                    self.parsed_packets.append(parsed_set)
                    
                    offset += packet_size
                else:
                    offset += 1
                    
            except struct.error:
                break
                
        return parsed_sets
    
    def parse_hex_string(self, hex_string: str, lane_number: Optional[int] = None) -> List[ParsedOrderedSet]:
        """Parse hexadecimal string representation of PCIe data"""
        
        # Remove spaces and convert to bytes
        hex_clean = hex_string.replace(' ', '').replace('\n', '')
        try:
            data = binascii.unhexlify(hex_clean)
            return self.parse_raw_data(data, lane_number)
        except ValueError as e:
            logger.error(f"Invalid hex string: {e}")
            return []
    
    def parse_symbol_list(self, symbols: List[int], lane_number: Optional[int] = None) -> List[ParsedOrderedSet]:
        """Parse a list of symbol values"""
        
        data = bytes(symbols)
        return self.parse_raw_data(data, lane_number)
    
    def get_statistics(self) -> dict:
        """Get parsing statistics"""
        
        stats = {
            'total_packets': len(self.parsed_packets),
            'eieos_count': len([p for p in self.parsed_packets if p.type == OrderedSetType.EIEOS]),
            'eios_count': len([p for p in self.parsed_packets if p.type == OrderedSetType.EIOS]),
            'unknown_count': len([p for p in self.parsed_packets if p.type == OrderedSetType.UNKNOWN]),
            'generations': {}
        }
        
        for packet in self.parsed_packets:
            if packet.generation:
                gen_name = packet.generation.name
                stats['generations'][gen_name] = stats['generations'].get(gen_name, 0) + 1
                
        return stats
    
    def format_ordered_set(self, ordered_set: ParsedOrderedSet) -> str:
        """Format an ordered set for display"""
        
        lines = []
        lines.append(f"Type: {ordered_set.type.value}")
        lines.append(f"Header: {ordered_set.header.symbol_0:02X} {ordered_set.header.symbol_1:02X} "
                    f"{ordered_set.header.symbol_2:02X} {ordered_set.header.symbol_3:02X}")
        
        if ordered_set.data_symbols:
            data_hex = ' '.join(f"{sym:02X}" for sym in ordered_set.data_symbols)
            lines.append(f"Data: {data_hex}")
            
        if ordered_set.generation:
            lines.append(f"Generation: {ordered_set.generation.value}")
            
        if ordered_set.lane_number is not None:
            lines.append(f"Lane: {ordered_set.lane_number}")
            
        lines.append(f"Raw: {ordered_set.raw_data.hex().upper()}")
        
        return '\n'.join(lines)

# Example usage and test cases
def main():
    """Example usage of the PCIe Ordered Set Parser"""
    
    parser = PCIeOrderedSetParser()
    
    # Example 1: Parse EIEOS packet (Gen 1/2 style)
    print("=== Example 1: EIEOS Packet (Gen 1/2) ===")
    eieos_hex = "BC 00 00 00 55 AA 55 AA FF 00 FF 00 CC 33 CC 33"
    eieos_packets = parser.parse_hex_string(eieos_hex, lane_number=0)
    
    for packet in eieos_packets:
        print(parser.format_ordered_set(packet))
        print()
    
    # Example 2: Parse EIOS packet
    print("=== Example 2: EIOS Packet ===")
    eios_hex = "BC 00 00 00"
    eios_packets = parser.parse_hex_string(eios_hex, lane_number=1)
    
    for packet in eios_packets:
        print(parser.format_ordered_set(packet))
        print()
    
    # Example 3: Parse Gen 3+ EIEOS
    print("=== Example 3: Gen 3+ EIEOS ===")
    gen3_eieos_hex = "BC FF FF FF AA 55 AA 55 F0 0F F0 0F C3 3C C3 3C"
    gen3_packets = parser.parse_hex_string(gen3_eieos_hex, lane_number=2)
    
    for packet in gen3_packets:
        print(parser.format_ordered_set(packet))
        print()
    
    # Example 4: Parse multiple packets in sequence
    print("=== Example 4: Multiple Packets ===")
    multi_hex = "BC 00 00 00 BC FF FF FF AA 55 AA 55 F0 0F F0 0F BC 00 00 00"
    multi_packets = parser.parse_hex_string(multi_hex, lane_number=3)
    
    for i, packet in enumerate(multi_packets):
        print(f"Packet {i+1}:")
        print(parser.format_ordered_set(packet))
        print()
    
    # Display statistics
    print("=== Parsing Statistics ===")
    stats = parser.get_statistics()
    for key, value in stats.items():
        print(f"{key}: {value}")

if __name__ == "__main__":
    main()