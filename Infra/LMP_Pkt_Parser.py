#!/usr/bin/env python3
"""
LDM LMP Packet Parser
Parses Link Data Management (LDM) Link Management Protocol (LMP) packets
based on Table 8-11 specification.
"""

from dataclasses import dataclass
from enum import Enum
from typing import Optional


class LDMType(Enum):
    """LDM Type field values"""
    TS_REQUEST = 0
    TS_RESPONSE = 1
    RESERVED_2 = 2
    RESERVED_3 = 3


@dataclass
class LDMLMPPacket:
    """Represents a parsed LDM LMP packet"""
    subtype: int  # 4 bits at DW0:5
    ldm_type: LDMType  # 3 bits at DW0:9
    ldm_sequence_number: int  # 2 bits at DW0:12
    response_delay: int  # 14 bits at DW1:0
    raw_data: bytes
    
    def __str__(self):
        return (
            f"LDM LMP Packet:\n"
            f"  SubType: 0x{self.subtype:X} (Precision Time Measurement)\n"
            f"  LDM Type: {self.ldm_type.name} (0x{self.ldm_type.value:X})\n"
            f"  LDM Sequence Number: {self.ldm_sequence_number}\n"
            f"  Response Delay: {self.response_delay} (tlsochTimestampGranularity units)\n"
        )


class LDMLMPParser:
    """Parser for LDM LMP packets"""
    
    @staticmethod
    def extract_bits(data: int, offset: int, width: int) -> int:
        """
        Extract bits from data.
        
        Args:
            data: The data word to extract from
            offset: Bit offset (LSB = 0)
            width: Number of bits to extract
            
        Returns:
            Extracted value
        """
        mask = (1 << width) - 1
        return (data >> offset) & mask
    
    @staticmethod
    def parse(data: bytes) -> Optional[LDMLMPPacket]:
        """
        Parse LDM LMP packet from raw bytes.
        
        Args:
            data: Raw packet data (minimum 4 bytes)
            
        Returns:
            Parsed LDMLMPPacket or None if data is invalid
        """
        if len(data) < 4:
            print(f"Error: Packet too short. Need at least 4 bytes, got {len(data)}")
            return None
        
        # Parse as little-endian DWORDs
        dw0 = int.from_bytes(data[0:4], byteorder='little')
        
        # Extract fields from DW0
        subtype = LDMLMPParser.extract_bits(dw0, 5, 4)
        ldm_type_val = LDMLMPParser.extract_bits(dw0, 9, 3)
        ldm_seq_num = LDMLMPParser.extract_bits(dw0, 12, 2)
        
        # Validate and convert LDM Type
        try:
            ldm_type = LDMType(ldm_type_val)
        except ValueError:
            ldm_type = LDMType.RESERVED_2  # Default for invalid values
        
        # Extract Response Delay from DW1 if available
        response_delay = 0
        if len(data) >= 8:
            dw1 = int.from_bytes(data[4:8], byteorder='little')
            response_delay = LDMLMPParser.extract_bits(dw1, 0, 14)
        
        return LDMLMPPacket(
            subtype=subtype,
            ldm_type=ldm_type,
            ldm_sequence_number=ldm_seq_num,
            response_delay=response_delay,
            raw_data=data
        )
    
    @staticmethod
    def create_request(sequence_number: int) -> bytes:
        """
        Create a LDM Request LMP packet.
        
        Args:
            sequence_number: Sequence number (0-3)
            
        Returns:
            Raw packet bytes
        """
        # SubType = 0 (Precision Time Measurement assumed)
        # LDM Type = 0 (TS Request)
        # LDM Sequence Number = provided value
        dw0 = 0
        dw0 |= (0 & 0xF) << 5  # SubType at bit 5
        dw0 |= (0 & 0x7) << 9  # LDM Type at bit 9
        dw0 |= (sequence_number & 0x3) << 12  # LDMS at bit 12
        
        return dw0.to_bytes(4, byteorder='little')
    
    @staticmethod
    def create_response(sequence_number: int, response_delay: int) -> bytes:
        """
        Create a LDM Response LMP packet.
        
        Args:
            sequence_number: Sequence number (0-3)
            response_delay: Response delay in tlsochTimestampGranularity units
            
        Returns:
            Raw packet bytes
        """
        # DW0: SubType, LDM Type, Sequence Number
        dw0 = 0
        dw0 |= (0 & 0xF) << 5  # SubType at bit 5
        dw0 |= (1 & 0x7) << 9  # LDM Type = 1 (TS Response) at bit 9
        dw0 |= (sequence_number & 0x3) << 12  # LDMS at bit 12
        
        # DW1: Response Delay
        dw1 = (response_delay & 0x3FFF)  # 14 bits at bit 0
        
        packet = dw0.to_bytes(4, byteorder='little')
        packet += dw1.to_bytes(4, byteorder='little')
        
        return packet


def main():
    """Example usage of the LDM LMP parser"""
    
    print("=== LDM LMP Packet Parser Demo ===\n")
    
    # Example 1: Create and parse a Request packet
    print("Example 1: LDM Request Packet")
    print("-" * 40)
    request_packet = LDMLMPParser.create_request(sequence_number=2)
    print(f"Raw bytes: {request_packet.hex()}")
    parsed_request = LDMLMPParser.parse(request_packet)
    if parsed_request:
        print(parsed_request)
    
    # Example 2: Create and parse a Response packet
    print("\nExample 2: LDM Response Packet")
    print("-" * 40)
    response_packet = LDMLMPParser.create_response(
        sequence_number=2,
        response_delay=1234
    )
    print(f"Raw bytes: {response_packet.hex()}")
    parsed_response = LDMLMPParser.parse(response_packet)
    if parsed_response:
        print(parsed_response)
    
    # Example 3: Parse custom packet
    print("\nExample 3: Parse Custom Packet")
    print("-" * 40)
    # Custom packet: SubType=0, LDMType=1, SeqNum=3, ResponseDelay=5000
    custom_data = bytes([0x20, 0x3E, 0x00, 0x00, 0x88, 0x13, 0x00, 0x00])
    print(f"Raw bytes: {custom_data.hex()}")
    parsed_custom = LDMLMPParser.parse(custom_data)
    if parsed_custom:
        print(parsed_custom)


if __name__ == "__main__":
    main()
