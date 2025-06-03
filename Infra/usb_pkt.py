#!/usr/bin/env python3
"""
USB Data Packet Header (DPH) Parser
Parses 4-word DPH headers according to the USB specification
"""

import struct
from typing import Dict, Any, List
from dataclasses import dataclass

@dataclass
class DPHFields:
    """Data structure to hold parsed DPH fields"""
    # DW0 fields
    device_address: int
    route_string: int
    packet_type: int
    
    # DW1 fields
    data_length: int
    setup_flag: bool
    reserved_dw1: int
    endpoint_num: int
    direction: bool
    reserved_pktpend: int
    reserved_r: int
    sequence_num: int
    
    # DW2 fields
    reserved_dw2_upper: int
    pp: int
    reserved_dw2_middle: int
    stream_id: int
    
    # DW3 fields
    crc5: int
    data_flag: bool
    data_length_flag: bool
    hub_depth: int
    reserved_dw3: int
    header_seq_num: int
    crc16: int

class USBPacketParser:
    """USB DPH packet parser"""
    
    # Packet type mappings
    PACKET_TYPES = {
        0x0: "Transaction Packet",
        0x1: "Data Packet", 
        0x2: "Handshake Packet",
        0x3: "Token Packet",
        0x4: "Special Packet",
        0x5: "Isochronous Packet",
        0x6: "Link Management Packet",
        0x7: "Reserved"
    }
    
    def __init__(self):
        pass
    
    def parse_packet(self, packet_data: bytes) -> DPHFields:
        """
        Parse a 16-byte DPH packet
        
        Args:
            packet_data: 16 bytes representing the DPH header
            
        Returns:
            DPHFields object with parsed fields
        """
        if len(packet_data) != 16:
            raise ValueError(f"DPH packet must be exactly 16 bytes, got {len(packet_data)}")
        
        # Unpack as 4 32-bit words (little-endian)
        dw0, dw1, dw2, dw3 = struct.unpack('<4I', packet_data)
        
        # Parse DW0 (bits 31-0)
        device_address = (dw0 >> 25) & 0x7F      # bits 31-25
        route_string = (dw0 >> 5) & 0xFFFFF      # bits 24-5
        packet_type = dw0 & 0x1F                 # bits 4-0
        
        # Parse DW1 (bits 31-0)
        data_length = (dw1 >> 16) & 0xFFFF       # bits 31-16
        setup_flag = bool((dw1 >> 15) & 0x1)     # bit 15
        reserved_dw1 = (dw1 >> 12) & 0x7         # bits 14-12
        endpoint_num = (dw1 >> 8) & 0xF          # bits 11-8
        direction = bool((dw1 >> 7) & 0x1)       # bit 7
        reserved_pktpend = (dw1 >> 6) & 0x1      # bit 6
        reserved_r = (dw1 >> 4) & 0x3            # bits 5-4
        sequence_num = dw1 & 0xF                 # bits 3-0
        
        # Parse DW2 (bits 31-0)
        reserved_dw2_upper = (dw2 >> 28) & 0xF   # bits 31-28
        pp = (dw2 >> 26) & 0x3                   # bits 27-26
        reserved_dw2_middle = (dw2 >> 16) & 0x3FF # bits 25-16
        stream_id = dw2 & 0xFFFF                 # bits 15-0
        
        # Parse DW3 (bits 31-0)
        crc5 = (dw3 >> 27) & 0x1F                # bits 31-27
        data_flag = bool((dw3 >> 26) & 0x1)      # bit 26
        data_length_flag = bool((dw3 >> 25) & 0x1) # bit 25
        hub_depth = (dw3 >> 22) & 0x7            # bits 24-22
        reserved_dw3 = (dw3 >> 19) & 0x7         # bits 21-19
        header_seq_num = (dw3 >> 16) & 0x7       # bits 18-16
        crc16 = dw3 & 0xFFFF                     # bits 15-0
        
        return DPHFields(
            device_address=device_address,
            route_string=route_string,
            packet_type=packet_type,
            data_length=data_length,
            setup_flag=setup_flag,
            reserved_dw1=reserved_dw1,
            endpoint_num=endpoint_num,
            direction=direction,
            reserved_pktpend=reserved_pktpend,
            reserved_r=reserved_r,
            sequence_num=sequence_num,
            reserved_dw2_upper=reserved_dw2_upper,
            pp=pp,
            reserved_dw2_middle=reserved_dw2_middle,
            stream_id=stream_id,
            crc5=crc5,
            data_flag=data_flag,
            data_length_flag=data_length_flag,
            hub_depth=hub_depth,
            reserved_dw3=reserved_dw3,
            header_seq_num=header_seq_num,
            crc16=crc16
        )
    
    def format_output(self, fields: DPHFields) -> str:
        """
        Format parsed fields into a readable string
        
        Args:
            fields: Parsed DPH fields
            
        Returns:
            Formatted string representation
        """
        output = []
        output.append("=" * 60)
        output.append("USB Data Packet Header (DPH) Analysis")
        output.append("=" * 60)
        
        # DW0 Analysis
        output.append("\nDW0 (Device and Routing Info):")
        output.append(f"  Device Address:     0x{fields.device_address:02X} ({fields.device_address})")
        output.append(f"  Route String:       0x{fields.route_string:05X}")
        output.append(f"  Packet Type:        0x{fields.packet_type:02X} ({self.PACKET_TYPES.get(fields.packet_type, 'Unknown')})")
        
        # DW1 Analysis
        output.append("\nDW1 (Data and Endpoint Info):")
        output.append(f"  Data Length:        {fields.data_length} bytes")
        output.append(f"  Setup Flag:         {'Yes' if fields.setup_flag else 'No'}")
        output.append(f"  Endpoint Number:    {fields.endpoint_num}")
        output.append(f"  Direction:          {'IN' if fields.direction else 'OUT'}")
        output.append(f"  Sequence Number:    {fields.sequence_num}")
        
        # DW2 Analysis
        output.append("\nDW2 (Stream and Protocol Info):")
        output.append(f"  PP (Packet Pending): {fields.pp}")
        output.append(f"  Stream ID:          0x{fields.stream_id:04X}")
        
        # DW3 Analysis
        output.append("\nDW3 (Link Control Word):")
        output.append(f"  CRC-5:              0x{fields.crc5:02X}")
        output.append(f"  DF (Data Flag):     {'Yes' if fields.data_flag else 'No'}")
        output.append(f"  DL (Data Length):   {'Yes' if fields.data_length_flag else 'No'}")
        output.append(f"  Hub Depth:          {fields.hub_depth}")
        output.append(f"  Header Seq #:       {fields.header_seq_num}")
        output.append(f"  CRC-16:             0x{fields.crc16:04X}")
        
        # Field Explanations
        output.append("\n" + "=" * 60)
        output.append("Field Explanations:")
        output.append("=" * 60)
        output.append("Device Address:   USB device address (0-127)")
        output.append("Route String:     Hub routing information for multi-tier hubs")
        output.append("Packet Type:      Type of USB packet being transmitted")
        output.append("Data Length:      Number of data bytes in packet payload")
        output.append("Setup Flag:       Indicates if this is a SETUP transaction")
        output.append("Endpoint Number:  Target endpoint on the device (0-15)")
        output.append("Direction:        Data direction (IN=device->host, OUT=host->device)")
        output.append("Sequence Number:  Packet sequence for flow control")
        output.append("PP:               Packet pending indicator")
        output.append("Stream ID:        Stream identifier for bulk endpoints")
        output.append("Hub Depth:        Depth in hub topology")
        output.append("Header Seq #:     Header sequence number")
        output.append("CRC-5/CRC-16:     Error detection checksums")
        
        return "\n".join(output)

def main():
    """Example usage with sample packet data"""
    parser = USBPacketParser()
    
    # Sample DPH packet (16 bytes)
    # This is a constructed example - replace with actual packet data
    sample_packet = bytes([
        # DW0: Device Addr=0x05, Route String=0x12345, Type=0x01 (Data Packet)
        0x41, 0x8D, 0x4A, 0x02,  # Little-endian: 0x024A8D41
        
        # DW1: Data Length=64, Setup=0, Endpoint=2, Direction=IN, Seq=3
        0x23, 0x02, 0x40, 0x00,  # Little-endian: 0x00400223
        
        # DW2: PP=1, Stream ID=0x1234
        0x34, 0x12, 0x00, 0x40,  # Little-endian: 0x40001234
        
        # DW3: CRC-5=0x1F, Hub Depth=2, Header Seq=5, CRC-16=0xABCD
        0xCD, 0xAB, 0x50, 0xFF   # Little-endian: 0xFF50ABCD
    ])
    
    print("Sample USB DPH Packet (16 bytes):")
    print(" ".join(f"{b:02X}" for b in sample_packet))
    print()
    
    try:
        # Parse the packet
        fields = parser.parse_packet(sample_packet)
        
        # Display formatted output
        print(parser.format_output(fields))
        
    except Exception as e:
        print(f"Error parsing packet: {e}")

if __name__ == "__main__":
    main()