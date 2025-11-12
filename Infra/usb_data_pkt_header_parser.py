from dataclasses import dataclass
from typing import Optional, List
from enum import IntEnum
import struct


# ============================================================================
# Header Type Definitions
# ============================================================================

class HeaderType(IntEnum):
    """USB 3.x Header Packet Types"""
    # Data Packet Headers
    DPH = 0b0101  # Data Packet Header
    
    # Status Packet Headers  
    SPH = 0b0111  # Status Packet Header (ACK)
    
    # Transaction Packet Headers
    TPH = 0b0100  # Transaction Packet Header
    
    # Isochronous Timestamp Packet
    ITP = 0b0001  # Isochronous Timestamp Packet
    
    # Link Management Packets
    LMP = 0b0000  # Link Management Packet
    
    # Extended variants (if applicable)
    EDPH = 0b1101  # Extended Data Packet Header
    ESPH = 0b1111  # Extended Status Packet Header


# ============================================================================
# USB Packet Generation
# ============================================================================

class USBGeneration(IntEnum):
    """USB Data Packet Generation"""
    GEN1 = 1  # USB 3.0/3.1 Gen 1
    GEN2 = 2  # USB 3.1 Gen 2 / 3.2


# ============================================================================
# Framing Symbols
# ============================================================================

# END symbols (4 types)
EPF_END = 0b00  # EPF: End of Packet, no error
EPS_END = 0b01  # EPS: End of Packet with Stream error
EPD_END = 0b10  # EPD: End of Packet with Decode error  
EPN_END = 0b11  # EPN: End of Packet with No error (Gen 2)

# START symbols (4 types)
SHP = 0b00  # Start of Header Packet
SDP = 0b01  # Start of Data Packet
SHDP = 0b10  # Start of Header and Data Packet
ESDP = 0b11  # Extended Start of Data Packet (Gen 2)


# ============================================================================
# Data Structures
# ============================================================================

@dataclass
class DataPacketHeader:
    """12-byte Data Packet Header"""
    # Common fields
    header_type: int  # 4 bits - should be DPH (0x5)
    route_string: int  # 20 bits
    device_address: int  # 7 bits
    endpoint: int  # 4 bits
    direction: int  # 1 bit (0=OUT, 1=IN)
    
    # DPH specific
    sequence_number: int  # 5 bits
    number_of_packets: int  # 5 bits
    data_length: int  # 16 bits (in bytes)
    stream_id: int  # 16 bits
    
    # Header CRC
    header_crc: int  # 16 bits
    
    def to_bytes(self) -> bytes:
        """Convert header to 12 bytes"""
        # DW0: Type(4) + RouteString(20) + DevAddr(7) + EP(4) + Dir(1) = 36 bits
        dw0 = (self.header_type & 0xF) << 32
        dw0 |= (self.route_string & 0xFFFFF) << 12
        dw0 |= (self.device_address & 0x7F) << 5
        dw0 |= (self.endpoint & 0xF) << 1
        dw0 |= (self.direction & 0x1)
        
        # DW1: SeqNum(5) + NumPackets(5) + Reserved(6) + DataLength(16)
        dw1 = (self.sequence_number & 0x1F) << 27
        dw1 |= (self.number_of_packets & 0x1F) << 22
        dw1 |= (self.data_length & 0xFFFF)
        
        # DW2: StreamID(16) + HeaderCRC(16)
        dw2 = (self.stream_id & 0xFFFF) << 16
        dw2 |= (self.header_crc & 0xFFFF)
        
        # Pack as little-endian (LSB transmitted first)
        return struct.pack('<III', dw0 & 0xFFFFFFFF, dw1, dw2)
    
    @staticmethod
    def from_bytes(data: bytes) -> 'DataPacketHeader':
        """Parse 12-byte header"""
        if len(data) < 12:
            raise ValueError(f"Header must be 12 bytes, got {len(data)}")
        
        dw0, dw1, dw2 = struct.unpack('<III', data[:12])
        
        return DataPacketHeader(
            header_type=(dw0 >> 32) & 0xF if dw0 > 0xFFFFFFFF else (dw0 >> 28) & 0xF,
            route_string=(dw0 >> 12) & 0xFFFFF,
            device_address=(dw0 >> 5) & 0x7F,
            endpoint=(dw0 >> 1) & 0xF,
            direction=dw0 & 0x1,
            sequence_number=(dw1 >> 27) & 0x1F,
            number_of_packets=(dw1 >> 22) & 0x1F,
            data_length=dw1 & 0xFFFF,
            stream_id=(dw2 >> 16) & 0xFFFF,
            header_crc=dw2 & 0xFFFF
        )


@dataclass
class StatusPacketHeader:
    """12-byte Status Packet Header (SPH)"""
    header_type: int  # 4 bits - should be SPH (0x7)
    route_string: int  # 20 bits
    device_address: int  # 7 bits
    endpoint: int  # 4 bits
    direction: int  # 1 bit
    
    # SPH specific
    sequence_number: int  # 5 bits
    number_of_packets: int  # 5 bits
    retry: int  # 1 bit
    
    # Header CRC
    header_crc: int  # 16 bits
    
    def to_bytes(self) -> bytes:
        """Convert header to 12 bytes"""
        dw0 = (self.header_type & 0xF) << 32
        dw0 |= (self.route_string & 0xFFFFF) << 12
        dw0 |= (self.device_address & 0x7F) << 5
        dw0 |= (self.endpoint & 0xF) << 1
        dw0 |= (self.direction & 0x1)
        
        dw1 = (self.sequence_number & 0x1F) << 27
        dw1 |= (self.number_of_packets & 0x1F) << 22
        dw1 |= (self.retry & 0x1) << 21
        
        dw2 = (self.header_crc & 0xFFFF)
        
        return struct.pack('<III', dw0 & 0xFFFFFFFF, dw1, dw2)


@dataclass
class DataPacket:
    """Complete USB Data Packet structure"""
    generation: USBGeneration
    
    # Framing - Start symbols
    start_symbols: List[int]  # 4 EPF/EPS/EPD/EPN symbols at MSB
    
    # Header
    header: DataPacketHeader
    
    # Link Control Word (2 bytes)
    link_control_word: int
    
    # Additional Gen 2 fields
    length_field_replica1: Optional[int] = None  # Gen 2 only
    length_field_replica2: Optional[int] = None  # Gen 2 only
    
    # Payload
    payload: bytes = b''
    
    # CRC and End framing
    crc32: int = 0
    end_symbols: List[int] = None  # 4 EPF/EPS/EPD/EPN symbols at LSB
    
    def __post_init__(self):
        if self.end_symbols is None:
            self.end_symbols = [EPF_END] * 4
    
    @property
    def total_framing_overhead(self) -> int:
        """Calculate total framing overhead in bytes"""
        if self.generation == USBGeneration.GEN1:
            return 20  # 12 header + 2 LCW + 2 CRC + 4 CRC + 8 framing
        else:  # GEN2
            return 24  # 12 header + 2 LCW + 2 LFR + 2 LFR + 2 CRC + 4 CRC + 8 framing
    
    @property
    def total_size(self) -> int:
        """Total packet size in bytes"""
        return self.total_framing_overhead + len(self.payload)


# ============================================================================
# Parser Class
# ============================================================================

class USBDataPacketParser:
    """Parser for USB 3.x Data Packets (Gen 1 and Gen 2)"""
    
    @staticmethod
    def parse_gen1_packet(data: bytes) -> DataPacket:
        """
        Parse Gen 1 Data Packet format.
        
        Structure (LSB transmitted first):
        - 4 EPF/EPS/EPD/EPN symbols (1 byte each) - Start
        - 12 bytes: Data Packet Header  
        - 2 bytes: Link Control Word
        - 2 bytes: CRC for above 14 bytes
        - 0-1024 bytes: Payload
        - 4 bytes: CRC-32 for payload
        - 4 EPF/EPS/EPD/EPN symbols (1 byte each) - End
        """
        if len(data) < 28:  # Minimum: 4+12+2+2+0+4+4
            raise ValueError(f"Gen 1 packet too short: {len(data)} bytes")
        
        offset = 0
        
        # Parse end symbols (transmitted first, so at LSB/start)
        end_symbols = [data[i] & 0x3 for i in range(4)]
        offset += 4
        
        # Parse header (12 bytes)
        header = DataPacketHeader.from_bytes(data[offset:offset+12])
        offset += 12
        
        # Parse Link Control Word (2 bytes)
        lcw = struct.unpack('<H', data[offset:offset+2])[0]
        offset += 2
        
        # Parse Header CRC (2 bytes) - skip for now
        header_crc = struct.unpack('<H', data[offset:offset+2])[0]
        offset += 2
        
        # Parse payload (variable length)
        payload_len = header.data_length
        if len(data) < offset + payload_len + 4 + 4:
            raise ValueError("Packet truncated")
        
        payload = data[offset:offset+payload_len]
        offset += payload_len
        
        # Parse CRC-32 (4 bytes)
        crc32 = struct.unpack('<I', data[offset:offset+4])[0]
        offset += 4
        
        # Parse start symbols (at MSB/end)
        start_symbols = [data[offset+i] & 0x3 for i in range(4)]
        
        return DataPacket(
            generation=USBGeneration.GEN1,
            start_symbols=start_symbols,
            header=header,
            link_control_word=lcw,
            payload=payload,
            crc32=crc32,
            end_symbols=end_symbols
        )
    
    @staticmethod
    def parse_gen2_packet(data: bytes) -> DataPacket:
        """
        Parse Gen 2 Data Packet format.
        
        Structure (LSB transmitted first):
        - 4 EPF/EPS/EPD/EPN symbols (1 byte each) - End
        - 12 bytes: Data Packet Header
        - 2 bytes: Link Control Word  
        - 2 bytes: Length Field Replica 1
        - 2 bytes: Length Field Replica 2
        - 2 bytes: CRC for above 18 bytes
        - 0-1024 bytes: Payload
        - 4 bytes: CRC-32 for payload
        - 4 EPF/EPS/EPD/EPN symbols (1 byte each) - Start
        """
        if len(data) < 32:  # Minimum: 4+12+2+2+2+2+0+4+4
            raise ValueError(f"Gen 2 packet too short: {len(data)} bytes")
        
        offset = 0
        
        # Parse end symbols
        end_symbols = [data[i] & 0x3 for i in range(4)]
        offset += 4
        
        # Parse header
        header = DataPacketHeader.from_bytes(data[offset:offset+12])
        offset += 12
        
        # Parse Link Control Word
        lcw = struct.unpack('<H', data[offset:offset+2])[0]
        offset += 2
        
        # Parse Length Field Replicas
        lfr1 = struct.unpack('<H', data[offset:offset+2])[0]
        offset += 2
        lfr2 = struct.unpack('<H', data[offset:offset+2])[0]
        offset += 2
        
        # Parse Header CRC (2 bytes)
        header_crc = struct.unpack('<H', data[offset:offset+2])[0]
        offset += 2
        
        # Parse payload
        payload_len = header.data_length
        if len(data) < offset + payload_len + 4 + 4:
            raise ValueError("Packet truncated")
        
        payload = data[offset:offset+payload_len]
        offset += payload_len
        
        # Parse CRC-32
        crc32 = struct.unpack('<I', data[offset:offset+4])[0]
        offset += 4
        
        # Parse start symbols
        start_symbols = [data[offset+i] & 0x3 for i in range(4)]
        
        return DataPacket(
            generation=USBGeneration.GEN2,
            start_symbols=start_symbols,
            header=header,
            link_control_word=lcw,
            length_field_replica1=lfr1,
            length_field_replica2=lfr2,
            payload=payload,
            crc32=crc32,
            end_symbols=end_symbols
        )
    
    @staticmethod
    def build_gen1_packet(header: DataPacketHeader, lcw: int, 
                          payload: bytes) -> bytes:
        """Build a Gen 1 Data Packet"""
        packet = bytearray()
        
        # End symbols (4 bytes) - transmitted first
        packet.extend([EPF_END, EPF_END, EPF_END, EPF_END])
        
        # Header (12 bytes)
        packet.extend(header.to_bytes())
        
        # Link Control Word (2 bytes)
        packet.extend(struct.pack('<H', lcw))
        
        # Header CRC placeholder (2 bytes)
        packet.extend(b'\x00\x00')
        
        # Payload
        packet.extend(payload)
        
        # CRC-32 placeholder (4 bytes)
        packet.extend(b'\x00\x00\x00\x00')
        
        # Start symbols (4 bytes)
        packet.extend([SHP, SHP, SHP, SHP])
        
        return bytes(packet)
    
    @staticmethod
    def build_gen2_packet(header: DataPacketHeader, lcw: int,
                          payload: bytes) -> bytes:
        """Build a Gen 2 Data Packet"""
        packet = bytearray()
        
        # End symbols (4 bytes)
        packet.extend([EPF_END, EPF_END, EPF_END, EPF_END])
        
        # Header (12 bytes)
        packet.extend(header.to_bytes())
        
        # Link Control Word (2 bytes)
        packet.extend(struct.pack('<H', lcw))
        
        # Length Field Replicas (2 + 2 bytes)
        data_len = header.data_length
        packet.extend(struct.pack('<H', data_len))
        packet.extend(struct.pack('<H', data_len))
        
        # Header CRC placeholder (2 bytes)
        packet.extend(b'\x00\x00')
        
        # Payload
        packet.extend(payload)
        
        # CRC-32 placeholder (4 bytes)
        packet.extend(b'\x00\x00\x00\x00')
        
        # Start symbols (4 bytes)
        packet.extend([SHP, SHP, SHP, SHP])
        
        return bytes(packet)


# ============================================================================
# Example Usage
# ============================================================================

if __name__ == "__main__":
    print("=== USB Data Packet Header Types ===")
    print(f"DPH (Data Packet Header): 0x{HeaderType.DPH:X}")
    print(f"SPH (Status Packet Header): 0x{HeaderType.SPH:X}")
    print(f"TPH (Transaction Packet Header): 0x{HeaderType.TPH:X}")
    print(f"ITP (Isochronous Timestamp Packet): 0x{HeaderType.ITP:X}")
    print()
    
    print("=== Framing Symbol Definitions ===")
    print(f"EPF (End Packet Frame, no error): 0b{EPF_END:02b}")
    print(f"EPS (End Packet Stream error): 0b{EPS_END:02b}")
    print(f"EPD (End Packet Decode error): 0b{EPD_END:02b}")
    print(f"EPN (End Packet No error): 0b{EPN_END:02b}")
    print()
    print(f"SHP (Start Header Packet): 0b{SHP:02b}")
    print(f"SDP (Start Data Packet): 0b{SDP:02b}")
    print(f"SHDP (Start Header+Data Packet): 0b{SHDP:02b}")
    print(f"ESDP (Extended Start Data Packet): 0b{ESDP:02b}")
    print()
    
    # Create example Data Packet Header
    header = DataPacketHeader(
        header_type=HeaderType.DPH,
        route_string=0x12345,
        device_address=5,
        endpoint=2,
        direction=1,  # IN
        sequence_number=3,
        number_of_packets=1,
        data_length=64,
        stream_id=0,
        header_crc=0xABCD
    )
    
    print("=== Example Data Packet Header ===")
    print(f"Type: DPH (0x{header.header_type:X})")
    print(f"Route String: 0x{header.route_string:05X}")
    print(f"Device Address: {header.device_address}")
    print(f"Endpoint: {header.endpoint} {'IN' if header.direction else 'OUT'}")
    print(f"Sequence Number: {header.sequence_number}")
    print(f"Number of Packets: {header.number_of_packets}")
    print(f"Data Length: {header.data_length} bytes")
    print(f"Stream ID: {header.stream_id}")
    print()
    
    # Build Gen 1 packet
    parser = USBDataPacketParser()
    payload = b"Hello USB 3.0!" + b"\x00" * 50  # 64 bytes total
    gen1_packet = parser.build_gen1_packet(header, lcw=0x1234, payload=payload)
    
    print(f"=== Gen 1 Packet ===")
    print(f"Total Size: {len(gen1_packet)} bytes")
    print(f"Overhead: 20 bytes (framing) + 12 (header) + 2 (LCW) + 2 (CRC) + 4 (CRC32)")
    print(f"Payload: {len(payload)} bytes")
    print()
    
    # Build Gen 2 packet
    gen2_packet = parser.build_gen2_packet(header, lcw=0x5678, payload=payload)
    
    print(f"=== Gen 2 Packet ===")
    print(f"Total Size: {len(gen2_packet)} bytes")
    print(f"Overhead: 24 bytes (includes 2 Length Field Replicas)")
    print(f"Payload: {len(payload)} bytes")
