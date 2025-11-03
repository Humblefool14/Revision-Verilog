import sys
from dataclasses import dataclass
from typing import List, Union, Tuple

@dataclass
class RRAPWriteCommand:
    """RRAP Write Command Format"""
    parity: int
    rsvd: int
    upper_addr: int  # bits [5:4]
    data: int  # 8 bits
    lower_addr: int  # 8 bits
    upper_addr_full: int  # bits [3:0]
    rsvd2: int
    parity_valid: bool
    rsvd_valid: bool
    
    @property
    def full_address(self):
        return (self.upper_addr << 10) | (self.upper_addr_full << 8) | self.lower_addr
    
    def __str__(self):
        status = []
        if not self.parity_valid:
            status.append("⚠ PARITY ERROR")
        if not self.rsvd_valid:
            status.append("⚠ RESERVED BITS NOT ZERO")
        status_str = " " + " | ".join(status) if status else ""
        
        return (f"RRAP Write Command:{status_str}\n"
                f"  Parity: {self.parity} {'✓' if self.parity_valid else '✗ Invalid'}\n"
                f"  Reserved: 0x{self.rsvd:X}, 0x{self.rsvd2:X} {'✓' if self.rsvd_valid else '✗ Should be 0'}\n"
                f"  Upper Address [5:4]: 0x{self.upper_addr:X}\n"
                f"  Data: 0x{self.data:02X}\n"
                f"  Lower Address: 0x{self.lower_addr:02X}\n"
                f"  Upper Address [3:0]: 0x{self.upper_addr_full:X}\n"
                f"  Full Address: 0x{self.full_address:03X}\n")

@dataclass
class RRAPWriteResponse:
    """RRAP Write Response Format"""
    parity: int
    rsvd: int
    ack: int
    rsvd_data: int  # All rsvd bits
    
    def __str__(self):
        return (f"RRAP Write Response:\n"
                f"  Parity: {self.parity}\n"
                f"  Reserved: 0x{self.rsvd:X}\n"
                f"  ACK: {self.ack}\n"
                f"  Status: {'Success' if self.ack == 1 else 'Failed'}\n")

@dataclass
class RRAPReadCommand:
    """RRAP Read Command Format"""
    parity: int
    rsvd1: int
    upper_addr: int  # bits [5:4]
    rsvd2: int
    lower_addr: int  # 8 bits
    upper_addr_full: int  # bits [3:0]
    rsvd3: int
    
    @property
    def full_address(self):
        return (self.upper_addr << 10) | (self.upper_addr_full << 8) | self.lower_addr
    
    def __str__(self):
        return (f"RRAP Read Command:\n"
                f"  Parity: {self.parity}\n"
                f"  Upper Address [5:4]: 0x{self.upper_addr:X}\n"
                f"  Lower Address: 0x{self.lower_addr:02X}\n"
                f"  Upper Address [3:0]: 0x{self.upper_addr_full:X}\n"
                f"  Full Address: 0x{self.full_address:03X}\n")

@dataclass
class RRAPReadResponse:
    """RRAP Read Response Format"""
    parity: int
    rsvd: int
    ack: int
    rsvd_byte3: int
    data: int  # 8 bits
    rsvd_byte1: int
    
    def __str__(self):
        return (f"RRAP Read Response:\n"
                f"  Parity: {self.parity}\n"
                f"  Reserved: 0x{self.rsvd:X}\n"
                f"  ACK: {self.ack}\n"
                f"  Data: 0x{self.data:02X}\n"
                f"  Status: {'Success' if self.ack == 1 else 'Failed'}\n")

class RRAPParser:
    """Parser for RRAP protocol messages"""
    
    @staticmethod
    def parse_write_command(data: bytes) -> RRAPWriteCommand:
        """Parse RRAP Write Command (4 bytes)"""
        if len(data) != 4:
            raise ValueError(f"Write command must be 4 bytes, got {len(data)}")
        
        byte3, byte2, byte1, byte0 = data
        
        parity = (byte3 >> 7) & 1
        rsvd = (byte3 >> 6) & 1
        upper_addr = (byte3 >> 4) & 0x3
        data_val = byte2
        lower_addr = byte1
        upper_addr_full = (byte0 >> 4) & 0xF
        rsvd2 = byte0 & 0xF
        
        return RRAPWriteCommand(parity, rsvd, upper_addr, data_val, 
                                lower_addr, upper_addr_full, rsvd2)
    
    @staticmethod
    def parse_write_response(data: bytes) -> RRAPWriteResponse:
        """Parse RRAP Write Response (4 bytes)"""
        if len(data) != 4:
            raise ValueError(f"Write response must be 4 bytes, got {len(data)}")
        
        byte3, byte2, byte1, byte0 = data
        
        parity = (byte3 >> 7) & 1
        rsvd = (byte3 >> 6) & 1
        ack = (byte3 >> 5) & 1
        rsvd_data = ((byte3 & 0x1F) << 24) | (byte2 << 16) | (byte1 << 8) | byte0
        
        return RRAPWriteResponse(parity, rsvd, ack, rsvd_data)
    
    @staticmethod
    def parse_read_command(data: bytes) -> RRAPReadCommand:
        """Parse RRAP Read Command (4 bytes)"""
        if len(data) != 4:
            raise ValueError(f"Read command must be 4 bytes, got {len(data)}")
        
        byte3, byte2, byte1, byte0 = data
        
        parity = (byte3 >> 7) & 1
        rsvd1 = (byte3 >> 6) & 1
        upper_addr = (byte3 >> 4) & 0x3
        rsvd2 = byte2
        lower_addr = byte1
        upper_addr_full = (byte0 >> 4) & 0xF
        rsvd3 = byte0 & 0xF
        
        return RRAPReadCommand(parity, rsvd1, upper_addr, rsvd2, 
                               lower_addr, upper_addr_full, rsvd3)
    
    @staticmethod
    def parse_read_response(data: bytes) -> RRAPReadResponse:
        """Parse RRAP Read Response (4 bytes)"""
        if len(data) != 4:
            raise ValueError(f"Read response must be 4 bytes, got {len(data)}")
        
        byte3, byte2, byte1, byte0 = data
        
        parity = (byte3 >> 7) & 1
        rsvd = (byte3 >> 6) & 1
        ack = (byte3 >> 5) & 1
        rsvd_byte3 = byte3 & 0x1F
        data_val = byte2
        rsvd_byte1 = (byte1 << 8) | byte0
        
        return RRAPReadResponse(parity, rsvd, ack, rsvd_byte3, data_val, rsvd_byte1)
    
    @staticmethod
    def auto_parse(data: bytes) -> Union[RRAPWriteCommand, RRAPWriteResponse, 
                                          RRAPReadCommand, RRAPReadResponse]:
        """Automatically detect and parse RRAP message type"""
        if len(data) != 4:
            raise ValueError(f"RRAP messages must be 4 bytes, got {len(data)}")
        
        byte0 = data[3]
        bits_0_1 = byte0 & 0x3
        
        # Determine message type based on bits [1:0] of Byte 0
        if bits_0_1 == 0b00:
            return RRAPParser.parse_write_command(data)
        elif bits_0_1 == 0b01:
            return RRAPParser.parse_write_response(data)
        elif bits_0_1 == 0b10:
            return RRAPParser.parse_read_command(data)
        elif bits_0_1 == 0b11:
            return RRAPParser.parse_read_response(data)

def read_rrap_file(filename: str) -> List[Union[RRAPWriteCommand, RRAPWriteResponse, 
                                                  RRAPReadCommand, RRAPReadResponse]]:
    """Read RRAP messages from file and parse them"""
    messages = []
    
    with open(filename, 'rb') as f:
        data = f.read()
    
    # Parse 4-byte chunks
    for i in range(0, len(data), 4):
        if i + 4 <= len(data):
            chunk = data[i:i+4]
            try:
                msg = RRAPParser.auto_parse(chunk)
                messages.append(msg)
            except Exception as e:
                print(f"Error parsing bytes at offset {i}: {e}")
    
    return messages

def main():
    if len(sys.argv) < 2:
        print("Usage: python rrap_parser.py <filename>")
        print("\nExample file format (binary): 4 bytes per message")
        print("\nOr create a test file with sample data:")
        
        # Create a sample test file
        test_data = bytes([
            # Write Command: addr=0x123, data=0xAB
            0x11, 0xAB, 0x23, 0x10,  # P=0, Upper[5:4]=0x0, Data=0xAB, Lower=0x23, Upper[3:0]=0x1, ends with 00
            # Write Response: ACK
            0x20, 0x00, 0x00, 0x01,  # P=0, ACK=1, ends with 01
            # Read Command: addr=0x123
            0x12, 0x00, 0x23, 0x12,  # P=0, Upper[5:4]=0x0, Lower=0x23, Upper[3:0]=0x1, ends with 10
            # Read Response: data=0xCD
            0x60, 0xCD, 0x00, 0x03,  # P=0, ACK=1, Data=0xCD, ends with 11
        ])
        
        with open('sample_rrap.bin', 'wb') as f:
            f.write(test_data)
        
        print("Created sample_rrap.bin with test data")
        print("\nParsing sample file...\n")
        filename = 'sample_rrap.bin'
    else:
        filename = sys.argv[1]
    
    try:
        messages = read_rrap_file(filename)
        
        print(f"Found {len(messages)} RRAP messages in '{filename}':\n")
        print("=" * 60)
        
        for i, msg in enumerate(messages, 1):
            print(f"\nMessage {i}:")
            print(msg)
            print("-" * 60)
            
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found")
    except Exception as e:
        print(f"Error: {e}")

if __name__ == "__main__":
    main()
