#!/usr/bin/env python3
"""
USB SuperSpeed Link Command Parser

Parses framed 8-symbol link commands used in USB 3.x SuperSpeed links.
Supports: LXU, LAU, LGO_Ux, LRTY
"""

from dataclasses import dataclass
from typing import Optional, Tuple
from enum import Enum


class LinkCommandType(Enum):
    """Link Command Types based on Class and Type bits"""
    LXU = (0, 1, 1, 0)      # Class=0, Type=110
    LAU = (0, 1, 0, 1)      # Class=0, Type=101
    LGO_Ux = (0, 1, 0, 0)   # Class=0, Type=100
    LRTY = (0, 0, 1, 0)     # Class=0, Type=010
    
    def __init__(self, class_bit, type_bit2, type_bit1, type_bit0):
        self.class_bit = class_bit
        self.type_bits = (type_bit2, type_bit1, type_bit0)


@dataclass
class LinkCommandWord:
    """Represents a 16-bit Link Command Word"""
    class_bit: int          # Bit 11
    type_bits: Tuple[int, int, int]  # Bits 10, 9, 8
    rsvd: int               # Bits 7-6-5-4 (Reserved)
    sub_type: Tuple[int, int, int, int]  # Bits 3-2-1-0
    
    @classmethod
    def from_bits(cls, bits: int):
        """Parse 16-bit value into Link Command Word"""
        class_bit = (bits >> 11) & 0x1
        type_bit2 = (bits >> 10) & 0x1
        type_bit1 = (bits >> 9) & 0x1
        type_bit0 = (bits >> 8) & 0x1
        rsvd = (bits >> 4) & 0xF
        sub_type_3 = (bits >> 3) & 0x1
        sub_type_2 = (bits >> 2) & 0x1
        sub_type_1 = (bits >> 1) & 0x1
        sub_type_0 = bits & 0x1
        
        return cls(
            class_bit=class_bit,
            type_bits=(type_bit2, type_bit1, type_bit0),
            rsvd=rsvd,
            sub_type=(sub_type_3, sub_type_2, sub_type_1, sub_type_0)
        )
    
    def get_command_type(self) -> Optional[LinkCommandType]:
        """Identify the command type"""
        signature = (self.class_bit, *self.type_bits)
        for cmd_type in LinkCommandType:
            if signature == (cmd_type.class_bit, *cmd_type.type_bits):
                return cmd_type
        return None
    
    def to_hex(self) -> str:
        """Convert to hex string representation"""
        bits = (self.class_bit << 11) | \
               (self.type_bits[0] << 10) | \
               (self.type_bits[1] << 9) | \
               (self.type_bits[2] << 8) | \
               (self.rsvd << 4) | \
               (self.sub_type[0] << 3) | \
               (self.sub_type[1] << 2) | \
               (self.sub_type[2] << 1) | \
               self.sub_type[3]
        return f"0x{bits:04X}"


@dataclass
class LinkCommand:
    """Complete Link Command packet"""
    crc5_header: int
    command_word_1: LinkCommandWord
    crc5_middle: int
    command_word_2: LinkCommandWord  # Replica - must match command_word_1
    epf: int                # End of Packet Framing
    slc: Tuple[int, int, int]  # Start Link Command symbols
    
    def validate(self) -> Tuple[bool, str]:
        """Validate the link command packet"""
        # Check if both command words match
        if self.command_word_1.to_hex() != self.command_word_2.to_hex():
            return False, "Command word replica mismatch"
        
        # Check if valid command type
        cmd_type = self.command_word_1.get_command_type()
        if cmd_type is None:
            return False, "Unknown command type"
        
        return True, "Valid"
    
    def get_command_name(self) -> str:
        """Get the human-readable command name"""
        cmd_type = self.command_word_1.get_command_type()
        if cmd_type:
            return cmd_type.name
        return "UNKNOWN"
    
    def get_u_state(self) -> Optional[int]:
        """Get U state for LGO_Ux commands"""
        cmd_type = self.command_word_1.get_command_type()
        if cmd_type == LinkCommandType.LGO_Ux:
            # U state is encoded in sub-type bits 1-0
            return (self.command_word_1.sub_type[2] << 1) | self.command_word_1.sub_type[3]
        return None


def parse_link_command(data: bytes) -> LinkCommand:
    """
    Parse a raw link command packet
    
    Args:
        data: Raw bytes of the link command (minimum 5 bytes)
        
    Returns:
        LinkCommand object
    """
    if len(data) < 5:
        raise ValueError("Link command must be at least 5 bytes")
    
    # Parse CRC-5 and command words
    # Assuming byte order: [CRC5_1][CMD1_high][CMD1_low][CRC5_2][CMD2_high][CMD2_low][Framing...]
    crc5_header = data[0] & 0x1F  # 5 bits
    
    cmd_word_1_bits = (data[1] << 8) | data[2]
    command_word_1 = LinkCommandWord.from_bits(cmd_word_1_bits)
    
    crc5_middle = data[3] & 0x1F
    
    cmd_word_2_bits = (data[4] << 8) | data[5]
    command_word_2 = LinkCommandWord.from_bits(cmd_word_2_bits)
    
    # Parse framing if available
    epf = 0
    slc = (0, 0, 0)
    if len(data) >= 7:
        epf = data[6] & 0x1
        if len(data) >= 10:
            slc = (data[7] & 0x1, data[8] & 0x1, data[9] & 0x1)
    
    return LinkCommand(
        crc5_header=crc5_header,
        command_word_1=command_word_1,
        crc5_middle=crc5_middle,
        command_word_2=command_word_2,
        epf=epf,
        slc=slc
    )


def create_link_command(cmd_type: LinkCommandType, sub_type: int = 0) -> bytes:
    """
    Create a link command packet
    
    Args:
        cmd_type: Type of link command
        sub_type: 4-bit sub-type value
        
    Returns:
        Raw bytes of the link command
    """
    # Build command word bits
    bits = (cmd_type.class_bit << 11) | \
           (cmd_type.type_bits[0] << 10) | \
           (cmd_type.type_bits[1] << 9) | \
           (cmd_type.type_bits[2] << 8) | \
           (sub_type & 0xF)
    
    cmd_high = (bits >> 8) & 0xFF
    cmd_low = bits & 0xFF
    
    # For simplicity, using dummy CRC-5 values (real implementation would calculate these)
    crc5_1 = 0x00
    crc5_2 = 0x00
    
    # Build packet: CRC5, CMD1, CRC5, CMD2 (replica), Framing
    packet = bytes([
        crc5_1,
        cmd_high, cmd_low,
        crc5_2,
        cmd_high, cmd_low,  # Replica
        0x01,  # EPF
        0x00, 0x00, 0x00  # SLC symbols
    ])
    
    return packet


def print_link_command(cmd: LinkCommand):
    """Pretty print a link command"""
    print("=" * 60)
    print(f"Link Command: {cmd.get_command_name()}")
    print("=" * 60)
    
    valid, msg = cmd.validate()
    print(f"Validation: {msg}")
    print()
    
    print("Command Word 1:")
    print(f"  Hex: {cmd.command_word_1.to_hex()}")
    print(f"  Class: {cmd.command_word_1.class_bit}")
    print(f"  Type: {cmd.command_word_1.type_bits}")
    print(f"  Reserved: {cmd.command_word_1.rsvd:04b}")
    print(f"  Sub-Type: {cmd.command_word_1.sub_type}")
    print()
    
    print("Command Word 2 (Replica):")
    print(f"  Hex: {cmd.command_word_2.to_hex()}")
    print(f"  Match: {'✓' if cmd.command_word_1.to_hex() == cmd.command_word_2.to_hex() else '✗'}")
    print()
    
    print(f"CRC-5 Header: 0x{cmd.crc5_header:02X}")
    print(f"CRC-5 Middle: 0x{cmd.crc5_middle:02X}")
    print(f"EPF: {cmd.epf}")
    print(f"SLC: {cmd.slc}")
    
    # Special handling for LGO_Ux
    u_state = cmd.get_u_state()
    if u_state is not None:
        print(f"\nU State: U{u_state}")
    
    print("=" * 60)


def main():
    """Demo of the parser"""
    print("USB SuperSpeed Link Command Parser\n")
    
    # Example 1: LXU command
    print("Example 1: Creating LXU command")
    lxu_packet = create_link_command(LinkCommandType.LXU, sub_type=0b0000)
    lxu_cmd = parse_link_command(lxu_packet)
    print_link_command(lxu_cmd)
    print()
    
    # Example 2: LAU command
    print("Example 2: Creating LAU command")
    lau_packet = create_link_command(LinkCommandType.LAU, sub_type=0b0000)
    lau_cmd = parse_link_command(lau_packet)
    print_link_command(lau_cmd)
    print()
    
    # Example 3: LGO_Ux command with U state
    print("Example 3: Creating LGO_U1 command")
    lgo_u1_packet = create_link_command(LinkCommandType.LGO_Ux, sub_type=0b0001)
    lgo_u1_cmd = parse_link_command(lgo_u1_packet)
    print_link_command(lgo_u1_cmd)
    print()
    
    # Example 4: LRTY command
    print("Example 4: Creating LRTY command")
    lrty_packet = create_link_command(LinkCommandType.LRTY, sub_type=0b0000)
    lrty_cmd = parse_link_command(lrty_packet)
    print_link_command(lrty_cmd)
    print()
    
    # Example 5: Manual packet parsing
    print("Example 5: Parsing manual hex data")
    # Simulating LXU: Class=0, Type=110, Sub-Type=0000
    # Binary: 0_110_0000_0000 = 0x0600
    manual_data = bytes([
        0x00,           # CRC-5 header
        0x06, 0x00,     # Command word 1: 0x0600
        0x00,           # CRC-5 middle
        0x06, 0x00,     # Command word 2: 0x0600 (replica)
        0x01,           # EPF
        0x00, 0x00, 0x00  # SLC
    ])
    manual_cmd = parse_link_command(manual_data)
    print_link_command(manual_cmd)


if __name__ == "__main__":
    main()
