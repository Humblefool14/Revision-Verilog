#!/usr/bin/env python3
"""
PCIe I/O Request TLP Parser
Parses and validates I/O Request Transaction Layer Packets per PCIe specification
"""

from dataclasses import dataclass
from typing import Optional, List
from enum import Enum

class TLPType(Enum):
    """TLP Type field values for I/O transactions"""
    IO_READ = 0b00010
    IO_WRITE = 0b00011

class IORequestError(Exception):
    """Exception raised for I/O Request validation errors"""
    pass

@dataclass
class IORequestTLP:
    """Parsed I/O Request TLP structure"""
    # Byte 0
    fmt: int           # Format (3 bits)
    type: int          # Type (5 bits)
    
    # Byte 1
    tc: int            # Traffic Class (3 bits)
    attr_bit2: int     # Attr[2] (1 bit)
    ln: int            # LN bit (1 bit)
    th: int            # TH bit (1 bit)
    td: int            # TD bit (1 bit)
    ep: int            # EP bit (1 bit)
    attr_1_0: int      # Attr[1:0] (2 bits)
    at: int            # AT field (2 bits)
    
    # Byte 2-3
    length: int        # Length field (10 bits)
    
    # Byte 4-5
    requester_id: int  # Requester ID (16 bits)
    
    # Byte 6-7
    tag: int           # Tag (8 bits)
    last_dw_be: int    # Last DW BE (4 bits)
    first_dw_be: int   # First DW BE (4 bits)
    
    # Byte 8-11
    address: int       # Address[31:2] (30 bits) + Reserved (2 bits)
    
    # Validation results
    is_valid: bool = True
    errors: List[str] = None
    
    def __post_init__(self):
        if self.errors is None:
            self.errors = []

class IORequestParser:
    """Parser for PCIe I/O Request TLPs"""
    
    def __init__(self, strict_reserved_check: bool = False):
        """
        Initialize parser
        
        Args:
            strict_reserved_check: If True, check reserved bits (optional per spec)
        """
        self.strict_reserved_check = strict_reserved_check
    
    def parse(self, tlp_bytes: bytes) -> IORequestTLP:
        """
        Parse I/O Request TLP from raw bytes
        
        Args:
            tlp_bytes: Minimum 12 bytes (3 DW header)
            
        Returns:
            IORequestTLP object with parsed fields
            
        Raises:
            ValueError: If input is invalid
        """
        if len(tlp_bytes) < 12:
            raise ValueError(f"I/O Request requires at least 12 bytes, got {len(tlp_bytes)}")
        
        # Parse Byte 0
        byte0 = tlp_bytes[0]
        fmt = (byte0 >> 5) & 0x7
        tlp_type = byte0 & 0x1F
        
        # Parse Byte 1
        byte1 = tlp_bytes[1]
        tc = (byte1 >> 5) & 0x7
        attr_bit2 = (byte1 >> 4) & 0x1
        ln = (byte1 >> 3) & 0x1
        th = (byte1 >> 2) & 0x1
        td = (byte1 >> 1) & 0x1
        ep = byte1 & 0x1
        
        # Parse Byte 2
        byte2 = tlp_bytes[2]
        attr_1_0 = (byte2 >> 6) & 0x3
        at = (byte2 >> 4) & 0x3
        length_high = byte2 & 0x3
        
        # Parse Byte 3
        byte3 = tlp_bytes[3]
        length = (length_high << 8) | byte3
        
        # Parse Byte 4-5 (Requester ID)
        requester_id = (tlp_bytes[4] << 8) | tlp_bytes[5]
        
        # Parse Byte 6-7
        tag = tlp_bytes[6]
        byte7 = tlp_bytes[7]
        last_dw_be = (byte7 >> 4) & 0xF
        first_dw_be = byte7 & 0xF
        
        # Parse Byte 8-11 (Address)
        address = (tlp_bytes[8] << 24) | (tlp_bytes[9] << 16) | \
                  (tlp_bytes[10] << 8) | tlp_bytes[11]
        
        # Create TLP object
        tlp = IORequestTLP(
            fmt=fmt,
            type=tlp_type,
            tc=tc,
            attr_bit2=attr_bit2,
            ln=ln,
            th=th,
            td=td,
            ep=ep,
            attr_1_0=attr_1_0,
            at=at,
            length=length,
            requester_id=requester_id,
            tag=tag,
            last_dw_be=last_dw_be,
            first_dw_be=first_dw_be,
            address=address
        )
        
        # Validate
        self._validate(tlp)
        
        return tlp
    
    def _validate(self, tlp: IORequestTLP):
        """Validate I/O Request TLP against specification rules"""
        errors = []
        
        # Check TC[2:0] must be 000b
        if tlp.tc != 0b000:
            errors.append(f"TC[2:0] must be 000b, got {tlp.tc:03b}b")
        
        # Check LN is not applicable (should be Reserved/0)
        if self.strict_reserved_check and tlp.ln != 0:
            errors.append(f"LN is not applicable to I/O Requests (Reserved), should be 0, got {tlp.ln}")
        
        # Check TH is not applicable (should be Reserved/0)
        if self.strict_reserved_check and tlp.th != 0:
            errors.append(f"TH is not applicable to I/O Requests (Reserved), should be 0, got {tlp.th}")
        
        # Check Attr[2] is Reserved (should be 0)
        if self.strict_reserved_check and tlp.attr_bit2 != 0:
            errors.append(f"Attr[2] is Reserved, should be 0, got {tlp.attr_bit2}")
        
        # Check Attr[1:0] must be 00b
        if tlp.attr_1_0 != 0b00:
            errors.append(f"Attr[1:0] must be 00b, got {tlp.attr_1_0:02b}b")
        
        # Check AT[1:0] must be 00b (note: receivers not required to check)
        if tlp.at != 0b00:
            errors.append(f"AT[1:0] must be 00b (not enforced by receivers), got {tlp.at:02b}b")
        
        # Check Length[9:0] must be 00 0000 0001b (1 DW)
        if tlp.length != 0b0000000001:
            errors.append(f"Length[9:0] must be 00 0000 0001b (1 DW), got {tlp.length:010b}b")
        
        # Check Last DW BE[3:0] must be 0000b
        if tlp.last_dw_be != 0b0000:
            errors.append(f"Last DW BE[3:0] must be 0000b, got {tlp.last_dw_be:04b}b")
        
        # Check Address[1:0] (lower 2 bits) must be Reserved (00b for 32-bit addressing)
        addr_low_2 = tlp.address & 0x3
        if self.strict_reserved_check and addr_low_2 != 0:
            errors.append(f"Address[1:0] is Reserved, should be 00b, got {addr_low_2:02b}b")
        
        # Check Format field (32-bit addressing)
        if tlp.fmt != 0b000:
            errors.append(f"Format must be 000b for 32-bit addressing, got {tlp.fmt:03b}b")
        
        # Check Type field
        if tlp.type not in [0b00010, 0b00011]:
            errors.append(f"Type must be I/O Read (00010b) or I/O Write (00011b), got {tlp.type:05b}b")
        
        # Update TLP validation status
        tlp.errors = errors
        tlp.is_valid = len(errors) == 0
    
    def get_io_type(self, tlp: IORequestTLP) -> Optional[str]:
        """Get I/O request type (Read/Write)"""
        if tlp.type == 0b00010:
            return "I/O Read"
        elif tlp.type == 0b00011:
            return "I/O Write"
        return None
    
    def get_address(self, tlp: IORequestTLP) -> int:
        """Get the actual I/O address (Address[31:2] aligned)"""
        return (tlp.address >> 2) << 2  # Clear lower 2 bits
    
    def format_tlp(self, tlp: IORequestTLP) -> str:
        """Format TLP for display"""
        lines = []
        lines.append("=" * 70)
        lines.append(f"PCIe I/O Request TLP - {self.get_io_type(tlp)}")
        lines.append("=" * 70)
        lines.append(f"Valid: {'✓ YES' if tlp.is_valid else '✗ NO'}")
        
        if not tlp.is_valid:
            lines.append("\nValidation Errors:")
            for err in tlp.errors:
                lines.append(f"  • {err}")
        
        lines.append("\nHeader Fields:")
        lines.append(f"  Format (Fmt):        {tlp.fmt:03b}b (32-bit addressing)")
        lines.append(f"  Type:                {tlp.type:05b}b ({self.get_io_type(tlp)})")
        lines.append(f"  Traffic Class (TC):  {tlp.tc:03b}b")
        lines.append(f"  Attr[2]:             {tlp.attr_bit2}b (Reserved)")
        lines.append(f"  LN:                  {tlp.ln}b (Not applicable)")
        lines.append(f"  TH:                  {tlp.th}b (Not applicable)")
        lines.append(f"  TD:                  {tlp.td}b")
        lines.append(f"  EP:                  {tlp.ep}b")
        lines.append(f"  Attr[1:0]:           {tlp.attr_1_0:02b}b")
        lines.append(f"  AT[1:0]:             {tlp.at:02b}b")
        lines.append(f"  Length:              {tlp.length:010b}b ({tlp.length} DW)")
        lines.append(f"  Requester ID:        0x{tlp.requester_id:04X}")
        lines.append(f"    Bus:               {(tlp.requester_id >> 8) & 0xFF}")
        lines.append(f"    Device:            {(tlp.requester_id >> 3) & 0x1F}")
        lines.append(f"    Function:          {tlp.requester_id & 0x7}")
        lines.append(f"  Tag:                 0x{tlp.tag:02X}")
        lines.append(f"  Last DW BE:          {tlp.last_dw_be:04b}b")
        lines.append(f"  First DW BE:         {tlp.first_dw_be:04b}b")
        lines.append(f"  Address[31:2]:       0x{self.get_address(tlp):08X}")
        lines.append(f"  Address[1:0]:        {tlp.address & 0x3:02b}b (Reserved)")
        lines.append("=" * 70)
        
        return "\n".join(lines)


def main():
    """Example usage"""
    parser = IORequestParser(strict_reserved_check=True)
    
    # Example 1: Valid I/O Read Request
    print("Example 1: Valid I/O Read Request")
    print("-" * 70)
    io_read = bytes([
        0b000_00010,  # Fmt=000, Type=00010 (I/O Read)
        0b000_0_0_0_0_0,  # TC=000, Attr[2]=0, LN=0, TH=0, TD=0, EP=0
        0b00_00_0000,  # Attr[1:0]=00, AT=00, Length[9:8]=00
        0b00000001,    # Length[7:0]=00000001 (1 DW)
        0x12, 0x34,    # Requester ID
        0xAB,          # Tag
        0b0000_1111,   # Last DW BE=0000, First DW BE=1111
        0x00, 0x00, 0xCF, 0x8C  # Address = 0x0000CF8C (aligned)
    ])
    
    tlp = parser.parse(io_read)
    print(parser.format_tlp(tlp))
    
    # Example 2: I/O Write with errors
    print("\n\nExample 2: I/O Write Request with Violations")
    print("-" * 70)
    io_write_bad = bytes([
        0b000_00011,  # Fmt=000, Type=00011 (I/O Write)
        0b001_0_1_1_0_0,  # TC=001 (WRONG!), LN=1 (WRONG!), TH=1 (WRONG!)
        0b01_01_0000,  # Attr[1:0]=01 (WRONG!), AT=01 (WRONG!)
        0b00000010,    # Length=2 DW (WRONG!)
        0x56, 0x78,    # Requester ID
        0xCD,          # Tag
        0b0001_1111,   # Last DW BE=0001 (WRONG!), First DW BE=1111
        0x00, 0x01, 0x00, 0x03  # Address with bit[0]=1 (WRONG!)
    ])
    
    tlp = parser.parse(io_write_bad)
    print(parser.format_tlp(tlp))


if __name__ == "__main__":
    main()
