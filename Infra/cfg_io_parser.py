#!/usr/bin/env python3
"""
PCIe Configuration Request TLP Parser
Parses and validates Configuration Request Transaction Layer Packets per PCIe specification
Configuration Requests route by ID and use a 3 DW header
"""

from dataclasses import dataclass
from typing import Optional, List
from enum import Enum

class ConfigTLPType(Enum):
    """TLP Type field values for Configuration transactions"""
    CONFIG_READ_TYPE0 = 0b00100
    CONFIG_WRITE_TYPE0 = 0b00101
    CONFIG_READ_TYPE1 = 0b00110
    CONFIG_WRITE_TYPE1 = 0b00111

class ConfigRequestError(Exception):
    """Exception raised for Configuration Request validation errors"""
    pass

@dataclass
class ConfigRequestTLP:
    """Parsed Configuration Request TLP structure"""
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
    
    # Byte 8-11 (ID Routing Fields)
    bus_number: int         # Bus Number (8 bits)
    device_number: int      # Device Number (5 bits)
    function_number: int    # Function Number (3 bits)
    reserved: int           # Reserved (4 bits)
    ext_reg_number: int     # Extended Register Number (4 bits)
    register_number: int    # Register Number (6 bits)
    
    # Validation results
    is_valid: bool = True
    errors: List[str] = None
    
    def __post_init__(self):
        if self.errors is None:
            self.errors = []

class ConfigRequestParser:
    """Parser for PCIe Configuration Request TLPs"""
    
    def __init__(self, strict_reserved_check: bool = False):
        """
        Initialize parser
        
        Args:
            strict_reserved_check: If True, check reserved bits (optional per spec)
        """
        self.strict_reserved_check = strict_reserved_check
    
    def parse(self, tlp_bytes: bytes) -> ConfigRequestTLP:
        """
        Parse Configuration Request TLP from raw bytes
        
        Args:
            tlp_bytes: Minimum 12 bytes (3 DW header)
            
        Returns:
            ConfigRequestTLP object with parsed fields
            
        Raises:
            ValueError: If input is invalid
        """
        if len(tlp_bytes) < 12:
            raise ValueError(f"Configuration Request requires at least 12 bytes, got {len(tlp_bytes)}")
        
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
        
        # Parse Byte 8 (Bus Number)
        bus_number = tlp_bytes[8]
        
        # Parse Byte 9 (Device Number[4:0] and Function Number[2:0])
        byte9 = tlp_bytes[9]
        device_number = (byte9 >> 3) & 0x1F
        function_number = byte9 & 0x7
        
        # Parse Byte 10 (Reserved[3:0] and Extended Register Number[3:0])
        byte10 = tlp_bytes[10]
        reserved = (byte10 >> 4) & 0xF
        ext_reg_number = byte10 & 0xF
        
        # Parse Byte 11 (Register Number[5:0] and R[1:0])
        byte11 = tlp_bytes[11]
        register_number = (byte11 >> 2) & 0x3F
        # Lower 2 bits are Reserved (R)
        
        # Create TLP object
        tlp = ConfigRequestTLP(
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
            bus_number=bus_number,
            device_number=device_number,
            function_number=function_number,
            reserved=reserved,
            ext_reg_number=ext_reg_number,
            register_number=register_number
        )
        
        # Validate
        self._validate(tlp)
        
        return tlp
    
    def _validate(self, tlp: ConfigRequestTLP):
        """Validate Configuration Request TLP against specification rules"""
        errors = []
        
        # Check TC[2:0] must be 000b
        if tlp.tc != 0b000:
            errors.append(f"TC[2:0] must be 000b, got {tlp.tc:03b}b")
        
        # Check LN is not applicable (should be Reserved/0)
        if self.strict_reserved_check and tlp.ln != 0:
            errors.append(f"LN is not applicable to Configuration Requests (Reserved), should be 0, got {tlp.ln}")
        
        # Check TH is not applicable (should be Reserved/0)
        if self.strict_reserved_check and tlp.th != 0:
            errors.append(f"TH is not applicable to Configuration Requests (Reserved), should be 0, got {tlp.th}")
        
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
        
        # Check Reserved field (4 bits in Byte 10)
        if self.strict_reserved_check and tlp.reserved != 0:
            errors.append(f"Reserved field should be 0000b, got {tlp.reserved:04b}b")
        
        # Check Format field (must be 000 for 3 DW header, no data)
        if tlp.fmt != 0b000:
            errors.append(f"Format must be 000b for 3 DW header, got {tlp.fmt:03b}b")
        
        # Check Type field (must be valid config type)
        valid_types = [0b00100, 0b00101, 0b00110, 0b00111]
        if tlp.type not in valid_types:
            errors.append(f"Type must be Config Read/Write Type 0/1, got {tlp.type:05b}b")
        
        # Check Device Number range (0-31)
        if tlp.device_number > 31:
            errors.append(f"Device Number out of range (0-31), got {tlp.device_number}")
        
        # Check Function Number range (0-7)
        if tlp.function_number > 7:
            errors.append(f"Function Number out of range (0-7), got {tlp.function_number}")
        
        # Check Register Number range (0-63)
        if tlp.register_number > 63:
            errors.append(f"Register Number out of range (0-63), got {tlp.register_number}")
        
        # Check Extended Register Number range (0-15)
        if tlp.ext_reg_number > 15:
            errors.append(f"Extended Register Number out of range (0-15), got {tlp.ext_reg_number}")
        
        # Update TLP validation status
        tlp.errors = errors
        tlp.is_valid = len(errors) == 0
    
    def get_config_type(self, tlp: ConfigRequestTLP) -> Optional[str]:
        """Get Configuration request type"""
        type_map = {
            0b00100: "Config Read Type 0",
            0b00101: "Config Write Type 0",
            0b00110: "Config Read Type 1",
            0b00111: "Config Write Type 1"
        }
        return type_map.get(tlp.type)
    
    def get_register_address(self, tlp: ConfigRequestTLP) -> int:
        """
        Get the full 12-bit register address (Extended[3:0]:Register[5:0]:00b)
        This gives the byte address in the 4KB configuration space
        """
        return (tlp.ext_reg_number << 8) | (tlp.register_number << 2)
    
    def get_bdf(self, tlp: ConfigRequestTLP) -> str:
        """Get Bus:Device.Function notation"""
        return f"{tlp.bus_number:02X}:{tlp.device_number:02X}.{tlp.function_number}"
    
    def get_requester_bdf(self, tlp: ConfigRequestTLP) -> str:
        """Get Requester Bus:Device.Function notation"""
        bus = (tlp.requester_id >> 8) & 0xFF
        device = (tlp.requester_id >> 3) & 0x1F
        function = tlp.requester_id & 0x7
        return f"{bus:02X}:{device:02X}.{function}"
    
    def format_tlp(self, tlp: ConfigRequestTLP) -> str:
        """Format TLP for display"""
        lines = []
        lines.append("=" * 70)
        lines.append(f"PCIe Configuration Request TLP - {self.get_config_type(tlp)}")
        lines.append("=" * 70)
        lines.append(f"Valid: {'✓ YES' if tlp.is_valid else '✗ NO'}")
        
        if not tlp.is_valid:
            lines.append("\nValidation Errors:")
            for err in tlp.errors:
                lines.append(f"  • {err}")
        
        lines.append("\nHeader Fields:")
        lines.append(f"  Format (Fmt):        {tlp.fmt:03b}b (3 DW header, routes by ID)")
        lines.append(f"  Type:                {tlp.type:05b}b ({self.get_config_type(tlp)})")
        lines.append(f"  Traffic Class (TC):  {tlp.tc:03b}b")
        lines.append(f"  Attr[2]:             {tlp.attr_bit2}b (Reserved)")
        lines.append(f"  LN:                  {tlp.ln}b (Not applicable)")
        lines.append(f"  TH:                  {tlp.th}b (Not applicable)")
        lines.append(f"  TD:                  {tlp.td}b")
        lines.append(f"  EP:                  {tlp.ep}b")
        lines.append(f"  Attr[1:0]:           {tlp.attr_1_0:02b}b")
        lines.append(f"  AT[1:0]:             {tlp.at:02b}b")
        lines.append(f"  Length:              {tlp.length:010b}b ({tlp.length} DW)")
        
        lines.append(f"\n  Requester ID:        0x{tlp.requester_id:04X} ({self.get_requester_bdf(tlp)})")
        lines.append(f"    Bus:               {(tlp.requester_id >> 8) & 0xFF} (0x{(tlp.requester_id >> 8) & 0xFF:02X})")
        lines.append(f"    Device:            {(tlp.requester_id >> 3) & 0x1F} (0x{(tlp.requester_id >> 3) & 0x1F:02X})")
        lines.append(f"    Function:          {tlp.requester_id & 0x7}")
        
        lines.append(f"\n  Tag:                 0x{tlp.tag:02X}")
        lines.append(f"  Last DW BE:          {tlp.last_dw_be:04b}b")
        lines.append(f"  First DW BE:         {tlp.first_dw_be:04b}b")
        
        lines.append(f"\nID Routing Fields (Target):")
        lines.append(f"  Bus Number:          {tlp.bus_number} (0x{tlp.bus_number:02X})")
        lines.append(f"  Device Number:       {tlp.device_number} (0x{tlp.device_number:02X})")
        lines.append(f"  Function Number:     {tlp.function_number}")
        lines.append(f"  Target BDF:          {self.get_bdf(tlp)}")
        
        lines.append(f"\nConfiguration Space Address:")
        lines.append(f"  Reserved:            {tlp.reserved:04b}b")
        lines.append(f"  Ext. Reg. Number:    {tlp.ext_reg_number} (0x{tlp.ext_reg_number:X})")
        lines.append(f"  Register Number:     {tlp.register_number} (0x{tlp.register_number:02X})")
        lines.append(f"  Full Reg Address:    0x{self.get_register_address(tlp):03X}")
        lines.append("=" * 70)
        
        return "\n".join(lines)


def main():
    """Example usage"""
    parser = ConfigRequestParser(strict_reserved_check=True)
    
    # Example 1: Valid Config Read Type 0 Request
    print("Example 1: Valid Config Read Type 0 Request")
    print("Reading Vendor ID/Device ID (offset 0x000) from device 00:1F.0")
    print("-" * 70)
    config_read_t0 = bytes([
        0b000_00100,  # Fmt=000, Type=00100 (Config Read Type 0)
        0b000_0_0_0_0_0,  # TC=000, Attr[2]=0, LN=0, TH=0, TD=0, EP=0
        0b00_00_0000,  # Attr[1:0]=00, AT=00, Length[9:8]=00
        0b00000001,    # Length[7:0]=00000001 (1 DW)
        0x00, 0x00,    # Requester ID (00:00.0)
        0x42,          # Tag
        0b0000_1111,   # Last DW BE=0000, First DW BE=1111 (read 4 bytes)
        0x00,          # Bus Number = 0
        0b11111_000,   # Device=31 (0x1F), Function=0
        0b0000_0000,   # Reserved=0000, Ext Reg=0
        0b000000_00    # Register=0, R=00
    ])
    
    tlp = parser.parse(config_read_t0)
    print(parser.format_tlp(tlp))
    
    # Example 2: Valid Config Write Type 1 Request
    print("\n\nExample 2: Valid Config Write Type 1 Request")
    print("Writing to Command Register (offset 0x004) on device 05:03.2")
    print("-" * 70)
    config_write_t1 = bytes([
        0b000_00111,  # Fmt=000, Type=00111 (Config Write Type 1)
        0b000_0_0_0_0_0,  # TC=000, Attr[2]=0, LN=0, TH=0, TD=0, EP=0
        0b00_00_0000,  # Attr[1:0]=00, AT=00, Length[9:8]=00
        0b00000001,    # Length[7:0]=00000001 (1 DW)
        0x01, 0x08,    # Requester ID (01:01.0)
        0x7F,          # Tag
        0b0000_0011,   # Last DW BE=0000, First DW BE=0011 (write lower 2 bytes)
        0x05,          # Bus Number = 5
        0b00011_010,   # Device=3, Function=2
        0b0000_0000,   # Reserved=0000, Ext Reg=0
        0b000001_00    # Register=1 (0x004 = register 1 * 4), R=00
    ])
    
    tlp = parser.parse(config_write_t1)
    print(parser.format_tlp(tlp))
    
    # Example 3: Config Read with Extended Register (PCIe Extended Config Space)
    print("\n\nExample 3: Config Read Type 0 - Extended Config Space")
    print("Reading PCIe Capability at offset 0x100 from device 00:00.0")
    print("-" * 70)
    config_read_ext = bytes([
        0b000_00100,  # Fmt=000, Type=00100 (Config Read Type 0)
        0b000_0_0_0_0_0,  # TC=000, all reserved bits 0
        0b00_00_0000,  # Attr[1:0]=00, AT=00, Length[9:8]=00
        0b00000001,    # Length[7:0]=00000001 (1 DW)
        0x00, 0x00,    # Requester ID (00:00.0)
        0xAA,          # Tag
        0b0000_1111,   # Last DW BE=0000, First DW BE=1111
        0x00,          # Bus Number = 0
        0b00000_000,   # Device=0, Function=0
        0b0000_0001,   # Reserved=0000, Ext Reg=1 (0x100)
        0b000000_00    # Register=0, R=00
    ])
    
    tlp = parser.parse(config_read_ext)
    print(parser.format_tlp(tlp))
    
    # Example 4: Invalid Config Request with multiple errors
    print("\n\nExample 4: Invalid Config Request with Violations")
    print("-" * 70)
    config_bad = bytes([
        0b000_00100,  # Fmt=000, Type=00100
        0b001_1_1_1_0_0,  # TC=001 (WRONG!), LN=1 (WRONG!), TH=1 (WRONG!), Attr[2]=1 (WRONG!)
        0b01_01_0000,  # Attr[1:0]=01 (WRONG!), AT=01 (WRONG!)
        0b00000010,    # Length=2 DW (WRONG!)
        0x12, 0x34,    # Requester ID
        0xCD,          # Tag
        0b0001_1111,   # Last DW BE=0001 (WRONG!), First DW BE=1111
        0x0A,          # Bus Number = 10
        0b00101_011,   # Device=5, Function=3
        0b1111_0010,   # Reserved=1111 (WRONG!), Ext Reg=2
        0b001000_00    # Register=8, R=00
    ])
    
    tlp = parser.parse(config_bad)
    print(parser.format_tlp(tlp))


if __name__ == "__main__":
    main()
