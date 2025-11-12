from dataclasses import dataclass
from typing import Literal
from enum import IntEnum


class USBSpeed(IntEnum):
    """USB speed types"""
    SUPERSPEED = 5  # USB 3.0
    SUPERSPEED_PLUS = 10  # USB 3.1/3.2


@dataclass
class LinkControlWord:
    """Parsed Link Control Word structure"""
    speed: USBSpeed
    crc: int  # 5-bit CRC
    deferred: bool  # 1-bit DEFERRED flag
    delayed: bool  # 1-bit DELAYED flag
    hub_depth: int  # 3-bit Hub Depth
    reserved: int  # 2 or 3 bits (depends on speed)
    header_sequence: int  # 3 or 4 bits (depends on speed)
    raw_value: int  # Original 16-bit value
    
    def __str__(self):
        return (f"LinkControlWord(speed={self.speed.name}, "
                f"CRC=0x{self.crc:02X}, "
                f"DEFERRED={self.deferred}, "
                f"DELAYED={self.delayed}, "
                f"Hub_Depth={self.hub_depth}, "
                f"Reserved=0x{self.reserved:X}, "
                f"Header_Seq={self.header_sequence})")


class LinkControlWordParser:
    """Parser for USB SuperSpeed and SuperSpeedPlus Link Control Words"""
    
    @staticmethod
    def parse(value: int, speed: USBSpeed = USBSpeed.SUPERSPEED) -> LinkControlWord:
        """
        Parse a 16-bit Link Control Word.
        
        Args:
            value: 16-bit Link Control Word value
            speed: USB speed type (SUPERSPEED or SUPERSPEED_PLUS)
            
        Returns:
            LinkControlWord object with parsed fields
        """
        if not 0 <= value <= 0xFFFF:
            raise ValueError(f"Link Control Word must be 16-bit value (0x0000-0xFFFF), got 0x{value:X}")
        
        # Extract fields from LSB to MSB (byte 0 transmitted first)
        # Byte 0 (LSB): Header Sequence, Reserved, Hub Depth (partial)
        # Byte 1 (MSB): Hub Depth (partial), DELAYED, DEFERRED, CRC
        
        if speed == USBSpeed.SUPERSPEED:
            # SuperSpeed: 3-bit Header Seq, 3-bit Reserved, 3-bit Hub Depth, 
            # 1-bit DELAYED, 1-bit DEFERRED, 5-bit CRC
            header_sequence = value & 0x07  # bits 0-2
            reserved = (value >> 3) & 0x07  # bits 3-5
            hub_depth = (value >> 6) & 0x07  # bits 6-8
            delayed = bool((value >> 9) & 0x01)  # bit 9
            deferred = bool((value >> 10) & 0x01)  # bit 10
            crc = (value >> 11) & 0x1F  # bits 11-15
            
        else:  # SUPERSPEED_PLUS
            # SuperSpeedPlus: 4-bit Header Seq, 2-bit Reserved, 3-bit Hub Depth,
            # 1-bit DELAYED, 1-bit DEFERRED, 5-bit CRC
            header_sequence = value & 0x0F  # bits 0-3
            reserved = (value >> 4) & 0x03  # bits 4-5
            hub_depth = (value >> 6) & 0x07  # bits 6-8
            delayed = bool((value >> 9) & 0x01)  # bit 9
            deferred = bool((value >> 10) & 0x01)  # bit 10
            crc = (value >> 11) & 0x1F  # bits 11-15
        
        return LinkControlWord(
            speed=speed,
            crc=crc,
            deferred=deferred,
            delayed=delayed,
            hub_depth=hub_depth,
            reserved=reserved,
            header_sequence=header_sequence,
            raw_value=value
        )
    
    @staticmethod
    def build(crc: int, deferred: bool, delayed: bool, hub_depth: int,
              reserved: int, header_sequence: int, 
              speed: USBSpeed = USBSpeed.SUPERSPEED) -> int:
        """
        Build a 16-bit Link Control Word from individual fields.
        
        Args:
            crc: 5-bit CRC value
            deferred: DEFERRED flag
            delayed: DELAYED flag
            hub_depth: 3-bit Hub Depth
            reserved: 2 or 3-bit Reserved field (depends on speed)
            header_sequence: 3 or 4-bit Header Sequence (depends on speed)
            speed: USB speed type
            
        Returns:
            16-bit Link Control Word value
        """
        # Validate inputs
        if not 0 <= crc <= 0x1F:
            raise ValueError(f"CRC must be 5-bit value (0-31), got {crc}")
        if not 0 <= hub_depth <= 0x07:
            raise ValueError(f"Hub Depth must be 3-bit value (0-7), got {hub_depth}")
        
        if speed == USBSpeed.SUPERSPEED:
            if not 0 <= reserved <= 0x07:
                raise ValueError(f"Reserved must be 3-bit value (0-7) for SuperSpeed, got {reserved}")
            if not 0 <= header_sequence <= 0x07:
                raise ValueError(f"Header Sequence must be 3-bit value (0-7) for SuperSpeed, got {header_sequence}")
            
            value = (header_sequence & 0x07) | \
                    ((reserved & 0x07) << 3) | \
                    ((hub_depth & 0x07) << 6) | \
                    ((1 if delayed else 0) << 9) | \
                    ((1 if deferred else 0) << 10) | \
                    ((crc & 0x1F) << 11)
        else:  # SUPERSPEED_PLUS
            if not 0 <= reserved <= 0x03:
                raise ValueError(f"Reserved must be 2-bit value (0-3) for SuperSpeedPlus, got {reserved}")
            if not 0 <= header_sequence <= 0x0F:
                raise ValueError(f"Header Sequence must be 4-bit value (0-15) for SuperSpeedPlus, got {header_sequence}")
            
            value = (header_sequence & 0x0F) | \
                    ((reserved & 0x03) << 4) | \
                    ((hub_depth & 0x07) << 6) | \
                    ((1 if delayed else 0) << 9) | \
                    ((1 if deferred else 0) << 10) | \
                    ((crc & 0x1F) << 11)
        
        return value


# Example usage
if __name__ == "__main__":
    parser = LinkControlWordParser()
    
    # Example 1: Parse SuperSpeed Link Control Word
    print("=== SuperSpeed Examples ===")
    ss_value = 0xA5C3  # Example value
    ss_lcw = parser.parse(ss_value, USBSpeed.SUPERSPEED)
    print(f"Input: 0x{ss_value:04X}")
    print(ss_lcw)
    print(f"Binary: {ss_value:016b}\n")
    
    # Example 2: Parse SuperSpeedPlus Link Control Word
    print("=== SuperSpeedPlus Examples ===")
    ssp_value = 0x9AF5  # Example value
    ssp_lcw = parser.parse(ssp_value, USBSpeed.SUPERSPEED_PLUS)
    print(f"Input: 0x{ssp_value:04X}")
    print(ssp_lcw)
    print(f"Binary: {ssp_value:016b}\n")
    
    # Example 3: Build a Link Control Word
    print("=== Building Link Control Word ===")
    built_value = parser.build(
        crc=0x15,
        deferred=True,
        delayed=False,
        hub_depth=3,
        reserved=2,
        header_sequence=7,
        speed=USBSpeed.SUPERSPEED
    )
    print(f"Built value: 0x{built_value:04X}")
    print(f"Binary: {built_value:016b}")
    
    # Verify by parsing back
    verify = parser.parse(built_value, USBSpeed.SUPERSPEED)
    print(f"Parsed back: {verify}")
