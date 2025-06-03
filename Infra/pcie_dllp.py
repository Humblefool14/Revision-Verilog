import struct
from typing import Dict, Any, Optional, Union
from enum import Enum

class DLLPType(Enum):
    """DLLP Types based on the first byte patterns"""
    ACK = 0x00
    NAK = 0x10  # Corrected pattern
    NOP = 0x31  # Corrected pattern
    INIT_FC1 = 0x40  # Pattern: 0100xxxx
    INIT_FC2 = 0x50  # Pattern: 0101xxxx  
    UPDATE_FC = 0x60  # Pattern: 0110xxxx
    PM = 0x20  # Pattern: 001xxxxx
    VENDOR_SPECIFIC = 0x30  # Pattern: 0011xxxx
    FEATURE_DLLP = 0x02  # Pattern: 00000010

class PCIeDLLPParser:
    """
    Parser for PCIe Data Link Layer Packets (DLLPs)
    Supports all DLLP formats from PCIe specification
    """
    
    def __init__(self):
        self.fc_types = {
            0: "Posted",
            1: "Non-Posted", 
            2: "Completion"
        }
        
    def _calculate_crc16(self, data: bytes) -> int:
        """Calculate CRC-16 for DLLP (simplified implementation)"""
        # This is a placeholder - actual CRC-16 calculation would be more complex
        return sum(data) & 0xFFFF
        
    def _extract_bits(self, byte_val: int, start_bit: int, num_bits: int) -> int:
        """Extract specific bits from a byte value"""
        mask = (1 << num_bits) - 1
        return (byte_val >> start_bit) & mask
        
    def _determine_dllp_type(self, first_byte: int) -> DLLPType:
        """Determine DLLP type from first byte pattern"""
        if first_byte == 0x00:
            return DLLPType.ACK
        elif first_byte == 0x10:
            return DLLPType.NAK
        elif first_byte == 0x31:
            return DLLPType.NOP
        elif (first_byte & 0xF0) == 0x40:
            return DLLPType.INIT_FC1
        elif (first_byte & 0xF0) == 0x50:
            return DLLPType.INIT_FC2
        elif (first_byte & 0xF0) == 0x60:
            return DLLPType.UPDATE_FC
        elif (first_byte & 0xE0) == 0x20:
            return DLLPType.PM
        elif (first_byte & 0xF0) == 0x30 and first_byte != 0x31:  # Exclude NOP
            return DLLPType.VENDOR_SPECIFIC
        elif first_byte == 0x02:
            return DLLPType.FEATURE_DLLP
        else:
            raise ValueError(f"Unknown DLLP type: 0x{first_byte:02X}")
            
    def _parse_ack_nak(self, data: bytes) -> Dict[str, Any]:
        """Parse ACK/NAK DLLP format"""
        if len(data) < 6:
            raise ValueError("ACK/NAK DLLP must be at least 6 bytes")
            
        first_byte = data[0]
        ack_nak_seq_num = struct.unpack('>H', data[1:3])[0] >> 4  # 12-bit field
        crc = struct.unpack('>H', data[4:6])[0]
        
        return {
            'type': 'ACK' if first_byte == 0x00 else 'NAK',
            'ack_nak_seq_num': ack_nak_seq_num,
            'reserved': data[3],
            'crc': crc,
            'crc_valid': self._verify_crc(data)
        }
        
    def _parse_nop(self, data: bytes) -> Dict[str, Any]:
        """Parse NOP DLLP format"""
        if len(data) < 6:
            raise ValueError("NOP DLLP must be at least 6 bytes")
            
        first_byte = data[0]
        arbitrary_value = struct.unpack('>I', b'\x00' + data[1:4])[0]  # 24-bit field
        crc = struct.unpack('>H', data[4:6])[0]
        
        return {
            'type': 'NOP',
            'pattern': f"0x{first_byte:02X}",
            'arbitrary_value': arbitrary_value,
            'crc': crc,
            'crc_valid': self._verify_crc(data)
        }
        
    def _parse_flow_control(self, data: bytes, fc_type: str) -> Dict[str, Any]:
        """Parse Flow Control DLLP formats (InitFC1, InitFC2, UpdateFC)"""
        if len(data) < 6:
            raise ValueError(f"{fc_type} DLLP must be at least 6 bytes")
            
        first_byte = data[0]
        
        # For InitFC1, VC ID is encoded in lower 4 bits of first byte
        if fc_type == "InitFC1":
            vc_id = self._extract_bits(first_byte, 0, 4)  # Lower 4 bits of 0100xxxx
            # Extract FC type from bits [2:1] of second byte
            fc_info = data[1]
            fc_scale_type = self._extract_bits(fc_info, 1, 2)
        else:
            # For InitFC2 and UpdateFC, VC ID is in bits [2:0] of second byte
            fc_info = data[1]
            fc_scale_type = self._extract_bits(fc_info, 1, 2)
            vc_id = self._extract_bits(fc_info, 0, 3)
        
        # Header and Data credits parsing
        if fc_type == "InitFC1":
            hdr_scale = self._extract_bits(data[1], 6, 2)
            hdr_fc = data[2]
            data_scale = self._extract_bits(data[2], 6, 2)
            data_fc = data[3]
        elif fc_type == "InitFC2":
            hdr_scale = self._extract_bits(data[1], 4, 2)
            hdr_fc = data[2]
            data_scale = self._extract_bits(data[3], 6, 2)
            data_fc = data[3] & 0x3F  # Lower 6 bits
        else:  # UpdateFC
            hdr_scale = self._extract_bits(data[1], 4, 2)
            hdr_fc = struct.unpack('>H', data[2:4])[0] >> 8
            data_scale = self._extract_bits(data[3], 6, 2)
            data_fc = data[3] & 0x3F  # Lower 6 bits
        
        crc = struct.unpack('>H', data[4:6])[0]
        
        result = {
            'type': fc_type,
            'vc_channel': vc_id,
            'fc_type': self.fc_types.get(fc_scale_type, f"Reserved({fc_scale_type})"),
            'hdr_scale': hdr_scale,
            'hdr_fc': hdr_fc,
            'data_scale': data_scale, 
            'data_fc': data_fc,
            'crc': crc,
            'crc_valid': self._verify_crc(data)
        }
        
        return result
        
    def _parse_pm(self, data: bytes) -> Dict[str, Any]:
        """Parse Power Management DLLP format"""
        if len(data) < 6:
            raise ValueError("PM DLLP must be at least 6 bytes")
            
        first_byte = data[0]
        pm_type = self._extract_bits(first_byte, 0, 3)
        
        # Reserved field spans bytes 1-3
        reserved = struct.unpack('>I', b'\x00' + data[1:4])[0]
        crc = struct.unpack('>H', data[4:6])[0]
        
        return {
            'type': 'PM',
            'pm_type': pm_type, 
            'pattern': f"0x{first_byte:02X}",
            'reserved': reserved,
            'crc': crc,
            'crc_valid': self._verify_crc(data)
        }
        
    def _parse_vendor_specific(self, data: bytes) -> Dict[str, Any]:
        """Parse Vendor-specific DLLP format"""
        if len(data) < 6:
            raise ValueError("Vendor-specific DLLP must be at least 6 bytes")
            
        first_byte = data[0]
        vendor_data = struct.unpack('>I', b'\x00' + data[1:4])[0]  # 24-bit field
        crc = struct.unpack('>H', data[4:6])[0]
        
        return {
            'type': 'Vendor-specific',
            'pattern': f"0x{first_byte:02X}",
            'vendor_defined': vendor_data,
            'crc': crc,
            'crc_valid': self._verify_crc(data)
        }
        
    def _parse_feature_dllp(self, data: bytes) -> Dict[str, Any]:
        """Parse Data Link Feature DLLP format"""
        if len(data) < 6:
            raise ValueError("Feature DLLP must be at least 6 bytes")
            
        first_byte = data[0]
        feature_support = struct.unpack('>I', b'\x00' + data[1:4])[0]  # 24-bit field
        crc = struct.unpack('>H', data[4:6])[0]
        
        return {
            'type': 'Feature DLLP',
            'pattern': f"0x{first_byte:02X}",
            'feature_support': feature_support,
            'crc': crc,
            'crc_valid': self._verify_crc(data)
        }
        
    def _verify_crc(self, data: bytes) -> bool:
        """Verify CRC-16 of DLLP"""
        if len(data) < 6:
            return False
        payload = data[:-2]
        received_crc = struct.unpack('>H', data[-2:])[0]
        calculated_crc = self._calculate_crc16(payload)
        return received_crc == calculated_crc
        
    def parse(self, data: Union[bytes, str]) -> Dict[str, Any]:
        """
        Parse a DLLP from raw bytes or hex string
        
        Args:
            data: Raw bytes or hex string representation of DLLP
            
        Returns:
            Dictionary containing parsed DLLP information
        """
        # Convert hex string to bytes if necessary
        if isinstance(data, str):
            # Remove spaces and convert hex string to bytes
            hex_str = data.replace(' ', '').replace('0x', '')
            if len(hex_str) % 2 != 0:
                raise ValueError("Invalid hex string length")
            data = bytes.fromhex(hex_str)
            
        if len(data) < 6:
            raise ValueError("DLLP must be at least 6 bytes long")
            
        # Determine DLLP type from first byte
        dllp_type = self._determine_dllp_type(data[0])
        
        # Parse based on type
        if dllp_type in [DLLPType.ACK, DLLPType.NAK]:
            return self._parse_ack_nak(data)
        elif dllp_type == DLLPType.NOP:
            return self._parse_nop(data)
        elif dllp_type == DLLPType.INIT_FC1:
            return self._parse_flow_control(data, "InitFC1")
        elif dllp_type == DLLPType.INIT_FC2:
            return self._parse_flow_control(data, "InitFC2")
        elif dllp_type == DLLPType.UPDATE_FC:
            return self._parse_flow_control(data, "UpdateFC")
        elif dllp_type == DLLPType.PM:
            return self._parse_pm(data)
        elif dllp_type == DLLPType.VENDOR_SPECIFIC:
            return self._parse_vendor_specific(data)
        elif dllp_type == DLLPType.FEATURE_DLLP:
            return self._parse_feature_dllp(data)
        else:
            raise ValueError(f"Unsupported DLLP type: {dllp_type}")
            
    def format_output(self, parsed_data: Dict[str, Any]) -> str:
        """Format parsed DLLP data for display"""
        output = [f"DLLP Type: {parsed_data['type']}"]
        
        for key, value in parsed_data.items():
            if key != 'type':
                if isinstance(value, int) and key not in ['vc_channel', 'vc_id', 'pm_type']:
                    output.append(f"{key}: 0x{value:04X} ({value})")
                else:
                    output.append(f"{key}: {value}")
                    
        return '\n'.join(output)


# Example usage and test cases
if __name__ == "__main__":
    parser = PCIeDLLPParser()
    
    # Test cases for different DLLP types
    test_cases = [
        # ACK DLLP
        ("00 12 34 00 AB CD", "ACK DLLP"),
        # NAK DLLP  
        ("10 56 78 00 EF 01", "NAK DLLP"),
        # NOP DLLP
        ("31 12 34 56 78 9A", "NOP DLLP"),
        # InitFC1 DLLP (0x42 = 0100 0010 -> VC channel 2)
        ("42 02 08 10 BC DE", "InitFC1 DLLP - VC2"),
        # InitFC1 DLLP (0x47 = 0100 0111 -> VC channel 7)  
        ("47 02 08 10 BC DE", "InitFC1 DLLP - VC7"),
        # InitFC2 DLLP
        ("50 02 08 10 BC DE", "InitFC2 DLLP"),
        # UpdateFC DLLP
        ("60 02 08 10 BC DE", "UpdateFC DLLP"),
        # PM DLLP
        ("23 00 00 00 12 34", "PM DLLP"),
        # Vendor-specific DLLP
        ("30 AB CD EF 56 78", "Vendor-specific DLLP"),
        # Feature DLLP
        ("02 00 01 00 9A BC", "Feature DLLP")
    ]
    
    print("PCIe DLLP Parser Test Results:")
    print("=" * 50)
    
    for hex_data, description in test_cases:
        try:
            print(f"\nTesting {description}")
            print(f"Input: {hex_data}")
            result = parser.parse(hex_data)
            print(parser.format_output(result))
        except Exception as e:
            print(f"Error parsing {description}: {e}")
        print("-" * 30)