"""
PCIe 128b/130b Compliance Pattern Parser

This module parses and generates PCIe compliance patterns according to the
128b/130b encoding specification.
"""

from typing import List, Tuple, Dict
import struct


class CompliancePattern:
    """Represents a PCIe 128b/130b compliance pattern"""
    
    SYNC_HEADER = 0b01  # 2-bit sync header
    
    # Symbol definitions for different blocks
    BLOCK2_SYMBOLS = [
        [0x55, 0xFF, 0xFF, 0xFF, 0x55, 0xFF, 0xFF, 0xFF],  # Symbol 0
        [0x55, 0xFF, 0xFF, 0xFF, 0x55, 0xFF, 0xFF, 0xFF],  # Symbol 1
        [0x55, 0x00, 0xFF, 0xFF, 0x55, 0xFF, 0xFF, 0xFF],  # Symbol 2
        [0x55, 0x00, 0xFF, 0xFF, 0x55, 0xFF, 0xF0, 0xF0],  # Symbol 3
        [0x55, 0x00, 0xFF, 0xC0, 0x55, 0xFF, 0x00, 0x00],  # Symbol 4
        [0x55, 0x00, 0xC0, 0x00, 0x55, 0xE0, 0x00, 0x00],  # Symbol 5
        [0x55, 0x00, 0x00, 0x00, 0x55, 0x00, 0x00, 0x00],  # Symbol 6
        [None, None, None, None, None, None, None, None],  # Symbol 7 - {P,~P}
        [0x00, 0x1E, 0x2D, 0x3C, 0x4B, 0x5A, 0x69, 0x78],  # Symbol 8
        [0x00, 0x55, 0x00, 0x00, 0x00, 0x55, 0x00, 0xF0],  # Symbol 9
        [0x00, 0x55, 0x00, 0x00, 0x00, 0x55, 0x00, 0x00],  # Symbol 10
        [0x00, 0x55, 0x00, 0x00, 0x00, 0x55, 0x00, 0x00],  # Symbol 11
        [0x00, 0x55, 0x0F, 0x0F, 0x00, 0x55, 0x07, 0x00],  # Symbol 12
        [0x00, 0x55, 0xFF, 0xFF, 0x00, 0x55, 0xFF, 0x00],  # Symbol 13
        [0x00, 0x55, 0xFF, 0xFF, 0x7F, 0x55, 0xFF, 0x00],  # Symbol 14
        [0x00, 0x55, 0xFF, 0xFF, 0xFF, 0x55, 0xFF, 0x00],  # Symbol 15
    ]
    
    BLOCK3_SYMBOLS = [
        [0xFF, 0xFF, 0x55, 0xFF, 0xFF, 0xFF, 0x55, 0xFF],  # Symbol 0
        [0xFF, 0xFF, 0x55, 0xFF, 0xFF, 0xFF, 0x55, 0xFF],  # Symbol 1
        [0xFF, 0xFF, 0x55, 0xFF, 0xFF, 0xFF, 0x55, 0xFF],  # Symbol 2
        [0xF0, 0xF0, 0x55, 0xF0, 0xF0, 0xF0, 0x55, 0xF0],  # Symbol 3
        [0x00, 0x00, 0x55, 0x00, 0x00, 0x00, 0x55, 0x00],  # Symbol 4
        [0x00, 0x00, 0x55, 0x00, 0x00, 0x00, 0x55, 0x00],  # Symbol 5
        [0x00, 0x00, 0x55, 0x00, 0x00, 0x00, 0x55, 0x00],  # Symbol 6
        [None, None, None, None, None, None, None, None],  # Symbol 7 - {P,~P}
        [0x00, 0x1E, 0x2D, 0x3C, 0x4B, 0x5A, 0x69, 0x78],  # Symbol 8
        [0x00, 0x00, 0x00, 0x55, 0x00, 0x00, 0x00, 0x55],  # Symbol 9
        [0x00, 0x00, 0x00, 0x55, 0x00, 0x00, 0x00, 0x55],  # Symbol 10
        [0x00, 0x00, 0x00, 0x55, 0x00, 0x00, 0x00, 0x55],  # Symbol 11
        [0xFF, 0x0F, 0x0F, 0x55, 0x0F, 0x0F, 0x0F, 0x55],  # Symbol 12
        [0xFF, 0xFF, 0xFF, 0x55, 0xFF, 0xFF, 0xFF, 0x55],  # Symbol 13
        [0xFF, 0xFF, 0xFF, 0x55, 0xFF, 0xFF, 0xFF, 0x55],  # Symbol 14
        [0xFF, 0xFF, 0xFF, 0x55, 0xFF, 0xFF, 0xFF, 0x55],  # Symbol 15
    ]
    
    def __init__(self, preset: int = 0):
        """
        Initialize compliance pattern generator
        
        Args:
            preset: 4-bit transmitter preset value (0-15)
        """
        self.preset = preset & 0xF
        self.preset_inv = (~preset) & 0xF
        
    def _generate_preset_byte(self, lane: int) -> int:
        """Generate P or ~P byte based on lane number"""
        # For symbol 7, alternate between P and ~P based on lane
        if lane % 2 == 0:
            # Even lanes get preset nibbles
            return (self.preset << 4) | self.preset
        else:
            # Odd lanes get inverted preset nibbles
            return (self.preset_inv << 4) | self.preset_inv
    
    def generate_block1(self) -> bytes:
        """
        Generate Block 1: Sync header + 64 ones followed by 64 zeros
        
        Returns:
            128-bit (16 bytes) unscrambled payload
        """
        # 64 ones (8 bytes of 0xFF) followed by 64 zeros (8 bytes of 0x00)
        return b'\xFF' * 8 + b'\x00' * 8
    
    def generate_block2(self, lane: int) -> bytes:
        """
        Generate Block 2 payload for a specific lane
        
        Args:
            lane: Lane number (0-7 for modulo 8)
            
        Returns:
            128-bit (16 bytes) unscrambled payload
        """
        payload = bytearray()
        lane_mod = lane % 8
        
        for symbol in self.BLOCK2_SYMBOLS:
            if symbol[lane_mod] is None:
                # Symbol 7 - use preset pattern
                payload.append(self._generate_preset_byte(lane))
            else:
                payload.append(symbol[lane_mod])
                
        return bytes(payload)
    
    def generate_block3(self, lane: int) -> bytes:
        """
        Generate Block 3 payload for a specific lane
        
        Args:
            lane: Lane number (0-7 for modulo 8)
            
        Returns:
            128-bit (16 bytes) unscrambled payload
        """
        payload = bytearray()
        lane_mod = lane % 8
        
        for symbol in self.BLOCK3_SYMBOLS:
            if symbol[lane_mod] is None:
                # Symbol 7 - use preset pattern
                payload.append(self._generate_preset_byte(lane))
            else:
                payload.append(symbol[lane_mod])
                
        return bytes(payload)
    
    def generate_eieosq_block(self) -> bytes:
        """
        Generate EIEOSQ block (placeholder - actual implementation depends on spec)
        
        Returns:
            128-bit (16 bytes) unscrambled payload
        """
        # EIEOSQ pattern - this is a placeholder
        # Actual pattern depends on detailed specification
        return b'\x00' * 16
    
    def generate_data_block(self) -> bytes:
        """
        Generate data block with 16 IDL symbols (00h) scrambled
        
        Returns:
            128-bit (16 bytes) payload (to be scrambled)
        """
        # 16 IDL symbols of 00h
        return b'\x00' * 16
    
    def generate_full_pattern(self, lane: int, num_iterations: int = 1) -> List[Tuple[int, bytes]]:
        """
        Generate complete compliance pattern for a specific lane
        
        Args:
            lane: Lane number
            num_iterations: Number of times to repeat the pattern
            
        Returns:
            List of tuples (sync_header, payload_bytes) for each block
        """
        pattern = []
        
        for _ in range(num_iterations):
            # Block 1: All ones followed by all zeros
            pattern.append((self.SYNC_HEADER, self.generate_block1()))
            
            # Block 2
            pattern.append((self.SYNC_HEADER, self.generate_block2(lane)))
            
            # Block 3
            pattern.append((self.SYNC_HEADER, self.generate_block3(lane)))
            
            # Block 4: EIEOSQ
            pattern.append((self.SYNC_HEADER, self.generate_eieosq_block()))
            
            # Blocks 5-36: 32 Data blocks with IDL symbols
            for _ in range(32):
                pattern.append((self.SYNC_HEADER, self.generate_data_block()))
        
        return pattern


class CompliancePatternParser:
    """Parser for received PCIe compliance patterns"""
    
    def __init__(self):
        self.blocks = []
        
    def parse_block(self, data: bytes) -> Dict:
        """
        Parse a single 130-bit block (2-bit sync + 128-bit payload)
        
        Args:
            data: 17 bytes (130 bits) of received data
            
        Returns:
            Dictionary with sync header and payload information
        """
        if len(data) < 17:
            raise ValueError("Block data must be at least 17 bytes (130 bits)")
        
        # Extract sync header (first 2 bits)
        sync_header = (data[0] >> 6) & 0b11
        
        # Extract payload (remaining 128 bits)
        # Shift first byte and combine with remaining bytes
        payload = bytearray()
        payload.append((data[0] << 2) & 0xFF | (data[1] >> 6) & 0x3)
        
        for i in range(1, 16):
            payload.append(((data[i] << 2) & 0xFF) | ((data[i+1] >> 6) & 0x3))
        
        payload.append((data[16] << 2) & 0xFF)
        
        return {
            'sync_header': sync_header,
            'payload': bytes(payload[:16]),  # 128 bits = 16 bytes
            'raw': data
        }
    
    def identify_block_type(self, payload: bytes) -> str:
        """
        Identify the type of compliance pattern block
        
        Args:
            payload: 16-byte payload
            
        Returns:
            String identifying block type
        """
        # Check for Block 1 pattern (64 ones followed by 64 zeros)
        if payload == b'\xFF' * 8 + b'\x00' * 8:
            return "Block 1: All ones/zeros"
        
        # Check for all zeros (likely data block with IDL)
        if payload == b'\x00' * 16:
            return "Data Block: IDL symbols"
        
        # Block 2/3 patterns have characteristic features:
        # 1. Contains 0x55, 0x77, or 0x88 bytes (common in pattern tables)
        # 2. Has mix of 0xFF and 0x00 bytes
        # 3. Not all same value
        
        unique_bytes = set(payload)
        
        # Check for characteristic pattern bytes
        pattern_markers = {0x55, 0x77, 0x88, 0xC0, 0xF0, 0xE0}
        if pattern_markers & unique_bytes:
            return "Block 2/3: Pattern block"
        
        # If we have significant 0xFF count and some 0x00, likely a pattern block
        ff_count = payload.count(0xFF)
        zero_count = payload.count(0x00)
        
        if ff_count >= 3 and zero_count >= 2 and len(unique_bytes) >= 3:
            return "Block 2/3: Pattern block"
        
        return "Unknown/EIEOSQ"
    
    def parse_stream(self, data: bytes, num_blocks: int) -> List[Dict]:
        """
        Parse a stream of compliance pattern blocks
        
        Args:
            data: Raw byte stream
            num_blocks: Number of blocks to parse
            
        Returns:
            List of parsed block dictionaries
        """
        blocks = []
        block_size = 17  # 130 bits = 16.25 bytes, rounded up
        
        for i in range(num_blocks):
            offset = i * block_size
            if offset + block_size <= len(data):
                block_data = data[offset:offset + block_size]
                parsed = self.parse_block(block_data)
                parsed['block_type'] = self.identify_block_type(parsed['payload'])
                parsed['block_number'] = i
                blocks.append(parsed)
        
        return blocks
    
    def extract_preset(self, block2_payload: bytes, lane: int) -> int:
        """
        Extract preset value from Block 2 Symbol 7
        
        Args:
            block2_payload: Block 2 payload bytes
            lane: Lane number
            
        Returns:
            4-bit preset value
        """
        # Symbol 7 is at byte 7
        symbol7 = block2_payload[7]
        
        # Extract preset based on lane (even lanes have P, odd have ~P)
        if lane % 2 == 0:
            preset = (symbol7 >> 4) & 0xF
        else:
            preset = ~((symbol7 >> 4) & 0xF) & 0xF
            
        return preset


def main():
    """Example usage of the compliance pattern generator and parser"""
    
    print("PCIe 128b/130b Compliance Pattern Generator\n")
    print("=" * 60)
    
    # Generate pattern for lane 0 with preset 5
    preset = 5
    lane = 0
    
    print(f"\nGenerating compliance pattern for:")
    print(f"  Lane: {lane}")
    print(f"  Preset: {preset} (0x{preset:X})")
    print(f"  Preset inverse: {(~preset) & 0xF} (0x{(~preset) & 0xF:X})")
    
    generator = CompliancePattern(preset=preset)
    pattern = generator.generate_full_pattern(lane, num_iterations=1)
    
    print(f"\nGenerated {len(pattern)} blocks (36-37 blocks per pattern)")
    print("\nFirst few blocks:")
    
    for i, (sync, payload) in enumerate(pattern[:5]):
        print(f"\nBlock {i+1}:")
        print(f"  Sync Header: 0b{sync:02b}")
        print(f"  Payload: {payload.hex()}")
        
        if i == 0:
            print(f"  Type: All ones followed by zeros")
        elif i == 1:
            print(f"  Type: Block 2 pattern")
        elif i == 2:
            print(f"  Type: Block 3 pattern")
        elif i == 3:
            print(f"  Type: EIEOSQ")
        else:
            print(f"  Type: Data block (IDL)")
    
    # Demonstrate parser
    print("\n" + "=" * 60)
    print("\nParser Example:")
    parser = CompliancePatternParser()
    
    # Create a test block (Block 1)
    test_sync = 0b01
    test_payload = b'\xFF' * 8 + b'\x00' * 8
    
    # Pack into 130 bits (17 bytes for simplicity)
    test_data = bytearray()
    test_data.append((test_sync << 6) | ((test_payload[0] >> 2) & 0x3F))
    for i in range(15):
        test_data.append(((test_payload[i] << 6) & 0xFF) | ((test_payload[i+1] >> 2) & 0x3F))
    test_data.append((test_payload[15] << 6) & 0xFF)
    
    parsed = parser.parse_block(bytes(test_data))
    print(f"\nParsed block:")
    print(f"  Sync Header: 0b{parsed['sync_header']:02b}")
    print(f"  Block Type: {parser.identify_block_type(parsed['payload'])}")
    print(f"  Payload: {parsed['payload'].hex()}")


if __name__ == "__main__":
    main()
