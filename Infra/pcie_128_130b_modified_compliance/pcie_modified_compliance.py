"""
PCIe 128b/130b Modified Compliance Pattern Parser

This module parses and generates modified PCIe compliance patterns according to the
128b/130b encoding specification for both non-SRIS and SRIS modes.
"""

from typing import List, Tuple, Dict
from enum import Enum


class SRISMode(Enum):
    """Operating mode for modified compliance pattern"""
    NON_SRIS = "non-SRIS"
    SRIS = "SRIS"


class ModifiedCompliancePattern:
    """Generates modified PCIe 128b/130b compliance patterns"""
    
    SYNC_HEADER = 0b01  # 2-bit sync header
    
    def __init__(self, sris_mode: SRISMode = SRISMode.NON_SRIS):
        """
        Initialize modified compliance pattern generator
        
        Args:
            sris_mode: Operating mode (NON_SRIS or SRIS)
        """
        self.sris_mode = sris_mode
    
    def generate_eieosq_block(self) -> bytes:
        """
        Generate EIEOSQ (Electrical Idle Exit Ordered Set Qualifier) block
        
        Returns:
            128-bit (16 bytes) unscrambled payload
        """
        # EIEOSQ pattern - placeholder implementation
        # Actual pattern depends on detailed specification
        return b'\x00' * 16
    
    def generate_data_block(self) -> bytes:
        """
        Generate data block with 16 Idle data Symbols (00h)
        
        Returns:
            128-bit (16 bytes) payload (to be scrambled)
        """
        # 16 Idle data symbols of 00h
        return b'\x00' * 16
    
    def generate_skp_ordered_set(self) -> bytes:
        """
        Generate SKP Ordered Set block
        
        Returns:
            128-bit (16 bytes) payload
        """
        # SKP Ordered Set pattern - placeholder implementation
        # Actual pattern depends on detailed specification
        # Typically contains SKP symbols for clock compensation
        return b'\xAA' * 16  # Placeholder
    
    def generate_non_sris_pattern(self) -> List[Tuple[int, bytes]]:
        """
        Generate complete modified compliance pattern for non-SRIS mode
        
        Pattern structure (65792 or 65793 blocks):
        1. One EIEOSQ block
        2. 256 Data blocks
        3. 255 sets of:
            i.  One SKP Ordered Set
            ii. 256 Data blocks
        
        Total: 1 + 256 + 255*(1 + 256) = 1 + 256 + 255*257 = 1 + 256 + 65535 = 65792 blocks
        
        Returns:
            List of tuples (sync_header, payload_bytes) for each block
        """
        pattern = []
        
        # Block 1: EIEOSQ
        pattern.append((self.SYNC_HEADER, self.generate_eieosq_block()))
        
        # Block 2-257: 256 Data blocks
        for _ in range(256):
            pattern.append((self.SYNC_HEADER, self.generate_data_block()))
        
        # Blocks 258-65792: 255 sets of (SKP + 256 Data blocks)
        for _ in range(255):
            # One SKP Ordered Set
            pattern.append((self.SYNC_HEADER, self.generate_skp_ordered_set()))
            
            # 256 Data blocks
            for _ in range(256):
                pattern.append((self.SYNC_HEADER, self.generate_data_block()))
        
        return pattern
    
    def generate_sris_pattern(self) -> List[Tuple[int, bytes]]:
        """
        Generate complete modified compliance pattern for SRIS mode
        
        Pattern structure (67585 or 67586 blocks):
        1. One EIEOSQ block
        2. 2048 sets of:
            i.  One SKP Ordered Set
            ii. 32 Data blocks
        
        Total: 1 + 2048*(1 + 32) = 1 + 2048*33 = 1 + 67584 = 67585 blocks
        
        Returns:
            List of tuples (sync_header, payload_bytes) for each block
        """
        pattern = []
        
        # Block 1: EIEOSQ
        pattern.append((self.SYNC_HEADER, self.generate_eieosq_block()))
        
        # Blocks 2-67585: 2048 sets of (SKP + 32 Data blocks)
        for _ in range(2048):
            # One SKP Ordered Set
            pattern.append((self.SYNC_HEADER, self.generate_skp_ordered_set()))
            
            # 32 Data blocks
            for _ in range(32):
                pattern.append((self.SYNC_HEADER, self.generate_data_block()))
        
        return pattern
    
    def generate_full_pattern(self, num_iterations: int = 1) -> List[Tuple[int, bytes]]:
        """
        Generate complete modified compliance pattern based on SRIS mode
        
        Args:
            num_iterations: Number of times to repeat the pattern
            
        Returns:
            List of tuples (sync_header, payload_bytes) for each block
        """
        pattern = []
        
        for _ in range(num_iterations):
            if self.sris_mode == SRISMode.NON_SRIS:
                pattern.extend(self.generate_non_sris_pattern())
            else:  # SRIS mode
                pattern.extend(self.generate_sris_pattern())
        
        return pattern
    
    def get_pattern_info(self) -> Dict:
        """
        Get information about the pattern structure
        
        Returns:
            Dictionary with pattern information
        """
        if self.sris_mode == SRISMode.NON_SRIS:
            return {
                'mode': 'non-SRIS',
                'total_blocks': 65792,
                'structure': {
                    'eieosq_blocks': 1,
                    'initial_data_blocks': 256,
                    'skp_data_sets': 255,
                    'data_blocks_per_set': 256,
                    'skp_blocks_per_set': 1
                },
                'calculation': '1 + 256 + 255*(1 + 256) = 65792'
            }
        else:  # SRIS mode
            return {
                'mode': 'SRIS',
                'total_blocks': 67585,
                'structure': {
                    'eieosq_blocks': 1,
                    'skp_data_sets': 2048,
                    'data_blocks_per_set': 32,
                    'skp_blocks_per_set': 1
                },
                'calculation': '1 + 2048*(1 + 32) = 67585'
            }


class ModifiedCompliancePatternParser:
    """Parser for received modified PCIe compliance patterns"""
    
    def __init__(self):
        self.blocks = []
        self.detected_mode = None
    
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
        Identify the type of modified compliance pattern block
        
        Args:
            payload: 16-byte payload
            
        Returns:
            String identifying block type
        """
        # Check for all zeros (Idle data symbols)
        if payload == b'\x00' * 16:
            return "Data Block: Idle symbols"
        
        # Check for SKP pattern (placeholder - 0xAA pattern)
        if payload == b'\xAA' * 16:
            return "SKP Ordered Set"
        
        # Check for potential EIEOSQ or other patterns
        unique_bytes = set(payload)
        if len(unique_bytes) <= 2:
            return "EIEOSQ or Special pattern"
        
        return "Unknown block type"
    
    def detect_pattern_mode(self, blocks: List[Dict]) -> SRISMode:
        """
        Detect whether pattern is non-SRIS or SRIS mode based on structure
        
        Args:
            blocks: List of parsed block dictionaries
            
        Returns:
            Detected SRIS mode
        """
        if len(blocks) < 300:
            return None
        
        # Count consecutive data blocks after first non-data block
        data_count = 0
        skp_found = False
        
        for i, block in enumerate(blocks[1:], start=1):  # Skip first EIEOSQ
            block_type = self.identify_block_type(block['payload'])
            
            if block_type == "Data Block: Idle symbols":
                if not skp_found:
                    data_count += 1
            elif "SKP" in block_type:
                skp_found = True
                break
        
        # Non-SRIS: 256 data blocks before first SKP
        # SRIS: Pattern starts with SKP + 32 data blocks
        if data_count >= 250:  # Close to 256
            return SRISMode.NON_SRIS
        elif data_count <= 40:  # Close to 32
            return SRISMode.SRIS
        
        return None
    
    def parse_stream(self, data: bytes, max_blocks: int = None) -> List[Dict]:
        """
        Parse a stream of modified compliance pattern blocks
        
        Args:
            data: Raw byte stream
            max_blocks: Maximum number of blocks to parse (None = all)
            
        Returns:
            List of parsed block dictionaries
        """
        blocks = []
        block_size = 17  # 130 bits = 16.25 bytes, rounded up
        
        num_blocks = len(data) // block_size
        if max_blocks:
            num_blocks = min(num_blocks, max_blocks)
        
        for i in range(num_blocks):
            offset = i * block_size
            if offset + block_size <= len(data):
                block_data = data[offset:offset + block_size]
                parsed = self.parse_block(block_data)
                parsed['block_type'] = self.identify_block_type(parsed['payload'])
                parsed['block_number'] = i
                blocks.append(parsed)
        
        return blocks
    
    def analyze_pattern_structure(self, blocks: List[Dict]) -> Dict:
        """
        Analyze the structure of a parsed pattern
        
        Args:
            blocks: List of parsed block dictionaries
            
        Returns:
            Dictionary with pattern analysis
        """
        analysis = {
            'total_blocks': len(blocks),
            'block_type_counts': {},
            'detected_mode': None,
            'structure_valid': False
        }
        
        # Count block types
        for block in blocks:
            block_type = block['block_type']
            analysis['block_type_counts'][block_type] = \
                analysis['block_type_counts'].get(block_type, 0) + 1
        
        # Detect mode
        analysis['detected_mode'] = self.detect_pattern_mode(blocks)
        
        # Validate structure
        if analysis['detected_mode']:
            expected_info = ModifiedCompliancePattern(analysis['detected_mode']).get_pattern_info()
            analysis['expected_blocks'] = expected_info['total_blocks']
            analysis['structure_info'] = expected_info
        
        return analysis


def calculate_pattern_sizes():
    """Calculate and display pattern sizes for both modes"""
    print("=" * 70)
    print("Modified Compliance Pattern Size Calculations")
    print("=" * 70)
    
    # Non-SRIS calculation
    print("\nNon-SRIS Mode:")
    print("-" * 50)
    non_sris_eieosq = 1
    non_sris_initial_data = 256
    non_sris_sets = 255
    non_sris_blocks_per_set = 1 + 256  # SKP + data blocks
    
    non_sris_total = non_sris_eieosq + non_sris_initial_data + \
                     (non_sris_sets * non_sris_blocks_per_set)
    
    print(f"  EIEOSQ blocks:              {non_sris_eieosq}")
    print(f"  Initial data blocks:        {non_sris_initial_data}")
    print(f"  Number of SKP/Data sets:    {non_sris_sets}")
    print(f"  Blocks per set (SKP+Data):  {non_sris_blocks_per_set}")
    print(f"  Calculation: 1 + 256 + 255*(1 + 256)")
    print(f"             = 1 + 256 + 255*257")
    print(f"             = 1 + 256 + {non_sris_sets * non_sris_blocks_per_set}")
    print(f"  Total blocks:               {non_sris_total}")
    
    # SRIS calculation
    print("\nSRIS Mode:")
    print("-" * 50)
    sris_eieosq = 1
    sris_sets = 2048
    sris_blocks_per_set = 1 + 32  # SKP + data blocks
    
    sris_total = sris_eieosq + (sris_sets * sris_blocks_per_set)
    
    print(f"  EIEOSQ blocks:              {sris_eieosq}")
    print(f"  Number of SKP/Data sets:    {sris_sets}")
    print(f"  Blocks per set (SKP+Data):  {sris_blocks_per_set}")
    print(f"  Calculation: 1 + 2048*(1 + 32)")
    print(f"             = 1 + 2048*33")
    print(f"             = 1 + {sris_sets * sris_blocks_per_set}")
    print(f"  Total blocks:               {sris_total}")
    
    print("\n" + "=" * 70)


def main():
    """Example usage of the modified compliance pattern generator and parser"""
    
    print("PCIe 128b/130b Modified Compliance Pattern Generator")
    print("=" * 70)
    
    # Display pattern size calculations
    calculate_pattern_sizes()
    
    # Generate non-SRIS pattern info
    print("\n\nPattern Generation Examples:")
    print("=" * 70)
    
    print("\n1. Non-SRIS Mode Pattern:")
    print("-" * 50)
    non_sris_gen = ModifiedCompliancePattern(SRISMode.NON_SRIS)
    non_sris_info = non_sris_gen.get_pattern_info()
    
    print(f"Mode: {non_sris_info['mode']}")
    print(f"Total blocks: {non_sris_info['total_blocks']:,}")
    print(f"Calculation: {non_sris_info['calculation']}")
    print("\nStructure:")
    for key, value in non_sris_info['structure'].items():
        print(f"  {key}: {value}")
    
    # Generate SRIS pattern info
    print("\n2. SRIS Mode Pattern:")
    print("-" * 50)
    sris_gen = ModifiedCompliancePattern(SRISMode.SRIS)
    sris_info = sris_gen.get_pattern_info()
    
    print(f"Mode: {sris_info['mode']}")
    print(f"Total blocks: {sris_info['total_blocks']:,}")
    print(f"Calculation: {sris_info['calculation']}")
    print("\nStructure:")
    for key, value in sris_info['structure'].items():
        print(f"  {key}: {value}")
    
    # Demonstrate pattern generation (first few blocks only)
    print("\n3. Sample Pattern Generation (first 10 blocks):")
    print("-" * 50)
    
    for mode in [SRISMode.NON_SRIS, SRISMode.SRIS]:
        generator = ModifiedCompliancePattern(mode)
        pattern = generator.generate_full_pattern(num_iterations=1)
        
        print(f"\n{mode.value} mode - First 10 blocks:")
        for i in range(min(10, len(pattern))):
            sync, payload = pattern[i]
            block_type = "Unknown"
            
            if i == 0:
                block_type = "EIEOSQ"
            elif payload == b'\x00' * 16:
                block_type = "Data (Idle)"
            elif payload == b'\xAA' * 16:
                block_type = "SKP Ordered Set"
            
            print(f"  Block {i+1:5d}: {payload[:8].hex():16s}... [{block_type}]")
    
    # Demonstrate parser
    print("\n4. Pattern Parser Example:")
    print("-" * 50)
    
    parser = ModifiedCompliancePatternParser()
    
    # Create sample pattern and analyze
    sample_gen = ModifiedCompliancePattern(SRISMode.NON_SRIS)
    sample_pattern = sample_gen.generate_full_pattern(num_iterations=1)
    
    # Analyze first 500 blocks
    print(f"\nAnalyzing pattern (first 500 blocks)...")
    
    block_counts = {
        'EIEOSQ': 0,
        'Data': 0,
        'SKP': 0
    }
    
    for i, (sync, payload) in enumerate(sample_pattern[:500]):
        if i == 0:
            block_counts['EIEOSQ'] += 1
        elif payload == b'\x00' * 16:
            block_counts['Data'] += 1
        elif payload == b'\xAA' * 16:
            block_counts['SKP'] += 1
    
    print(f"\nBlock type distribution (first 500 blocks):")
    for block_type, count in block_counts.items():
        print(f"  {block_type}: {count}")
    
    print("\n" + "=" * 70)
    print(f"Total pattern size for non-SRIS: {len(sample_pattern):,} blocks")
    print("=" * 70)


if __name__ == "__main__":
    main()
