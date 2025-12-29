"""
Advanced Examples for PCIe 128b/130b Compliance Pattern Parser

Demonstrates various use cases and features of the parser library.
"""

from pcie_compliance_parser import CompliancePattern, CompliancePatternParser


def example_1_basic_generation():
    """Example 1: Basic pattern generation"""
    print("=" * 70)
    print("EXAMPLE 1: Basic Pattern Generation")
    print("=" * 70)
    
    # Create generator with preset 3
    generator = CompliancePattern(preset=3)
    
    # Generate pattern for lane 0
    pattern = generator.generate_full_pattern(lane=0, num_iterations=1)
    
    print(f"\nGenerated {len(pattern)} blocks for lane 0 with preset 3")
    print("\nBlock summary:")
    
    for i, (sync, payload) in enumerate(pattern[:10]):  # Show first 10
        block_type = "Unknown"
        if i == 0:
            block_type = "Block 1 (ones/zeros)"
        elif i == 1:
            block_type = "Block 2 (pattern)"
        elif i == 2:
            block_type = "Block 3 (pattern)"
        elif i == 3:
            block_type = "EIEOSQ"
        else:
            block_type = "Data (IDL)"
        
        print(f"  Block {i+1:2d}: {payload[:8].hex():16s}... [{block_type}]")


def example_2_all_lanes():
    """Example 2: Generate patterns for all lanes"""
    print("\n" + "=" * 70)
    print("EXAMPLE 2: Pattern Generation for All Lanes")
    print("=" * 70)
    
    generator = CompliancePattern(preset=7)
    
    print("\nBlock 2 patterns for each lane (first 8 bytes shown):")
    print(f"{'Lane':<6} {'Block 2 Pattern (hex)'}")
    print("-" * 40)
    
    for lane in range(8):
        block2 = generator.generate_block2(lane)
        print(f"{lane:<6} {block2[:8].hex()}")
    
    print("\nNote: Patterns repeat for lanes 8+, using modulo 8")


def example_3_preset_encoding():
    """Example 3: Demonstrate preset encoding in Symbol 7"""
    print("\n" + "=" * 70)
    print("EXAMPLE 3: Preset Encoding in Symbol 7")
    print("=" * 70)
    
    for preset in [0, 5, 10, 15]:
        generator = CompliancePattern(preset=preset)
        
        print(f"\nPreset {preset} (0x{preset:X}):")
        print(f"  Inverse: {(~preset) & 0xF} (0x{(~preset) & 0xF:X})")
        
        # Show Symbol 7 encoding for even and odd lanes
        block2_lane0 = generator.generate_block2(0)
        block2_lane1 = generator.generate_block2(1)
        
        symbol7_lane0 = block2_lane0[7]
        symbol7_lane1 = block2_lane1[7]
        
        print(f"  Lane 0 (even) Symbol 7: 0x{symbol7_lane0:02X}")
        print(f"  Lane 1 (odd)  Symbol 7: 0x{symbol7_lane1:02X}")


def example_4_parsing():
    """Example 4: Parse generated patterns"""
    print("\n" + "=" * 70)
    print("EXAMPLE 4: Pattern Parsing")
    print("=" * 70)
    
    # Generate a pattern
    preset = 6
    lane = 2
    generator = CompliancePattern(preset=preset)
    pattern = generator.generate_full_pattern(lane, num_iterations=1)
    
    # Parse the patterns
    parser = CompliancePatternParser()
    
    print(f"\nParsing pattern for lane {lane}, preset {preset}:")
    
    block_types = []
    for i, (sync, payload) in enumerate(pattern[:8]):
        block_type = parser.identify_block_type(payload)
        block_types.append(block_type)
        print(f"  Block {i+1}: {block_type}")
    
    # Extract preset from Block 2
    extracted_preset = parser.extract_preset(pattern[1][1], lane)
    print(f"\nExtracted preset from Block 2: {extracted_preset}")
    print(f"Original preset: {preset}")
    print(f"Match: {'✓' if extracted_preset == preset else '✗'}")


def example_5_pattern_comparison():
    """Example 5: Compare patterns across lanes"""
    print("\n" + "=" * 70)
    print("EXAMPLE 5: Pattern Comparison Across Lanes")
    print("=" * 70)
    
    generator = CompliancePattern(preset=4)
    
    # Generate Block 2 for multiple lanes
    lanes = [0, 1, 4, 5]
    blocks = {}
    
    for lane in lanes:
        blocks[lane] = generator.generate_block2(lane)
    
    print("\nComparing Block 2 patterns:")
    print(f"{'Symbol':<8}", end='')
    for lane in lanes:
        print(f"Lane {lane:<3}", end='  ')
    print()
    print("-" * 50)
    
    for symbol_idx in range(16):
        print(f"Sym {symbol_idx:<2}  ", end='')
        for lane in lanes:
            byte_val = blocks[lane][symbol_idx]
            print(f"  {byte_val:02X}   ", end='  ')
        print()


def example_6_multipattern_generation():
    """Example 6: Generate multiple pattern iterations"""
    print("\n" + "=" * 70)
    print("EXAMPLE 6: Multiple Pattern Iterations")
    print("=" * 70)
    
    generator = CompliancePattern(preset=8)
    
    # Generate 3 iterations
    pattern = generator.generate_full_pattern(lane=0, num_iterations=3)
    
    print(f"\nGenerated {len(pattern)} blocks (3 iterations)")
    print(f"Expected: {36 * 3} blocks")
    
    # Verify pattern repeats correctly
    print("\nVerifying pattern repetition:")
    iteration_size = 36
    
    for iteration in range(3):
        start_idx = iteration * iteration_size
        block1 = pattern[start_idx][1]
        is_block1 = (block1 == b'\xFF' * 8 + b'\x00' * 8)
        print(f"  Iteration {iteration + 1}: Block 1 correct: {'✓' if is_block1 else '✗'}")


def example_7_validation():
    """Example 7: Validate generated patterns"""
    print("\n" + "=" * 70)
    print("EXAMPLE 7: Pattern Validation")
    print("=" * 70)
    
    generator = CompliancePattern(preset=9)
    pattern = generator.generate_full_pattern(lane=3, num_iterations=1)
    parser = CompliancePatternParser()
    
    print("\nValidation checks:")
    
    # Check 1: Correct number of blocks
    check1 = len(pattern) == 36
    print(f"  ✓ Total blocks = 36: {check1}")
    
    # Check 2: Block 1 format
    check2 = pattern[0][1] == b'\xFF' * 8 + b'\x00' * 8
    print(f"  ✓ Block 1 format correct: {check2}")
    
    # Check 3: Sync headers
    check3 = all(sync == 0b01 for sync, _ in pattern)
    print(f"  ✓ All sync headers = 01b: {check3}")
    
    # Check 4: Payload sizes
    check4 = all(len(payload) == 16 for _, payload in pattern)
    print(f"  ✓ All payloads = 16 bytes: {check4}")
    
    # Check 5: Data blocks are all zeros
    check5 = all(pattern[i][1] == b'\x00' * 16 for i in range(4, 36))
    print(f"  ✓ Data blocks all zeros: {check5}")
    
    # Check 6: Preset extraction
    extracted = parser.extract_preset(pattern[1][1], 3)
    check6 = extracted == 9
    print(f"  ✓ Preset extraction correct: {check6} (got {extracted})")
    
    all_passed = all([check1, check2, check3, check4, check5, check6])
    print(f"\nOverall: {'All checks passed ✓' if all_passed else 'Some checks failed ✗'}")


def example_8_lane_independence():
    """Example 8: Demonstrate lane independence"""
    print("\n" + "=" * 70)
    print("EXAMPLE 8: Lane Independence")
    print("=" * 70)
    
    preset = 11
    generator = CompliancePattern(preset=preset)
    
    print(f"\nGenerating patterns with preset {preset}:")
    print("\nEach lane can have its own independent pattern")
    print("while sharing the same preset value.\n")
    
    print(f"{'Lane':<6} {'Block 2 Unique Bytes':<25} {'Block 3 Unique Bytes'}")
    print("-" * 60)
    
    for lane in range(8):
        block2 = generator.generate_block2(lane)
        block3 = generator.generate_block3(lane)
        
        unique2 = len(set(block2))
        unique3 = len(set(block3))
        
        print(f"{lane:<6} {unique2:<25} {unique3}")
    
    print("\nNote: Different unique byte counts indicate different patterns per lane")


def main():
    """Run all examples"""
    examples = [
        example_1_basic_generation,
        example_2_all_lanes,
        example_3_preset_encoding,
        example_4_parsing,
        example_5_pattern_comparison,
        example_6_multipattern_generation,
        example_7_validation,
        example_8_lane_independence,
    ]
    
    print("\n" + "=" * 70)
    print("PCIe 128b/130b Compliance Pattern - Advanced Examples")
    print("=" * 70)
    
    for example_func in examples:
        example_func()
    
    print("\n" + "=" * 70)
    print("All examples completed!")
    print("=" * 70)


if __name__ == "__main__":
    main()
