"""
Test suite for PCIe 128b/130b Compliance Pattern Parser
"""

import unittest
from pcie_compliance_parser import CompliancePattern, CompliancePatternParser


class TestCompliancePattern(unittest.TestCase):
    """Test cases for CompliancePattern generator"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.generator = CompliancePattern(preset=5)
    
    def test_block1_generation(self):
        """Test Block 1 generation (all ones followed by all zeros)"""
        block1 = self.generator.generate_block1()
        
        # Should be 16 bytes total
        self.assertEqual(len(block1), 16)
        
        # First 8 bytes should be 0xFF
        self.assertEqual(block1[:8], b'\xFF' * 8)
        
        # Last 8 bytes should be 0x00
        self.assertEqual(block1[8:], b'\x00' * 8)
    
    def test_block2_generation_lane0(self):
        """Test Block 2 generation for lane 0"""
        block2 = self.generator.generate_block2(0)
        
        # Should be 16 bytes (16 symbols)
        self.assertEqual(len(block2), 16)
        
        # Check first symbol (should be 0x55 for lane 0)
        self.assertEqual(block2[0], 0x55)
        
        # Check symbol 8 (should be 0x00 for lane 0)
        self.assertEqual(block2[8], 0x00)
    
    def test_block2_generation_lane1(self):
        """Test Block 2 generation for lane 1"""
        block2 = self.generator.generate_block2(1)
        
        # Should be 16 bytes (16 symbols)
        self.assertEqual(len(block2), 16)
        
        # Check first symbol (should be 0xFF for lane 1)
        self.assertEqual(block2[0], 0xFF)
        
        # Check symbol 8 (should be 0x1E for lane 1)
        self.assertEqual(block2[8], 0x1E)
    
    def test_block3_generation_lane0(self):
        """Test Block 3 generation for lane 0"""
        block3 = self.generator.generate_block3(0)
        
        # Should be 16 bytes (16 symbols)
        self.assertEqual(len(block3), 16)
        
        # Check first symbol (should be 0xFF for lane 0)
        self.assertEqual(block3[0], 0xFF)
    
    def test_preset_byte_generation(self):
        """Test preset byte generation for symbol 7"""
        # Lane 0 (even) should get preset in both nibbles
        preset_byte_even = self.generator._generate_preset_byte(0)
        self.assertEqual(preset_byte_even, 0x55)  # preset=5, so 0x55
        
        # Lane 1 (odd) should get inverted preset
        preset_byte_odd = self.generator._generate_preset_byte(1)
        self.assertEqual(preset_byte_odd, 0xAA)  # ~5=10 (0xA), so 0xAA
    
    def test_data_block_generation(self):
        """Test data block generation (IDL symbols)"""
        data_block = self.generator.generate_data_block()
        
        # Should be 16 bytes of zeros
        self.assertEqual(data_block, b'\x00' * 16)
    
    def test_full_pattern_length(self):
        """Test full pattern generation produces correct number of blocks"""
        pattern = self.generator.generate_full_pattern(0, num_iterations=1)
        
        # Should have 36 blocks (1 + 1 + 1 + 1 + 32)
        self.assertEqual(len(pattern), 36)
    
    def test_full_pattern_structure(self):
        """Test full pattern has correct structure"""
        pattern = self.generator.generate_full_pattern(0, num_iterations=1)
        
        # Block 1 should be all ones/zeros
        self.assertEqual(pattern[0][1], b'\xFF' * 8 + b'\x00' * 8)
        
        # Blocks 5-36 should be data blocks (all zeros)
        for i in range(4, 36):
            self.assertEqual(pattern[i][1], b'\x00' * 16)
    
    def test_multiple_iterations(self):
        """Test multiple pattern iterations"""
        pattern = self.generator.generate_full_pattern(0, num_iterations=2)
        
        # Should have 72 blocks (36 * 2)
        self.assertEqual(len(pattern), 72)
    
    def test_lane_modulo_8(self):
        """Test that lane numbers work with modulo 8"""
        # Lane 8 should behave same as lane 0
        block2_lane0 = self.generator.generate_block2(0)
        block2_lane8 = self.generator.generate_block2(8)
        
        self.assertEqual(block2_lane0, block2_lane8)


class TestCompliancePatternParser(unittest.TestCase):
    """Test cases for CompliancePatternParser"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.parser = CompliancePatternParser()
    
    def test_identify_block1(self):
        """Test Block 1 identification"""
        block1_payload = b'\xFF' * 8 + b'\x00' * 8
        block_type = self.parser.identify_block_type(block1_payload)
        
        self.assertEqual(block_type, "Block 1: All ones/zeros")
    
    def test_identify_data_block(self):
        """Test data block identification"""
        data_payload = b'\x00' * 16
        block_type = self.parser.identify_block_type(data_payload)
        
        self.assertEqual(block_type, "Data Block: IDL symbols")
    
    def test_identify_pattern_block(self):
        """Test Block 2/3 identification"""
        # Create a typical Block 2 pattern
        pattern_payload = bytes([0x55, 0xFF, 0xFF, 0xFF, 0x55, 0xFF, 0xFF, 0xFF,
                                0x00, 0x55, 0x00, 0x00, 0x00, 0x55, 0x00, 0x00])
        block_type = self.parser.identify_block_type(pattern_payload)
        
        self.assertEqual(block_type, "Block 2/3: Pattern block")
    
    def test_extract_preset_even_lane(self):
        """Test preset extraction from even lane"""
        # Create Block 2 with preset=5 for lane 0
        generator = CompliancePattern(preset=5)
        block2 = generator.generate_block2(0)
        
        extracted_preset = self.parser.extract_preset(block2, 0)
        self.assertEqual(extracted_preset, 5)
    
    def test_extract_preset_odd_lane(self):
        """Test preset extraction from odd lane"""
        # Create Block 2 with preset=5 for lane 1
        generator = CompliancePattern(preset=5)
        block2 = generator.generate_block2(1)
        
        extracted_preset = self.parser.extract_preset(block2, 1)
        self.assertEqual(extracted_preset, 5)


class TestIntegration(unittest.TestCase):
    """Integration tests"""
    
    def test_generate_and_parse_roundtrip(self):
        """Test generating pattern and parsing it back"""
        preset = 7
        lane = 3
        
        # Generate pattern
        generator = CompliancePattern(preset=preset)
        pattern = generator.generate_full_pattern(lane, num_iterations=1)
        
        # Verify structure
        self.assertEqual(len(pattern), 36)
        
        # Verify Block 1
        parser = CompliancePatternParser()
        block1_type = parser.identify_block_type(pattern[0][1])
        self.assertEqual(block1_type, "Block 1: All ones/zeros")
        
        # Verify Block 2
        block2_type = parser.identify_block_type(pattern[1][1])
        self.assertEqual(block2_type, "Block 2/3: Pattern block")
        
        # Extract and verify preset
        extracted = parser.extract_preset(pattern[1][1], lane)
        self.assertEqual(extracted, preset)
    
    def test_all_lanes(self):
        """Test pattern generation for all 8 lanes"""
        generator = CompliancePattern(preset=3)
        
        for lane in range(8):
            pattern = generator.generate_full_pattern(lane, num_iterations=1)
            self.assertEqual(len(pattern), 36)
            
            # Each lane should have valid blocks
            for sync, payload in pattern:
                self.assertEqual(sync, 0b01)
                self.assertEqual(len(payload), 16)


class TestEdgeCases(unittest.TestCase):
    """Test edge cases and boundary conditions"""
    
    def test_preset_boundary_values(self):
        """Test with minimum and maximum preset values"""
        # Test preset = 0
        gen0 = CompliancePattern(preset=0)
        block2_0 = gen0.generate_block2(0)
        self.assertEqual(len(block2_0), 16)
        
        # Test preset = 15
        gen15 = CompliancePattern(preset=15)
        block2_15 = gen15.generate_block2(0)
        self.assertEqual(len(block2_15), 16)
    
    def test_preset_overflow(self):
        """Test that preset values > 15 are masked"""
        gen = CompliancePattern(preset=0xFF)
        # Should be masked to 4 bits (0xF)
        self.assertEqual(gen.preset, 0xF)
    
    def test_lane_numbers(self):
        """Test various lane numbers including high values"""
        generator = CompliancePattern(preset=5)
        
        # Test lane 0
        block0 = generator.generate_block2(0)
        
        # Test lane 100 (should behave like lane 4 due to modulo 8)
        block100 = generator.generate_block2(100)
        block4 = generator.generate_block2(4)
        
        self.assertEqual(block100, block4)


def run_tests():
    """Run all tests and display results"""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestCompliancePattern))
    suite.addTests(loader.loadTestsFromTestCase(TestCompliancePatternParser))
    suite.addTests(loader.loadTestsFromTestCase(TestIntegration))
    suite.addTests(loader.loadTestsFromTestCase(TestEdgeCases))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Print summary
    print("\n" + "=" * 70)
    print("TEST SUMMARY")
    print("=" * 70)
    print(f"Tests run: {result.testsRun}")
    print(f"Successes: {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"Failures: {len(result.failures)}")
    print(f"Errors: {len(result.errors)}")
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_tests()
    exit(0 if success else 1)
