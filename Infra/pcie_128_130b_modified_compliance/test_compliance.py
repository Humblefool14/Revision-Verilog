"""
Test suite for Modified PCIe 128b/130b Compliance Pattern Parser
"""

import unittest
from modified_compliance_parser import (
    ModifiedCompliancePattern,
    ModifiedCompliancePatternParser,
    SRISMode
)


class TestModifiedCompliancePattern(unittest.TestCase):
    """Test cases for ModifiedCompliancePattern generator"""
    
    def test_non_sris_pattern_length(self):
        """Test non-SRIS pattern has correct number of blocks"""
        generator = ModifiedCompliancePattern(SRISMode.NON_SRIS)
        pattern = generator.generate_full_pattern(num_iterations=1)
        
        # Expected: 1 + 256 + 255*(1 + 256) = 65792 blocks
        expected = 1 + 256 + 255 * (1 + 256)
        self.assertEqual(len(pattern), expected)
        self.assertEqual(len(pattern), 65792)
    
    def test_sris_pattern_length(self):
        """Test SRIS pattern has correct number of blocks"""
        generator = ModifiedCompliancePattern(SRISMode.SRIS)
        pattern = generator.generate_full_pattern(num_iterations=1)
        
        # Expected: 1 + 2048*(1 + 32) = 67585 blocks
        expected = 1 + 2048 * (1 + 32)
        self.assertEqual(len(pattern), expected)
        self.assertEqual(len(pattern), 67585)
    
    def test_non_sris_structure_first_blocks(self):
        """Test non-SRIS pattern has correct initial structure"""
        generator = ModifiedCompliancePattern(SRISMode.NON_SRIS)
        pattern = generator.generate_full_pattern(num_iterations=1)
        
        # Block 1 should be EIEOSQ
        self.assertEqual(pattern[0][1], generator.generate_eieosq_block())
        
        # Blocks 2-257 should be data blocks
        for i in range(1, 257):
            self.assertEqual(pattern[i][1], b'\x00' * 16)
    
    def test_sris_structure_first_blocks(self):
        """Test SRIS pattern has correct initial structure"""
        generator = ModifiedCompliancePattern(SRISMode.SRIS)
        pattern = generator.generate_full_pattern(num_iterations=1)
        
        # Block 1 should be EIEOSQ
        self.assertEqual(pattern[0][1], generator.generate_eieosq_block())
        
        # Block 2 should be SKP
        self.assertEqual(pattern[1][1], generator.generate_skp_ordered_set())
        
        # Blocks 3-34 should be data blocks (32 total)
        for i in range(2, 34):
            self.assertEqual(pattern[i][1], b'\x00' * 16)
    
    def test_non_sris_skp_pattern(self):
        """Test non-SRIS SKP/Data set pattern"""
        generator = ModifiedCompliancePattern(SRISMode.NON_SRIS)
        pattern = generator.generate_full_pattern(num_iterations=1)
        
        # After initial EIEOSQ + 256 data, should have 255 sets of (SKP + 256 data)
        # Check first SKP/Data set (starts at block 258, index 257)
        skp_index = 257
        self.assertEqual(pattern[skp_index][1], generator.generate_skp_ordered_set())
        
        # Next 256 should be data blocks
        for i in range(skp_index + 1, skp_index + 257):
            self.assertEqual(pattern[i][1], b'\x00' * 16)
    
    def test_sris_skp_pattern(self):
        """Test SRIS SKP/Data set pattern"""
        generator = ModifiedCompliancePattern(SRISMode.SRIS)
        pattern = generator.generate_full_pattern(num_iterations=1)
        
        # Pattern: EIEOSQ + 2048 sets of (SKP + 32 data)
        # Check first few sets
        for set_num in range(5):  # Check first 5 sets
            base_index = 1 + set_num * 33  # 1 for EIEOSQ, 33 per set
            
            # Should be SKP
            self.assertEqual(pattern[base_index][1], generator.generate_skp_ordered_set())
            
            # Next 32 should be data
            for i in range(base_index + 1, base_index + 33):
                self.assertEqual(pattern[i][1], b'\x00' * 16)
    
    def test_sync_headers(self):
        """Test all blocks have correct sync header"""
        for mode in [SRISMode.NON_SRIS, SRISMode.SRIS]:
            generator = ModifiedCompliancePattern(mode)
            # Only generate first 1000 blocks for speed
            pattern = generator.generate_full_pattern(num_iterations=1)[:1000]
            
            for sync, _ in pattern:
                self.assertEqual(sync, 0b01)
    
    def test_payload_sizes(self):
        """Test all payloads are 16 bytes"""
        for mode in [SRISMode.NON_SRIS, SRISMode.SRIS]:
            generator = ModifiedCompliancePattern(mode)
            # Only generate first 1000 blocks for speed
            pattern = generator.generate_full_pattern(num_iterations=1)[:1000]
            
            for _, payload in pattern:
                self.assertEqual(len(payload), 16)
    
    def test_pattern_info_non_sris(self):
        """Test pattern info for non-SRIS mode"""
        generator = ModifiedCompliancePattern(SRISMode.NON_SRIS)
        info = generator.get_pattern_info()
        
        self.assertEqual(info['mode'], 'non-SRIS')
        self.assertEqual(info['total_blocks'], 65792)
        self.assertEqual(info['structure']['eieosq_blocks'], 1)
        self.assertEqual(info['structure']['initial_data_blocks'], 256)
        self.assertEqual(info['structure']['skp_data_sets'], 255)
        self.assertEqual(info['structure']['data_blocks_per_set'], 256)
    
    def test_pattern_info_sris(self):
        """Test pattern info for SRIS mode"""
        generator = ModifiedCompliancePattern(SRISMode.SRIS)
        info = generator.get_pattern_info()
        
        self.assertEqual(info['mode'], 'SRIS')
        self.assertEqual(info['total_blocks'], 67585)
        self.assertEqual(info['structure']['eieosq_blocks'], 1)
        self.assertEqual(info['structure']['skp_data_sets'], 2048)
        self.assertEqual(info['structure']['data_blocks_per_set'], 32)
    
    def test_multiple_iterations(self):
        """Test multiple pattern iterations"""
        generator = ModifiedCompliancePattern(SRISMode.NON_SRIS)
        pattern = generator.generate_full_pattern(num_iterations=2)
        
        # Should be 2x the base pattern
        expected = 65792 * 2
        self.assertEqual(len(pattern), expected)


class TestModifiedCompliancePatternParser(unittest.TestCase):
    """Test cases for ModifiedCompliancePatternParser"""
    
    def test_identify_data_block(self):
        """Test identification of data blocks"""
        parser = ModifiedCompliancePatternParser()
        data_payload = b'\x00' * 16
        
        block_type = parser.identify_block_type(data_payload)
        self.assertEqual(block_type, "Data Block: Idle symbols")
    
    def test_identify_skp_block(self):
        """Test identification of SKP blocks"""
        parser = ModifiedCompliancePatternParser()
        skp_payload = b'\xAA' * 16
        
        block_type = parser.identify_block_type(skp_payload)
        self.assertEqual(block_type, "SKP Ordered Set")
    
    def test_detect_non_sris_mode(self):
        """Test detection of non-SRIS mode"""
        generator = ModifiedCompliancePattern(SRISMode.NON_SRIS)
        pattern = generator.generate_full_pattern(num_iterations=1)
        
        # Convert to block dictionaries
        blocks = []
        for i, (sync, payload) in enumerate(pattern[:500]):  # First 500 blocks
            blocks.append({'payload': payload, 'sync_header': sync})
        
        parser = ModifiedCompliancePatternParser()
        detected_mode = parser.detect_pattern_mode(blocks)
        
        self.assertEqual(detected_mode, SRISMode.NON_SRIS)
    
    def test_detect_sris_mode(self):
        """Test detection of SRIS mode"""
        generator = ModifiedCompliancePattern(SRISMode.SRIS)
        pattern = generator.generate_full_pattern(num_iterations=1)
        
        # Convert to block dictionaries
        blocks = []
        for i, (sync, payload) in enumerate(pattern[:500]):  # First 500 blocks
            blocks.append({'payload': payload, 'sync_header': sync})
        
        parser = ModifiedCompliancePatternParser()
        detected_mode = parser.detect_pattern_mode(blocks)
        
        self.assertEqual(detected_mode, SRISMode.SRIS)
    
    def test_analyze_pattern_structure_non_sris(self):
        """Test pattern structure analysis for non-SRIS"""
        generator = ModifiedCompliancePattern(SRISMode.NON_SRIS)
        pattern = generator.generate_full_pattern(num_iterations=1)
        
        # Convert to block dictionaries
        blocks = []
        parser = ModifiedCompliancePatternParser()
        for i, (sync, payload) in enumerate(pattern[:1000]):  # First 1000 blocks
            blocks.append({
                'payload': payload,
                'sync_header': sync,
                'block_type': parser.identify_block_type(payload)
            })
        
        analysis = parser.analyze_pattern_structure(blocks)
        
        self.assertEqual(analysis['total_blocks'], 1000)
        self.assertEqual(analysis['detected_mode'], SRISMode.NON_SRIS)
        self.assertIn('Data Block: Idle symbols', analysis['block_type_counts'])
    
    def test_analyze_pattern_structure_sris(self):
        """Test pattern structure analysis for SRIS"""
        generator = ModifiedCompliancePattern(SRISMode.SRIS)
        pattern = generator.generate_full_pattern(num_iterations=1)
        
        # Convert to block dictionaries
        blocks = []
        parser = ModifiedCompliancePatternParser()
        for i, (sync, payload) in enumerate(pattern[:1000]):  # First 1000 blocks
            blocks.append({
                'payload': payload,
                'sync_header': sync,
                'block_type': parser.identify_block_type(payload)
            })
        
        analysis = parser.analyze_pattern_structure(blocks)
        
        self.assertEqual(analysis['total_blocks'], 1000)
        self.assertEqual(analysis['detected_mode'], SRISMode.SRIS)
        self.assertIn('SKP Ordered Set', analysis['block_type_counts'])


class TestPatternCalculations(unittest.TestCase):
    """Test pattern size calculations"""
    
    def test_non_sris_calculation(self):
        """Verify non-SRIS calculation matches formula"""
        # 1 + 256 + 255*(1 + 256) = 65792
        eieosq = 1
        initial_data = 256
        num_sets = 255
        blocks_per_set = 1 + 256
        
        total = eieosq + initial_data + (num_sets * blocks_per_set)
        
        self.assertEqual(total, 65792)
        
        # Alternative calculation
        alt_calc = 1 + 256 + 255 * 257
        self.assertEqual(alt_calc, 65792)
    
    def test_sris_calculation(self):
        """Verify SRIS calculation matches formula"""
        # 1 + 2048*(1 + 32) = 67585
        eieosq = 1
        num_sets = 2048
        blocks_per_set = 1 + 32
        
        total = eieosq + (num_sets * blocks_per_set)
        
        self.assertEqual(total, 67585)
        
        # Alternative calculation
        alt_calc = 1 + 2048 * 33
        self.assertEqual(alt_calc, 67585)
    
    def test_pattern_size_difference(self):
        """Test the difference between SRIS and non-SRIS patterns"""
        non_sris_size = 65792
        sris_size = 67585
        
        difference = sris_size - non_sris_size
        self.assertEqual(difference, 1793)


class TestIntegration(unittest.TestCase):
    """Integration tests"""
    
    def test_generate_and_validate_non_sris(self):
        """Generate non-SRIS pattern and validate structure"""
        generator = ModifiedCompliancePattern(SRISMode.NON_SRIS)
        pattern = generator.generate_full_pattern(num_iterations=1)
        
        # Validate total length
        self.assertEqual(len(pattern), 65792)
        
        # Validate first block is EIEOSQ
        self.assertEqual(pattern[0][1], generator.generate_eieosq_block())
        
        # Validate initial 256 data blocks
        for i in range(1, 257):
            self.assertEqual(pattern[i][1], b'\x00' * 16)
        
        # Validate pattern has SKP blocks
        skp_count = sum(1 for _, payload in pattern 
                       if payload == generator.generate_skp_ordered_set())
        self.assertEqual(skp_count, 255)
    
    def test_generate_and_validate_sris(self):
        """Generate SRIS pattern and validate structure"""
        generator = ModifiedCompliancePattern(SRISMode.SRIS)
        pattern = generator.generate_full_pattern(num_iterations=1)
        
        # Validate total length
        self.assertEqual(len(pattern), 67585)
        
        # Validate first block is EIEOSQ
        self.assertEqual(pattern[0][1], generator.generate_eieosq_block())
        
        # Validate pattern has SKP blocks
        skp_count = sum(1 for _, payload in pattern 
                       if payload == generator.generate_skp_ordered_set())
        self.assertEqual(skp_count, 2048)


def run_tests():
    """Run all tests and display results"""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestModifiedCompliancePattern))
    suite.addTests(loader.loadTestsFromTestCase(TestModifiedCompliancePatternParser))
    suite.addTests(loader.loadTestsFromTestCase(TestPatternCalculations))
    suite.addTests(loader.loadTestsFromTestCase(TestIntegration))
    
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
