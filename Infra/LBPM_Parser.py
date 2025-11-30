#!/usr/bin/env python3
"""
LBPM (Link Block Protocol Message) Parser
USB PHY specification decoder
"""

class LBPMParser:
    def __init__(self, lbpm_binary):
        """
        Initialize parser with 8-bit binary string
        
        Args:
            lbpm_binary (str): 8-bit binary string (e.g., '00000100')
        """
        self.raw = lbpm_binary.replace(' ', '').replace('_', '')
        self.validate()
        self.bits = self.extract_bits()
        
    def validate(self):
        """Validate LBPM format"""
        if len(self.raw) != 8:
            raise ValueError(f"LBPM must be exactly 8 bits, got {len(self.raw)}")
        
        if not all(c in '01' for c in self.raw):
            raise ValueError("LBPM must contain only 0s and 1s")
    
    def extract_bits(self):
        """Extract individual bits"""
        return {f'b{i}': int(self.raw[i]) for i in range(8)}
    
    def get_type(self):
        """Parse LBPM Type [b1:b0]"""
        type_value = (self.bits['b1'] << 1) | self.bits['b0']
        
        types = {
            0b00: 'PHY Capability',
            0b01: 'PHY Ready',
            0b10: 'Reserved',
            0b11: 'Reserved'
        }
        
        return types[type_value], type_value
    
    def parse_phy_capability(self):
        """Parse PHY Capability message (Type = 00)"""
        result = {}
        
        # Speed [b3:b2]
        speed_value = (self.bits['b3'] << 1) | self.bits['b2']
        speeds = {
            0b00: '5 Gbps',
            0b01: '10 Gbps',
            0b10: 'Reserved',
            0b11: 'Reserved'
        }
        result['speed'] = speeds[speed_value]
        result['speed_raw'] = f"{speed_value:02b}"
        
        # Reserved b4
        result['reserved_b4'] = 'Valid' if self.bits['b4'] == 0 else 'Invalid (should be 0)'
        
        # Lane Configuration [b6]
        result['lane_config'] = 'Single-lane' if self.bits['b6'] == 0 else 'Dual-lane'
        
        # Reserved b5, b7
        result['reserved_b5'] = 'Valid' if self.bits['b5'] == 0 else 'Invalid (should be 0)'
        result['reserved_b7'] = 'Valid' if self.bits['b7'] == 0 else 'Invalid (should be 0)'
        
        return result
    
    def parse_phy_ready(self):
        """Parse PHY Ready message (Type = 01)"""
        result = {}
        
        # Re-timer information [b4:b2]
        retimer_value = (self.bits['b4'] << 2) | (self.bits['b3'] << 1) | self.bits['b2']
        
        if retimer_value == 0:
            result['retimer'] = 'No re-timers'
        else:
            result['retimer'] = f'{retimer_value} re-timer(s) at index {retimer_value}'
        result['retimer_raw'] = f"{retimer_value:03b}"
        
        # Port Type [b5]
        result['port_type'] = 'UFP' if self.bits['b5'] == 0 else 'DFP'
        
        # x2 Operation Status [b7]
        if self.bits['b5'] == 1:  # DFP
            result['x2_status'] = 'Config Done. DFP ready to exit' if self.bits['b7'] == 0 else 'RT Config. DFP to address re-timers'
        else:  # UFP
            result['x2_status'] = 'Reserved (0)' if self.bits['b7'] == 0 else 'Invalid for UFP'
        
        # Subtype [b7:b2]
        subtype = (self.bits['b7'] << 5) | (self.bits['b6'] << 4) | (self.bits['b5'] << 3) | \
                  (self.bits['b4'] << 2) | (self.bits['b3'] << 1) | self.bits['b2']
        result['subtype'] = f"0x{subtype:02X}" if subtype != 0 else "Reserved (single-lane)"
        result['subtype_raw'] = f"{subtype:06b}"
        
        # b6 analysis
        result['b6_note'] = 'Reserved (0)' if self.bits['b6'] == 0 else 'Reserved (1)'
        
        return result
    
    def parse(self):
        """Parse the LBPM message"""
        lbpm_type, type_value = self.get_type()
        
        result = {
            'raw': self.raw,
            'hex': f"0x{int(self.raw, 2):02X}",
            'decimal': int(self.raw, 2),
            'bits': self.bits,
            'type': lbpm_type,
            'type_value': f"{type_value:02b}"
        }
        
        if lbpm_type == 'PHY Capability':
            result['details'] = self.parse_phy_capability()
        elif lbpm_type == 'PHY Ready':
            result['details'] = self.parse_phy_ready()
        else:
            result['details'] = {'note': 'Reserved LBPM type'}
        
        return result
    
    def __str__(self):
        """Pretty print the parsed LBPM"""
        parsed = self.parse()
        
        output = []
        output.append("=" * 60)
        output.append("LBPM PARSER RESULTS")
        output.append("=" * 60)
        output.append(f"Raw Binary:  {parsed['raw']}")
        output.append(f"Hexadecimal: {parsed['hex']}")
        output.append(f"Decimal:     {parsed['decimal']}")
        output.append("")
        
        # Bit breakdown
        output.append("Bit Breakdown:")
        bits_display = " | ".join([f"{k}:{v}" for k, v in parsed['bits'].items()])
        output.append(f"  {bits_display}")
        output.append("")
        
        # Type
        output.append(f"LBPM Type [b1:b0]: {parsed['type']} ({parsed['type_value']})")
        output.append("")
        
        # Details
        if 'details' in parsed and parsed['details']:
            output.append("Details:")
            output.append("-" * 60)
            
            if parsed['type'] == 'PHY Capability':
                details = parsed['details']
                output.append(f"  Speed [b3:b2]:           {details['speed']} ({details['speed_raw']})")
                output.append(f"  Lane Config [b6]:        {details['lane_config']}")
                output.append(f"  Reserved b4:             {details['reserved_b4']}")
                output.append(f"  Reserved b5:             {details['reserved_b5']}")
                output.append(f"  Reserved b7:             {details['reserved_b7']}")
                
            elif parsed['type'] == 'PHY Ready':
                details = parsed['details']
                output.append(f"  Re-timer [b4:b2]:        {details['retimer']} ({details['retimer_raw']})")
                output.append(f"  Port Type [b5]:          {details['port_type']}")
                output.append(f"  x2 Status [b7]:          {details['x2_status']}")
                output.append(f"  Subtype [b7:b2]:         {details['subtype']} ({details['subtype_raw']})")
                output.append(f"  b6 Status:               {details['b6_note']}")
        
        output.append("=" * 60)
        return "\n".join(output)


def main():
    """Example usage and test cases"""
    print("LBPM Parser - USB PHY Specification\n")
    
    # Test cases from the specification
    test_cases = [
        ('00000100', 'PHY Capability: 10 Gbps, single-lane'),
        ('00000001', 'PHY Capability: 10 Gbps'),
        ('00000000', 'PHY Capability: 5 Gbps, single-lane'),
        ('01000000', 'PHY Ready: No re-timers, UFP'),
        ('01000001', 'PHY Ready: 1 re-timer'),
        ('00000101', 'PHY Capability: 10 Gbps, dual-lane'),
    ]
    
    for lbpm_binary, description in test_cases:
        print(f"\nTest: {description}")
        print(f"Input: {lbpm_binary}")
        print("-" * 60)
        try:
            parser = LBPMParser(lbpm_binary)
            print(parser)
        except ValueError as e:
            print(f"ERROR: {e}")
        print()
    
    # Interactive mode
    print("\n" + "=" * 60)
    print("Interactive Mode")
    print("=" * 60)
    print("Enter an 8-bit LBPM binary string (or 'quit' to exit)")
    
    while True:
        try:
            user_input = input("\nLBPM> ").strip()
            
            if user_input.lower() in ['quit', 'exit', 'q']:
                print("Goodbye!")
                break
            
            if not user_input:
                continue
            
            parser = LBPMParser(user_input)
            print(parser)
            
        except ValueError as e:
            print(f"ERROR: {e}")
        except KeyboardInterrupt:
            print("\nGoodbye!")
            break
        except EOFError:
            break


if __name__ == "__main__":
    main()
