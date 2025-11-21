#!/usr/bin/env python3
"""
Gen 2 SKP Ordered Set Parser
Parses USB Gen 2 SKP (Skip) Ordered Sets according to Table 6-13
"""

class SKPOrderedSet:
    """Represents a Gen 2 SKP Ordered Set"""
    
    SKPEND_SYMBOL = 0x33
    
    def __init__(self, symbols):
        """
        Initialize SKP Ordered Set from a list of symbols
        
        Args:
            symbols: List of symbol values (bytes or integers)
        """
        if len(symbols) < 4:
            raise ValueError(f"SKP Ordered Set must have at least 4 symbols, got {len(symbols)}")
        
        # N can be 0-9, so total symbols = 4*N + 4
        if (len(symbols) - 4) % 4 != 0:
            raise ValueError(f"Invalid symbol count: {len(symbols)}. Must be 4*N+4 where N is 0-9")
        
        self.n = (len(symbols) - 4) // 4
        if self.n > 9:
            raise ValueError(f"N value {self.n} exceeds maximum of 9")
        
        self.symbols = symbols
        self._validate()
    
    def _validate(self):
        """Validate the ordered set structure"""
        # Check SKP symbols (0 through 4*N-1)
        skp_count = 4 * self.n
        for i in range(skp_count):
            if self.symbols[i] != 0xCC:
                raise ValueError(f"Symbol {i} should be SKP (0xCC), got 0x{self.symbols[i]:02X}")
        
        # Check SKPEND symbol at position 4*N
        if self.symbols[skp_count] != self.SKPEND_SYMBOL:
            raise ValueError(f"Symbol {skp_count} should be SKPEND (0x33), got 0x{self.symbols[skp_count]:02X}")
        
        # Symbols 4*N+1, 4*N+2, 4*N+3 contain LFSR data (validated in decoding)
    
    @classmethod
    def from_bytes(cls, data):
        """
        Create SKP Ordered Set from raw bytes
        
        Args:
            data: bytes object containing the ordered set symbols
        """
        return cls(list(data))
    
    def get_identifier(self):
        """Get the SKP Ordered Set Identifier (Symbol 0)"""
        return self.symbols[0]
    
    def decode_lfsr(self):
        """
        Decode the LFSR (Linear Feedback Shift Register) value from the ordered set
        
        Returns:
            dict with 'lfsr_value' (23-bit integer) and 'inverted_bit' (boolean)
        """
        skp_count = 4 * self.n
        
        # Symbol 4*N+1: Bit[7] = ~LFSR[22], Bit[6:0] = LFSR[22:16]
        sym1 = self.symbols[skp_count + 1]
        inverted_bit = bool(sym1 & 0x80)  # Bit 7
        lfsr_22_16 = sym1 & 0x7F  # Bits 6:0
        
        # Symbol 4*N+2: LFSR[15:8]
        lfsr_15_8 = self.symbols[skp_count + 2]
        
        # Symbol 4*N+3: LFSR[7:0]
        lfsr_7_0 = self.symbols[skp_count + 3]
        
        # Reconstruct 23-bit LFSR value
        lfsr_value = (lfsr_22_16 << 16) | (lfsr_15_8 << 8) | lfsr_7_0
        
        return {
            'lfsr_value': lfsr_value,
            'inverted_bit': inverted_bit,
            'lfsr_hex': f"0x{lfsr_value:06X}"
        }
    
    def __str__(self):
        """String representation of the ordered set"""
        lfsr_info = self.decode_lfsr()
        return (f"SKP Ordered Set (N={self.n}):\n"
                f"  SKP Symbols: {4 * self.n}\n"
                f"  LFSR Value: {lfsr_info['lfsr_hex']}\n"
                f"  Inverted Bit: {lfsr_info['inverted_bit']}\n"
                f"  Raw Symbols: {' '.join(f'{s:02X}' for s in self.symbols)}")
    
    def to_bytes(self):
        """Convert ordered set back to bytes"""
        return bytes(self.symbols)


def parse_skp_ordered_set(data):
    """
    Parse a Gen 2 SKP Ordered Set from raw data
    
    Args:
        data: bytes, bytearray, or list of integers
        
    Returns:
        SKPOrderedSet object
    """
    return SKPOrderedSet(data if isinstance(data, list) else list(data))


def create_skp_ordered_set(n, lfsr_value, inverted_bit=False):
    """
    Create a Gen 2 SKP Ordered Set
    
    Args:
        n: Number of SKP symbol groups (0-9)
        lfsr_value: 23-bit LFSR value (0x000000 - 0x7FFFFF)
        inverted_bit: Whether bit 7 of symbol 4*N+1 should be inverted
        
    Returns:
        SKPOrderedSet object
    """
    if not 0 <= n <= 9:
        raise ValueError(f"N must be between 0 and 9, got {n}")
    
    if not 0 <= lfsr_value <= 0x7FFFFF:
        raise ValueError(f"LFSR value must be 23-bit (0x000000-0x7FFFFF), got 0x{lfsr_value:X}")
    
    symbols = []
    
    # Add SKP symbols (0 through 4*N-1)
    symbols.extend([0xCC] * (4 * n))
    
    # Add SKPEND symbol at position 4*N
    symbols.append(0x33)
    
    # Symbol 4*N+1: Bit[7] = ~LFSR[22], Bit[6:0] = LFSR[22:16]
    lfsr_22_16 = (lfsr_value >> 16) & 0x7F
    bit7 = 0x80 if inverted_bit else 0x00
    symbols.append(bit7 | lfsr_22_16)
    
    # Symbol 4*N+2: LFSR[15:8]
    symbols.append((lfsr_value >> 8) & 0xFF)
    
    # Symbol 4*N+3: LFSR[7:0]
    symbols.append(lfsr_value & 0xFF)
    
    return SKPOrderedSet(symbols)


# Example usage and testing
if __name__ == "__main__":
    print("Gen 2 SKP Ordered Set Parser\n")
    
    # Example 1: Create an ordered set with N=2
    print("Example 1: Creating SKP Ordered Set (N=2)")
    skp1 = create_skp_ordered_set(n=2, lfsr_value=0x123456, inverted_bit=True)
    print(skp1)
    print()
    
    # Example 2: Parse from raw bytes
    print("Example 2: Parsing from raw bytes (N=0)")
    raw_data = bytes([0xCC, 0xCC, 0xCC, 0xCC, 0x33, 0xFF, 0xAB, 0xCD])
    skp2 = parse_skp_ordered_set(raw_data)
    print(skp2)
    print()
    
    # Example 3: Minimal ordered set (N=0)
    print("Example 3: Minimal SKP Ordered Set (N=0)")
    skp3 = create_skp_ordered_set(n=0, lfsr_value=0x000000, inverted_bit=False)
    print(skp3)
    print()
    
    # Example 4: Maximum ordered set (N=9)
    print("Example 4: Maximum SKP Ordered Set (N=9)")
    skp4 = create_skp_ordered_set(n=9, lfsr_value=0x7FFFFF, inverted_bit=True)
    print(skp4)
