"""
SKP Ordered Set Parser for 128b/130b Encoding
Parses Standard and Control SKP Ordered Sets according to tables 4-22 and 4-23
"""

from enum import Enum
from dataclasses import dataclass
from typing import List, Optional, Union


class DataRate(Enum):
    """Supported data rates"""
    RATE_8_0 = "8.0 GT/s"
    RATE_16_0 = "16.0 GT/s"
    RATE_32_0 = "32.0 GT/s"
    RATE_HIGHER = "32.0+ GT/s"


class LTSSMState(Enum):
    """LTSSM states"""
    POLLING_COMPLIANCE = "Polling.Compliance"
    OTHER = "Other"


@dataclass
class SKPSymbol:
    """Represents a single SKP symbol"""
    position: int  # Position in ordered set (0 to 4*N+3)
    value: str     # Hex value of the symbol
    description: str


@dataclass
class StandardSKPOrderedSet:
    """Standard SKP Ordered Set (Table 4-22)"""
    data_rate: DataRate
    symbols: List[SKPSymbol]
    
    def __init__(self, data_rate: DataRate, n: int = 1, 
                 ltssm_state: LTSSMState = LTSSMState.OTHER,
                 prior_block_was_data: bool = False,
                 lfsr_value: int = 0,
                 error_status: int = 0):
        """
        Initialize Standard SKP Ordered Set
        
        Args:
            data_rate: Data rate (8.0/16.0 GT/s or 32.0+ GT/s)
            n: Number of SKP symbols (1-5)
            ltssm_state: Current LTSSM state
            prior_block_was_data: Whether prior block was a data block
            lfsr_value: LFSR[22:16] or LFSR[22] value
            error_status: Error_Status[7:0] value
        """
        self.data_rate = data_rate
        self.symbols = []
        
        # Symbols 0 through (4*N-1): SKP identifiers
        skp_identifier = "AAh" if data_rate in [DataRate.RATE_8_0, DataRate.RATE_16_0] else "99h"
        for i in range(4 * n):
            self.symbols.append(SKPSymbol(
                position=i,
                value=skp_identifier,
                description=f"SKP Symbol. Symbol 0 is the SKP Ordered Set identifier."
            ))
        
        # Symbol 4*N: SKP_END
        self.symbols.append(SKPSymbol(
            position=4 * n,
            value="E1h",
            description="SKP_END Symbol. Signifies the end of the SKP Ordered Set after three more Symbols."
        ))
        
        # Symbol 4*N+1: Conditional content
        symbol_4n_plus_1 = self._build_symbol_4n_plus_1(
            n, ltssm_state, prior_block_was_data, lfsr_value
        )
        self.symbols.append(symbol_4n_plus_1)
        
        # Symbol 4*N+2: Error status or LFSR
        symbol_4n_plus_2 = self._build_symbol_4n_plus_2(
            n, ltssm_state, error_status, lfsr_value
        )
        self.symbols.append(symbol_4n_plus_2)
        
        # Symbol 4*N+3: Error status complement or LFSR
        symbol_4n_plus_3 = self._build_symbol_4n_plus_3(
            n, ltssm_state, error_status, lfsr_value
        )
        self.symbols.append(symbol_4n_plus_3)
    
    def _build_symbol_4n_plus_1(self, n: int, ltssm_state: LTSSMState, 
                                prior_block_was_data: bool, lfsr_value: int) -> SKPSymbol:
        """Build symbol at position 4*N+1"""
        if ltssm_state == LTSSMState.POLLING_COMPLIANCE:
            desc = "(i) If LTSSM state is Polling.Compliance: AAh"
            value = "AAh"
        elif prior_block_was_data:
            bit_7 = (lfsr_value >> 6) & 1  # Data Parity
            bit_6_0 = lfsr_value & 0x7F    # LFSR[22:16]
            value = f"{(bit_7 << 7) | bit_6_0:02X}h"
            desc = f"(ii) Prior block was Data Block: Bit[7]=Data Parity, Bit[6:0]=LFSR[22:16]"
        else:
            bit_7 = (lfsr_value >> 22) & 1  # ~LFSR[22]
            bit_6_0 = lfsr_value & 0x7F     # LFSR[22:16]
            value = f"{((~bit_7 & 1) << 7) | bit_6_0:02X}h"
            desc = f"(iii) Else: Bit[7]=~LFSR[22], Bit[6:0]=LFSR[22:16]"
        
        return SKPSymbol(position=4*n+1, value=value, description=desc)
    
    def _build_symbol_4n_plus_2(self, n: int, ltssm_state: LTSSMState,
                                error_status: int, lfsr_value: int) -> SKPSymbol:
        """Build symbol at position 4*N+2"""
        if ltssm_state == LTSSMState.POLLING_COMPLIANCE:
            value = f"{error_status:02X}h"
            desc = f"(i) If LTSSM state is Polling.Compliance: Error_Status[7:0]"
        else:
            value = f"{lfsr_value & 0xFF:02X}h"
            desc = f"(ii) Else LFSR[15:8]"
        
        return SKPSymbol(position=4*n+2, value=value, description=desc)
    
    def _build_symbol_4n_plus_3(self, n: int, ltssm_state: LTSSMState,
                                error_status: int, lfsr_value: int) -> SKPSymbol:
        """Build symbol at position 4*N+3"""
        if ltssm_state == LTSSMState.POLLING_COMPLIANCE:
            value = f"{(~error_status & 0xFF):02X}h"
            desc = f"(i) If LTSSM state is Polling.Compliance: ~Error_Status[7:0]"
        else:
            value = f"{lfsr_value & 0xFF:02X}h"
            desc = f"(ii) Else: LFSR[7:0]"
        
        return SKPSymbol(position=4*n+3, value=value, description=desc)
    
    def to_bytes(self) -> bytes:
        """Convert ordered set to byte sequence"""
        result = []
        for symbol in self.symbols:
            # Extract hex value and convert to byte
            hex_str = symbol.value.replace('h', '')
            result.append(int(hex_str, 16))
        return bytes(result)
    
    def __str__(self) -> str:
        output = f"Standard SKP Ordered Set ({self.data_rate.value})\n"
        output += "=" * 70 + "\n"
        for symbol in self.symbols:
            output += f"Symbol {symbol.position}: {symbol.value:6s} - {symbol.description}\n"
        return output


@dataclass
class ControlSKPOrderedSet:
    """Control SKP Ordered Set (Table 4-23)"""
    data_rate: DataRate
    symbols: List[SKPSymbol]
    
    def __init__(self, data_rate: DataRate, n: int = 1,
                 data_parity: int = 0,
                 first_retimer_parity: int = 0,
                 second_retimer_parity: int = 0,
                 margin_crc: int = 0,
                 margin_parity: int = 0):
        """
        Initialize Control SKP Ordered Set
        
        Args:
            data_rate: Data rate (8.0/16.0 GT/s or 32.0+ GT/s)
            n: Number of SKP symbols (1-5)
            data_parity: Data Parity bit
            first_retimer_parity: First Retimer Data Parity bit
            second_retimer_parity: Second Retimer Parity bit
            margin_crc: Margin CRC [4:0] value
            margin_parity: Margin Parity bit
        """
        self.data_rate = data_rate
        self.symbols = []
        
        # Symbols 0 through (4*N-1): SKP identifiers
        skp_identifier = "AAh" if data_rate in [DataRate.RATE_8_0, DataRate.RATE_16_0] else "99h"
        for i in range(4 * n):
            self.symbols.append(SKPSymbol(
                position=i,
                value=skp_identifier,
                description=f"SKP Symbol. Symbol 0 is the SKP Ordered Set identifier."
            ))
        
        # Symbol 4*N: SKP_END_CTL
        self.symbols.append(SKPSymbol(
            position=4 * n,
            value="78h",
            description="SKP_END_CTL Symbol. Signifies the end of the Control SKP Ordered Set after three more Symbols."
        ))
        
        # Symbol 4*N+1: Parity and CRC information
        bit_7 = data_parity & 1
        bit_6 = first_retimer_parity & 1
        bit_5 = second_retimer_parity & 1
        bits_4_0 = margin_crc & 0x1F
        
        symbol_value = (bit_7 << 7) | (bit_6 << 6) | (bit_5 << 5) | bits_4_0
        self.symbols.append(SKPSymbol(
            position=4 * n + 1,
            value=f"{symbol_value:02X}h",
            description="Bit 7: Data Parity, Bit 6: First Retimer Data Parity, Bit 5: Second Retimer Parity, Bits [4:0]: Margin CRC [4:0]"
        ))
        
        # Symbol 4*N+2: Margin Parity and reference to Section 4.2.13.1
        bit_7_margin = margin_parity & 1
        symbol_value_2 = (bit_7_margin << 7)  # Bits [6:0] refer to Section 4.2.13.1
        self.symbols.append(SKPSymbol(
            position=4 * n + 2,
            value=f"{symbol_value_2:02X}h",
            description="Bit 7: Margin Parity, Bits [6:0]: Refer to Section 4.2.13.1"
        ))
        
        # Symbol 4*N+3: Reference to Section 4.2.13.1
        self.symbols.append(SKPSymbol(
            position=4 * n + 3,
            value="00h",
            description="Bits [7:0]: Refer to Section 4.2.13.1"
        ))
    
    def to_bytes(self) -> bytes:
        """Convert ordered set to byte sequence"""
        result = []
        for symbol in self.symbols:
            hex_str = symbol.value.replace('h', '')
            result.append(int(hex_str, 16))
        return bytes(result)
    
    def __str__(self) -> str:
        output = f"Control SKP Ordered Set ({self.data_rate.value})\n"
        output += "=" * 70 + "\n"
        for symbol in self.symbols:
            output += f"Symbol {symbol.position}: {symbol.value:6s} - {symbol.description}\n"
        return output


class SKPParser:
    """Parser for SKP Ordered Sets"""
    
    @staticmethod
    def parse_standard(data: bytes) -> Optional[StandardSKPOrderedSet]:
        """
        Parse a byte sequence as a Standard SKP Ordered Set
        
        Args:
            data: Byte sequence to parse
            
        Returns:
            StandardSKPOrderedSet if valid, None otherwise
        """
        if len(data) < 7:  # Minimum size: 4 SKP + 1 END + 3 data
            return None
        
        # Detect data rate based on first symbol
        if data[0] == 0xAA:
            data_rate = DataRate.RATE_8_0
        elif data[0] == 0x99:
            data_rate = DataRate.RATE_32_0
        else:
            return None
        
        # Find SKP_END marker (E1h)
        end_pos = -1
        for i, byte in enumerate(data):
            if byte == 0xE1:
                end_pos = i
                break
        
        if end_pos == -1 or end_pos < 4:
            return None
        
        # Calculate N
        n = end_pos // 4
        if end_pos != 4 * n:
            return None
        
        # Verify we have exactly 3 more symbols after END
        if len(data) != end_pos + 4:
            return None
        
        # Parse the symbols (simplified - actual parsing would need LTSSM state context)
        print(f"Detected Standard SKP with N={n}, data_rate={data_rate.value}")
        return None  # Would return parsed object with proper context
    
    @staticmethod
    def parse_control(data: bytes) -> Optional[ControlSKPOrderedSet]:
        """
        Parse a byte sequence as a Control SKP Ordered Set
        
        Args:
            data: Byte sequence to parse
            
        Returns:
            ControlSKPOrderedSet if valid, None otherwise
        """
        if len(data) < 7:
            return None
        
        # Detect data rate
        if data[0] == 0xAA:
            data_rate = DataRate.RATE_8_0
        elif data[0] == 0x99:
            data_rate = DataRate.RATE_32_0
        else:
            return None
        
        # Find SKP_END_CTL marker (78h)
        end_pos = -1
        for i, byte in enumerate(data):
            if byte == 0x78:
                end_pos = i
                break
        
        if end_pos == -1 or end_pos < 4:
            return None
        
        # Calculate N
        n = end_pos // 4
        if end_pos != 4 * n:
            return None
        
        # Verify we have exactly 3 more symbols after END
        if len(data) != end_pos + 4:
            return None
        
        # Extract parity and CRC information
        symbol_4n_plus_1 = data[end_pos + 1]
        data_parity = (symbol_4n_plus_1 >> 7) & 1
        first_retimer_parity = (symbol_4n_plus_1 >> 6) & 1
        second_retimer_parity = (symbol_4n_plus_1 >> 5) & 1
        margin_crc = symbol_4n_plus_1 & 0x1F
        
        symbol_4n_plus_2 = data[end_pos + 2]
        margin_parity = (symbol_4n_plus_2 >> 7) & 1
        
        return ControlSKPOrderedSet(
            data_rate=data_rate,
            n=n,
            data_parity=data_parity,
            first_retimer_parity=first_retimer_parity,
            second_retimer_parity=second_retimer_parity,
            margin_crc=margin_crc,
            margin_parity=margin_parity
        )


def main():
    """Example usage of the SKP parser"""
    
    print("=" * 70)
    print("SKP Ordered Set Parser - Example Usage")
    print("=" * 70)
    print()
    
    # Example 1: Create a Standard SKP Ordered Set
    print("Example 1: Standard SKP Ordered Set (8.0 GT/s, N=1)")
    print("-" * 70)
    standard_skp = StandardSKPOrderedSet(
        data_rate=DataRate.RATE_8_0,
        n=1,
        ltssm_state=LTSSMState.OTHER,
        prior_block_was_data=False,
        lfsr_value=0x1A2B3C,
        error_status=0x00
    )
    print(standard_skp)
    print(f"Byte sequence: {standard_skp.to_bytes().hex(' ')}")
    print()
    
    # Example 2: Create a Control SKP Ordered Set
    print("Example 2: Control SKP Ordered Set (32.0 GT/s, N=2)")
    print("-" * 70)
    control_skp = ControlSKPOrderedSet(
        data_rate=DataRate.RATE_32_0,
        n=2,
        data_parity=1,
        first_retimer_parity=0,
        second_retimer_parity=1,
        margin_crc=0x15,
        margin_parity=1
    )
    print(control_skp)
    print(f"Byte sequence: {control_skp.to_bytes().hex(' ')}")
    print()
    
    # Example 3: Parse a Control SKP
    print("Example 3: Parse Control SKP from bytes")
    print("-" * 70)
    test_bytes = control_skp.to_bytes()
    parsed = SKPParser.parse_control(test_bytes)
    if parsed:
        print("Successfully parsed Control SKP:")
        print(parsed)
    else:
        print("Failed to parse")


if __name__ == "__main__":
    main()
