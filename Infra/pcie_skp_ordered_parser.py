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


class UsageModel(Enum):
    """Usage Model for Margin Command (Table 4-25)"""
    LANE_MARGINING = 0b0  # Lane Margining at Receiver
    RESERVED = 0b1        # Reserved Encoding


class MarginType(Enum):
    """Margin Type values (3 bits)"""
    TYPE_0 = 0
    TYPE_1 = 1
    TYPE_2 = 2
    TYPE_3 = 3
    TYPE_4 = 4
    TYPE_5 = 5
    TYPE_6 = 6
    TYPE_7 = 7


@dataclass
class SKPSymbol:
    """Represents a single SKP symbol"""
    position: int  # Position in ordered set (0 to 4*N+3)
    value: str     # Hex value of the symbol
    description: str


@dataclass
class MarginCommandFields:
    """Margin Command Related Fields (Table 4-25) for Control SKP Ordered Set"""
    usage_model: UsageModel
    margin_type: MarginType = MarginType.TYPE_0
    receiver_number: int = 0  # 3 bits [2:0]
    margin_payload: int = 0   # 8 bits [7:0]
    
    def __post_init__(self):
        """Validate field ranges"""
        if not 0 <= self.receiver_number <= 7:
            raise ValueError("receiver_number must be 0-7 (3 bits)")
        if not 0 <= self.margin_payload <= 255:
            raise ValueError("margin_payload must be 0-255 (8 bits)")
    
    def encode_symbol_4n_plus_2(self, margin_parity: int) -> int:
        """
        Encode Symbol 4*N+2 based on usage model
        
        Args:
            margin_parity: Margin Parity bit (bit 7)
            
        Returns:
            8-bit value for Symbol 4*N+2
        """
        margin_parity_bit = (margin_parity & 1) << 7
        
        if self.usage_model == UsageModel.LANE_MARGINING:
            # Usage Model = 0b: Lane Margining at Receiver
            # Bit 7: Margin Parity
            # Bit 6: Usage Model = 0b
            # Bits [5:3]: Margin Type
            # Bits [2:0]: Receiver Number
            usage_model_bit = 0 << 6
            margin_type_bits = (self.margin_type.value & 0x7) << 3
            receiver_number_bits = self.receiver_number & 0x7
            return margin_parity_bit | usage_model_bit | margin_type_bits | receiver_number_bits
        else:
            # Usage Model = 1b: Reserved Encoding
            # Bit 7: Margin Parity
            # Bit 6: Usage Model = 1b
            # Bits [5:0]: Reserved
            usage_model_bit = 1 << 6
            return margin_parity_bit | usage_model_bit
    
    def encode_symbol_4n_plus_3(self) -> int:
        """
        Encode Symbol 4*N+3 based on usage model
        
        Returns:
            8-bit value for Symbol 4*N+3
        """
        if self.usage_model == UsageModel.LANE_MARGINING:
            # Bits [7:0]: Margin Payload
            return self.margin_payload & 0xFF
        else:
            # Bits [7:0]: Reserved
            return 0x00
    
    @staticmethod
    def decode_symbol_4n_plus_2(value: int) -> tuple:
        """
        Decode Symbol 4*N+2
        
        Returns:
            Tuple of (margin_parity, usage_model, margin_type, receiver_number)
        """
        margin_parity = (value >> 7) & 1
        usage_model_bit = (value >> 6) & 1
        usage_model = UsageModel.RESERVED if usage_model_bit else UsageModel.LANE_MARGINING
        
        if usage_model == UsageModel.LANE_MARGINING:
            margin_type = MarginType((value >> 3) & 0x7)
            receiver_number = value & 0x7
        else:
            margin_type = None
            receiver_number = None
        
        return margin_parity, usage_model, margin_type, receiver_number
    
    @staticmethod
    def decode_symbol_4n_plus_3(value: int, usage_model: UsageModel) -> Optional[int]:
        """
        Decode Symbol 4*N+3
        
        Returns:
            Margin Payload if usage_model is LANE_MARGINING, None otherwise
        """
        if usage_model == UsageModel.LANE_MARGINING:
            return value & 0xFF
        return None


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
    margin_fields: Optional[MarginCommandFields] = None
    
    def __init__(self, data_rate: DataRate, n: int = 1,
                 data_parity: int = 0,
                 first_retimer_parity: int = 0,
                 second_retimer_parity: int = 0,
                 margin_crc: int = 0,
                 margin_parity: int = 0,
                 margin_fields: Optional[MarginCommandFields] = None):
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
            margin_fields: Optional MarginCommandFields for Table 4-25 encoding
        """
        self.data_rate = data_rate
        self.symbols = []
        self.margin_fields = margin_fields
        
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
        
        # Symbol 4*N+2: Margin Parity and Margin Command fields (Table 4-25)
        if margin_fields:
            symbol_value_2 = margin_fields.encode_symbol_4n_plus_2(margin_parity)
            if margin_fields.usage_model == UsageModel.LANE_MARGINING:
                desc = f"Bit 7: Margin Parity, Bit 6: Usage Model=0b (Lane Margining), Bits [5:3]: Margin Type={margin_fields.margin_type.value}, Bits [2:0]: Receiver Number={margin_fields.receiver_number}"
            else:
                desc = "Bit 7: Margin Parity, Bit 6: Usage Model=1b (Reserved), Bits [5:0]: Reserved"
        else:
            # Default behavior without margin fields
            symbol_value_2 = (margin_parity & 1) << 7
            desc = "Bit 7: Margin Parity, Bits [6:0]: Refer to Section 4.2.13.1"
        
        self.symbols.append(SKPSymbol(
            position=4 * n + 2,
            value=f"{symbol_value_2:02X}h",
            description=desc
        ))
        
        # Symbol 4*N+3: Margin Payload or Reserved (Table 4-25)
        if margin_fields:
            symbol_value_3 = margin_fields.encode_symbol_4n_plus_3()
            if margin_fields.usage_model == UsageModel.LANE_MARGINING:
                desc = f"Bits [7:0]: Margin Payload = {symbol_value_3:02X}h"
            else:
                desc = "Bits [7:0]: Reserved"
        else:
            # Default behavior without margin fields
            symbol_value_3 = 0x00
            desc = "Bits [7:0]: Refer to Section 4.2.13.1"
        
        self.symbols.append(SKPSymbol(
            position=4 * n + 3,
            value=f"{symbol_value_3:02X}h",
            description=desc
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
        if self.margin_fields:
            output += "\nMargin Command Fields (Table 4-25):\n"
            output += f"  Usage Model: {self.margin_fields.usage_model.name}\n"
            if self.margin_fields.usage_model == UsageModel.LANE_MARGINING:
                output += f"  Margin Type: {self.margin_fields.margin_type.value}\n"
                output += f"  Receiver Number: {self.margin_fields.receiver_number}\n"
                output += f"  Margin Payload: 0x{self.margin_fields.margin_payload:02X}\n"
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
        
        # Extract parity and CRC information from Symbol 4*N+1
        symbol_4n_plus_1 = data[end_pos + 1]
        data_parity = (symbol_4n_plus_1 >> 7) & 1
        first_retimer_parity = (symbol_4n_plus_1 >> 6) & 1
        second_retimer_parity = (symbol_4n_plus_1 >> 5) & 1
        margin_crc = symbol_4n_plus_1 & 0x1F
        
        # Extract and decode Symbol 4*N+2 (Table 4-25)
        symbol_4n_plus_2 = data[end_pos + 2]
        margin_parity, usage_model, margin_type, receiver_number = \
            MarginCommandFields.decode_symbol_4n_plus_2(symbol_4n_plus_2)
        
        # Extract Symbol 4*N+3 (Table 4-25)
        symbol_4n_plus_3 = data[end_pos + 3]
        margin_payload = MarginCommandFields.decode_symbol_4n_plus_3(symbol_4n_plus_3, usage_model)
        
        # Create MarginCommandFields if usage model is LANE_MARGINING
        margin_fields = None
        if usage_model == UsageModel.LANE_MARGINING and margin_type is not None:
            margin_fields = MarginCommandFields(
                usage_model=usage_model,
                margin_type=margin_type,
                receiver_number=receiver_number,
                margin_payload=margin_payload if margin_payload is not None else 0
            )
        
        return ControlSKPOrderedSet(
            data_rate=data_rate,
            n=n,
            data_parity=data_parity,
            first_retimer_parity=first_retimer_parity,
            second_retimer_parity=second_retimer_parity,
            margin_crc=margin_crc,
            margin_parity=margin_parity,
            margin_fields=margin_fields
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
    
    # Example 2: Create a Control SKP Ordered Set (without Margin fields)
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
    
    # Example 3: Control SKP with Margin Command Fields (Table 4-25)
    print("Example 3: Control SKP with Lane Margining (Table 4-25)")
    print("-" * 70)
    margin_fields = MarginCommandFields(
        usage_model=UsageModel.LANE_MARGINING,
        margin_type=MarginType.TYPE_3,
        receiver_number=5,
        margin_payload=0xAB
    )
    
    control_skp_margin = ControlSKPOrderedSet(
        data_rate=DataRate.RATE_8_0,
        n=1,
        data_parity=1,
        first_retimer_parity=1,
        second_retimer_parity=0,
        margin_crc=0x0F,
        margin_parity=1,
        margin_fields=margin_fields
    )
    print(control_skp_margin)
    print(f"Byte sequence: {control_skp_margin.to_bytes().hex(' ')}")
    print()
    
    # Example 4: Parse a Control SKP with Margin fields
    print("Example 4: Parse Control SKP with Margin fields from bytes")
    print("-" * 70)
    test_bytes = control_skp_margin.to_bytes()
    parsed = SKPParser.parse_control(test_bytes)
    if parsed:
        print("Successfully parsed Control SKP:")
        print(parsed)
    else:
        print("Failed to parse")
    print()
    
    # Example 5: Control SKP with Reserved Usage Model
    print("Example 5: Control SKP with Reserved Usage Model")
    print("-" * 70)
    margin_fields_reserved = MarginCommandFields(
        usage_model=UsageModel.RESERVED
    )
    
    control_skp_reserved = ControlSKPOrderedSet(
        data_rate=DataRate.RATE_32_0,
        n=1,
        data_parity=0,
        first_retimer_parity=0,
        second_retimer_parity=0,
        margin_crc=0x00,
        margin_parity=0,
        margin_fields=margin_fields_reserved
    )
    print(control_skp_reserved)
    print(f"Byte sequence: {control_skp_reserved.to_bytes().hex(' ')}")


if __name__ == "__main__":
    main()
