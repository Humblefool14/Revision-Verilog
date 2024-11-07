// Transmitter Preset Encoding defines
`define TX_PRESET_P0  4'b0000
`define TX_PRESET_P1  4'b0001
`define TX_PRESET_P2  4'b0010
`define TX_PRESET_P3  4'b0011
`define TX_PRESET_P4  4'b0100
`define TX_PRESET_P5  4'b0101
`define TX_PRESET_P6  4'b0110
`define TX_PRESET_P7  4'b0111
`define TX_PRESET_P8  4'b1000
`define TX_PRESET_P9  4'b1001
`define TX_PRESET_P10 4'b1010

// Transmitter Preset Reserved Range
`define TX_PRESET_RESERVED_START 4'b1011
`define TX_PRESET_RESERVED_END   4'b1111

// Receiver Preset Hint Encoding defines for 8.0 GT/s
`define RX_PRESET_MINUS_6DB  3'b000    // -6 dB
`define RX_PRESET_MINUS_7DB  3'b001    // -7 dB
`define RX_PRESET_MINUS_8DB  3'b010    // -8 dB
`define RX_PRESET_MINUS_9DB  3'b011    // -9 dB
`define RX_PRESET_MINUS_10DB 3'b100    // -10 dB
`define RX_PRESET_MINUS_11DB 3'b101    // -11 dB
`define RX_PRESET_MINUS_12DB 3'b110    // -12 dB
`define RX_PRESET_RESERVED   3'b111    // Reserved value

// Function to check if transmitter preset is in reserved range
function automatic bit is_tx_preset_reserved(logic [3:0] preset);
    return (preset >= `TX_PRESET_RESERVED_START && preset <= `TX_PRESET_RESERVED_END);
endfunction

// Function to check if receiver preset is valid
function automatic bit is_rx_preset_valid(logic [2:0] preset);
    return (preset != `RX_PRESET_RESERVED);
endfunction
