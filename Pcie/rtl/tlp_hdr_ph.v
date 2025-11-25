// Processing Hint (PH) enum
typedef enum logic [1:0] {
    PH_BIDIR   = 2'b00,  // Bi-directional data structure
    PH_REQ     = 2'b01,  // Requester - frequent access by device
    PH_TARGET  = 2'b10,  // Target - frequent access by Host
    PH_RSVD    = 2'b11   // Reserved
} ph_encoding_e;

/*
// TLP Header field assignments with PH
logic [1:0] tlp_hdr_ph;
ph_encoding_e processing_hint;

// Assign processing hint based on access pattern
assign processing_hint = PH_BIDIR;  // or PH_REQ, PH_TARGET based on use case
assign tlp_hdr_ph = processing_hint;

// PH location in TLP header depends on addressing mode:
// 32-bit addressing: Bits [1:0] of Byte 11 (DW2[25:24])
// 64-bit addressing: Bits [1:0] of Byte 15 (DW3[25:24])

// Example for 32-bit addressing
logic [31:0] tlp_dw2;
assign tlp_dw2[25:24] = tlp_hdr_ph;  // PH field in DW2

// Example for 64-bit addressing
logic [31:0] tlp_dw3;
assign tlp_dw3[25:24] = tlp_hdr_ph;  // PH field in DW3
*/ 
