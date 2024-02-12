  // Special Symbols
`define B_COM                       8'hBC
`define B_STP                       8'hFB
`define B_SDP                       8'h5C
`define B_END                       8'hFD
`define B_EDB                       8'hFE
`define B_PAD                       8'hF7
`define B_SKP                       8'h1C
`define B_FTS                       8'h3C
`define B_IDL                       8'h7C
`define B_EIE                       8'hFC
`define B_ERR                       8'h23
`define K_COM                       {1'b1, `B_COM} // K28_5
`define K_STP                       {1'b1, `B_STP} // K27.7
`define K_SDP                       {1'b1, `B_SDP} // K28.2
`define K_END                       {1'b1, `B_END} // K29.7
`define K_EDB                       {1'b1, `B_EDB} // K30.7
`define K_PAD                       {1'b1, `B_PAD} // K23_7
`define K_SKP                       {1'b1, `B_SKP} // K28_0
`define K_FTS                       {1'b1, `B_FTS} // K28_1
`define K_IDL                       {1'b1, `B_IDL} // K28_3
`define K_EIE                       {1'b1, `B_EIE} // K28_7