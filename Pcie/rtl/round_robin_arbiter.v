module roundrobin #(
    parameter NUMDESC = 8)(
   input wire  [NUMDESC-1:0]      req,
   input wire  [NUMDESC-1:0]      cstate,
   input wire                     cstate0,
   output wire [NUMDESC-1:0]      nextstate
   );

   //-------------------------------------------------------------

  wire [2*NUMDESC-1:0] nrequest;
  wire [2*NUMDESC-1:0] inv_inc;
  wire [2*NUMDESC-1:0] granted;

  // request      ----1110    ----1010    ----0101   ----0000    ----0100
  // curr_state   ----0001    ----0100    ----1000   ----0000    ----0000

  // nrequest     00000001    00000101    00001010   ----1111    ----1011
  // inv_inc      11110010    11101001    00010010   00010000    00001100
  // granted      00000010    00001000    00010000   00010000    00000100
  // next_state   ----0010    ----1000    ----0001   ----0000    ----0100

  // Invert & expand request vector
  assign nrequest   = {{(NUMDESC){1'b0}}, ~req};

  // Invert & increment request
  // (if curr_state=0's then do +1)
  assign inv_inc = nrequest + {cstate | {{(NUMDESC-1){1'b0}}, cstate0}};

  // Detect the trailing one: return one-hot value
  assign granted = (inv_inc & {req, req});

  // Handle wrap-around
  assign next_state = granted[NUMDESC-1:0];
endmodule 