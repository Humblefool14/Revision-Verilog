module Bitselect(A,C,Z,file);
  input [3:0] A,C;
  input reg[3:0]file;
  output [3:0] Z;
  
  assign Z[3:1] ={A[2],C[3:2]};
  assign Z[0] =file[3];
endmodule
