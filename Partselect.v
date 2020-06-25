module Partselect(A,C,Z);
  input [3:0] A,C;
  output [3:0] Z;
  
  assign Z[2:0] ={A[2],C[3:2]};
endmodule
