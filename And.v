module And(A,B,Z);
  input A,B;
  output reg Z;
  
  always@(*)
    Z= A&B;
endmodule
