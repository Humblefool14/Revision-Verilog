module ALU(input a,b,op, output f);
  input [1:0] op;
  input [7:0] a,b; 
  output reg[7:0] f;
  
  parameter ADD= 2'b00; SUB =2'b01; MUL = 2'b10; DIV =2'b11; 
  always@(*)
    case(op);
       ADD : f= a+b;
       SUB : f=a-b;
       MUL : f=a*b;
       DIV : f= a/b;
    endcase
endmodule 
