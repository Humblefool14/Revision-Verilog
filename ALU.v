`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    20:19:52 08/01/2020 
// Design Name: 
// Module Name:    ALU 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
module ALU(
    input [N-1 :0] A,
    input [N-1:0] B ,
    input [2:0] Select ,
    output reg Compare ,
    output reg [N-1:0] Dataout
    );
	 parameter N =2;
	 parameter Op_XOR = 3'b001,
				  Op_Incra=3'b010,
				  Op_Lt = 3'b100;
	 always@(A or B or Select)
	  case(Select)
	  Op_Incra :
				 begin
				 Dataout = A+1;
				 Compare = 'bx;
				 end 
		Op_Lt : 
					begin 
					Compare = A < B;
					Dataout = 'bx;
					end 
		Op_XOR : 
					begin 
					Dataout = A^B;
					Compare = 'bx;
					end 
		default : 
					 begin 
					 Dataout = 'bx;
					 Compare = 'bx;
					 end 
		endcase			 
endmodule
