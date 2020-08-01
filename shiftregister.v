`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    18:27:45 08/01/2020 
// Design Name: 
// Module Name:    measlyfsm 
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
module shiftregister(
    input Clk,
    input Clear,
    input Leftin,
    input Rightin,
    input S0,
    input S1,
    input [2:0] Parin,
    output reg [2:0] Q
    );
	 always@(negedge Clear or posedge Clk)
		if(!Clear)
		  Q <= 3'b000; // Clear the value and set 
		else 
		  case({S0,S1})
		  2'b00: ; // Nothing has changed 
		  2'b01: 
				Q <= {Q[1:0],Rightin};  // shift left 
		  2'b10: 
		      Q <= {Leftin,Q[2:1]}; // Shift right
		   2'b11 :
			    Q <= Parin; // Load the bits 
			endcase
endmodule
