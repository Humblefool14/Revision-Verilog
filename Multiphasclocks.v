`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    19:16:39 07/31/2020 
// Design Name: 
// Module Name:    Multiphasclocks 
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
module Multiphasclocks(
    input Clk,
    input A,
    input B,
    input C,
    output E
    );
	  reg E,D;
	  always@(posedge Clk)
			E <= D|C;
	  always@(negedge Clk)
			D <= A&B;
endmodule
