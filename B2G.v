`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    22:01:17 07/31/2020 
// Design Name: 
// Module Name:    B2G 
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
module B2G(
    input A,
    input B,
    input C,
    output G0,
    output G1,
    output G2
    );
	 wire NotA,NotB,NotC;
	assign NotA = ~A;
	assign NotB = ~B;
	assign NotC = ~C;
	
	assign G2 = (A & B & C) + (A & NotB &C) + (A &NotB&NotC) +(A&B&NotC);
	assign G1 = (A & B & C) + (NotA & B &C) + (NotA &B&NotC) +(A&NotB&C);
	assign G0 = (A & B & C) + (NotA & NotB &C) + (NotA &B&NotC) +(A&NotB&NotC);
endmodule
