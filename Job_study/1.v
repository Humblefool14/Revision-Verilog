`timescale 1ns/1ps
module mux_2x1(
    input [7:0] X,
    input [7:0] Y,
    input sel,
    output [7:0] out_port);

        assign out_port = sel ?X:Y;

endmodule 