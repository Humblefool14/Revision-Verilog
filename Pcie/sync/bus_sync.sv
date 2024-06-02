module bus_sync #(
    parameter integer NUMSTGS = 2,  // Number of synchronization stages
    parameter integer DATAWTH = 8
)(
    input wire clk,                  // Clock signal of the destination domain
    input wire  [DATAWTH-1:0] data_in,  // Asynchronous input bus from the source domain
    output wire [DATAWTH-1:0] data_out   // Synchronized output bus
);

 generate(genvar i = 0; i < DATAWTH; i=i+1)begin 
    b_sync(
        .clk(clk),
        .data_in(data_in[i]), 
        .data_out(data_out[i])
        ); 
 end
 endgenerate 

endmodule 