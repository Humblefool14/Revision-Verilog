module delay_module #(
    parameter BITDATA = 8,    // Width of the data word
    parameter DELAY = 1       // Delay in clock cycles
)(
    input wire clk,                       // Clock signal
    input wire enable,                    // Enable signal
    input wire [BITDATA-1:0] din,         // Input data word
    output reg [BITDATA-1:0] dout         // Output data word
);

    reg [BITDATA-1:0] delay_reg [0:DELAY-1]; // Register array for delay pipeline
    integer i;

    always @(posedge clk) begin
        if (enable) begin
            // Shift input data through the delay pipeline
            delay_reg[0] <= din;
            for (i = 1; i < DELAY; i = i + 1) begin
                delay_reg[i] <= delay_reg[i-1];
            end
            // Output the data from the last register in the pipeline
            dout <= delay_reg[DELAY-1];
        end
    end

    `ifdef FORMAL 
    // Assertion to check if dout is correct
    // Ensure DELAY is greater than 0 for meaningful delay
    initial begin
        if (DELAY > 0) begin
            assert property (@(posedge clk) disable iff (!enable)
                dout == $past(din, DELAY))
            else $error("Assertion failed: dout does not match expected delayed din");
        end
    end
    `endif 

endmodule