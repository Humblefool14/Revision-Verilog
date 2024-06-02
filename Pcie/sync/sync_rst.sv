module parameterized_bus_synchronizer #(
    parameter integer DATAWTH = 8,  // Width of the bus
    parameter integer NUMSTGS = 2  // Number of synchronization stages
)(
    input wire clk,                  // Clock signal of the destination domain
    input wire reset,                     // Synchronous reset signal
    input wire [DATAWTH-1:0] data_in,  // Asynchronous input bus from the source domain
    output reg [DATAWTH-1:0] data_out   // Synchronized output bus
);

    reg [DATAWTH-1:0] sync_stages [0:NUMSTGS-1];  // Synchronizer stages

    // Synchronizer logic
    always @(posedge clk) begin
        if (reset) begin
            sync_stages[0] <= {DATAWTH{1'b0}};
            data_out <= {DATAWTH{1'b0}};
        end else begin
            sync_stages[0] <= data_in;  // First stage
            for (integer i = 1; i < NUMSTGS; i = i + 1) begin
                sync_stages[i] <= sync_stages[i-1];  // Subsequent stages
            end
            data_out <= sync_stages[NUMSTGS-1];  // Final output
        end
    end

    `ifdef FORMAL 
    // Assertions for each bit of the bus
    genvar i;
    generate
        for (i = 0; i < DATAWTH; i = i + 1) begin : sync_assertions
            property data_out_stable;
                @(posedge clk)
                disable iff (reset)
                data_out[i] == $past(sync_stages[NUMSTGS-1][i]);
            endproperty
            assert property (data_out_stable)
                else $fatal("data_out[%0d] does not follow the last stage correctly", i);
        end
    endgenerate
    `endif 

endmodule