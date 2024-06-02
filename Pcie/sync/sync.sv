module sync #(
    parameter integer NUMSTGS = 2  // Number of synchronization stages
)(
    input wire clk,                  // Clock signal of the destination domain
    input wire data_in,  // Asynchronous input bus from the source domain
    output wire data_out   // Synchronized output bus
);

    reg sync_stages [0:NUMSTGS-1];  // Synchronizer stages

    // Synchronizer logic
    always @(posedge clk) begin
        sync_stages[0] <= data_in;  // First stage
        for (integer i = 1; i < NUMSTGS; i = i + 1) begin
            sync_stages[i] <= sync_stages[i-1];  // Subsequent stages
        end
        data_out <= sync_stages[NUMSTGS-1];  // Final output
    end

endmodule