module msi_x_capability_header (
    input wire clk,
    input wire reset,
    input wire [15:0] write_data,
    input wire write_enable,
    output wire [15:0] read_data
);

    // Register to hold the MSI-X Capability Header
    reg [15:0] header;

    // Constant for Capability ID
    localparam CAPABILITY_ID = 8'h11;

    // Initialize the header
    initial begin
        header[7:0] = CAPABILITY_ID;
        header[15:8] = 8'h00; // Initial value for Next Capability Pointer
    end

    // Write operation (only for Next Capability Pointer)
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            header[15:8] <= 8'h00;
        end else if (write_enable) begin
            header[15:8] <= write_data[15:8];
        end
    end

    // Read operation
    assign read_data = header;

endmodule 