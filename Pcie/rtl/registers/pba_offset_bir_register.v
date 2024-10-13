module pba_offset_bir_register (
    input wire clk,
    input wire reset,
    input wire [31:0] write_data,
    input wire write_enable,
    output reg [31:0] read_data
);

    // PBA Offset (bits 31:3) and PBA BIR (bits 2:0)
    reg [31:0] register;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            register <= 32'b0;
        end else if (write_enable) begin
            // PBA Offset (bits 31:3)
            register[31:3] <= write_data[31:3];
            // PBA BIR (bits 2:0)
            register[2:0] <= write_data[2:0];
        end
    end

    // Read operation
    always @(*) begin
        read_data = register;
    end

endmodule