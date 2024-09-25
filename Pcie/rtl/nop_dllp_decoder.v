module nop_dllp_decoder (
    input  logic [31:0] packet_data,
    output logic        is_valid_nop
);

    // Decode NOP DLLP
    always_comb begin
        // Check if bits [7:0] are 0011_0001 (0x31)
        // The rest of the bits can be arbitrary
        if (packet_data[7:0] == 8'h31) begin
            is_valid_nop = 1'b1;
        end else begin
            is_valid_nop = 1'b0;
        end
    end

    // Assertion to check if bits [7:0] are always 0011_0001
    always_ff @(posedge clk) begin
        assert(packet_data[7:0] == 8'h31)
        else $error("Invalid NOP DLLP: first byte is not 0x31");
    end

endmodule