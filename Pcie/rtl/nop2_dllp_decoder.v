module nop2_dllp_decoder (
    input  logic [31:0] packet_data,
    output logic        is_valid_nop2
);

    // Decode NOP2 DLLP
    always_comb begin
        // Check if all bits are 0 except bit 5 of byte 0
        if (packet_data == 32'h00000000) begin
            is_valid_nop2 = 1'b1;
        end else begin
            is_valid_nop2 = 1'b0;
        end
    end

    // Assertion to check if bits [31:6] and [4:0] are always 0
    always_ff @(posedge clk) begin
        assert((packet_data[31:6] == 26'b0) && (packet_data[4:0] == 5'b0))
        else $error("Invalid NOP2 DLLP: bits other than bit 5 of byte 0 are not 0");
    end

endmodule