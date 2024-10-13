module pcie_extended_capability_header_decoder (
    input  logic        clk,
    input  logic        rst_n,
    
    // Input for the entire register
    input  logic [31:0] capability_header,
    
    // Output signals decoded from the register
    output logic [15:0] pci_express_extended_capability_id,
    output logic [3:0]  capability_version,
    output logic [11:0] next_capability_offset,
    
    // Additional outputs
    output logic        is_last_capability,
    output logic [1:0]  reserved_bits
);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            pci_express_extended_capability_id <= 16'h0000;
            capability_version                 <= 4'h0;
            next_capability_offset             <= 12'h000;
            is_last_capability                 <= 1'b0;
            reserved_bits                      <= 2'b00;
        end else begin
            pci_express_extended_capability_id <= capability_header[15:0];
            capability_version                 <= capability_header[19:16];
            next_capability_offset             <= capability_header[31:20];
            is_last_capability                 <= (capability_header[31:20] == 12'h000);
            reserved_bits                      <= capability_header[1:0];
        end
    end

    // Assertion to check if the reserved bits are always 00
    assert property (@(posedge clk) disable iff (!rst_n)
        reserved_bits == 2'b00)
    else $error("Reserved bits are not 00");

    // Assertion to check if the Next Capability Offset is valid
    assert property (@(posedge clk) disable iff (!rst_n)
        (next_capability_offset == 12'h000) || (next_capability_offset > 12'h0FF))
    else $error("Next Capability Offset is invalid");

endmodule