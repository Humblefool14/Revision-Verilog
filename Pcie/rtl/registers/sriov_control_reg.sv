// SR-IOV Control Register
// Implements PCI Express Base Specification 6.0.1 Figure 9-13/Table 9-4
module sriov_control_reg #(
    parameter IS_LOWEST_PF = 0  // Set to 1 if this is the lowest-numbered PF
)(
    // Standard inputs
    input wire        clk,
    input wire        rst_n,
    input wire [11:0] addr,     // Configuration space address
    input wire        wr_en,    // Write enable
    input wire [31:0] wr_data,  // Write data
    
    // Capability dependencies
    input wire        cap_10bit_tag_supported,
    input wire        cap_14bit_tag_supported,
    
    // Status inputs
    input wire        has_outstanding_nonposted_requests,
    
    // Control outputs
    output wire       vf_enable,
    output wire       vf_migration_enable,
    output wire       vf_migration_int_enable,
    output wire       vf_mse,
    output wire       ari_capable_hierarchy,
    output wire       vf_10bit_tag_enable,
    output wire       vf_14bit_tag_enable,
    
    // Read data output
    output reg [31:0] rd_data
);

    // Register bit positions
    localparam RSVDP_POS = 7;
    localparam RSVDP_WIDTH = 9;

    // Internal registers for RW fields
    reg vf_enable_reg;
    reg vf_migration_enable_reg;
    reg vf_migration_int_enable_reg;
    reg vf_mse_reg;
    reg ari_capable_hierarchy_reg;
    reg vf_10bit_tag_enable_reg;
    reg vf_14bit_tag_enable_reg;

    // Write logic
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Default values are 0b for all fields
            vf_enable_reg <= 1'b0;
            vf_migration_enable_reg <= 1'b0;
            vf_migration_int_enable_reg <= 1'b0;
            vf_mse_reg <= 1'b0;
            ari_capable_hierarchy_reg <= 1'b0;
            vf_10bit_tag_enable_reg <= 1'b0;
            vf_14bit_tag_enable_reg <= 1'b0;
        end else if (wr_en) begin
            // VF Enable (bit 0)
            vf_enable_reg <= wr_data[0];
            
            // VF Migration Enable (bit 1)
            // Only writable in lowest-numbered PF
            if (IS_LOWEST_PF) begin
                vf_migration_enable_reg <= wr_data[1];
            end
            
            // VF Migration Interrupt Enable (bit 2)
            vf_migration_int_enable_reg <= wr_data[2];
            
            // VF MSE (bit 3)
            vf_mse_reg <= wr_data[3];
            
            // ARI Capable Hierarchy (bit 4)
            // Only writable in lowest-numbered PF
            if (IS_LOWEST_PF) begin
                ari_capable_hierarchy_reg <= wr_data[4];
            end
            
            // VF 10-Bit Tag Requester Enable (bit 5)
            // Only writable if supported and 14-bit not enabled
            if (cap_10bit_tag_supported && !vf_14bit_tag_enable_reg && !has_outstanding_nonposted_requests) begin
                vf_10bit_tag_enable_reg <= wr_data[5];
            end
            
            // VF 14-Bit Tag Requester Enable (bit 6)
            // Only writable if supported and 10-bit not enabled
            if (cap_14bit_tag_supported && !vf_10bit_tag_enable_reg && !has_outstanding_nonposted_requests) begin
                vf_14bit_tag_enable_reg <= wr_data[6];
            end
        end
    end

    // Read logic
    always @(*) begin
        rd_data = 32'h0;  // Default value
        
        // Bit assignments
        rd_data[0] = vf_enable_reg;
        rd_data[1] = IS_LOWEST_PF ? vf_migration_enable_reg : 1'b0;
        rd_data[2] = vf_migration_int_enable_reg;
        rd_data[3] = vf_mse_reg;
        rd_data[4] = IS_LOWEST_PF ? ari_capable_hierarchy_reg : 1'b0;
        rd_data[5] = vf_10bit_tag_enable_reg;
        rd_data[6] = vf_14bit_tag_enable_reg;
        // Bits [15:7] are RsvdP
        rd_data[RSVDP_POS +: RSVDP_WIDTH] = 9'h0;
    end

    // Output assignments
    assign vf_enable = vf_enable_reg;
    assign vf_migration_enable = vf_migration_enable_reg;
    assign vf_migration_int_enable = vf_migration_int_enable_reg;
    assign vf_mse = vf_mse_reg;
    assign ari_capable_hierarchy = ari_capable_hierarchy_reg;
    assign vf_10bit_tag_enable = vf_10bit_tag_enable_reg;
    assign vf_14bit_tag_enable = vf_14bit_tag_enable_reg;

    // Assertions
    // synthesis translate_off
    always @(posedge clk) begin
        // Check mutually exclusive tag enables
        if (vf_10bit_tag_enable_reg && vf_14bit_tag_enable_reg) begin
            $error("SR-IOV Control: 10-bit and 14-bit tag enables cannot both be set");
        end
        
        // Check capability dependencies
        if (vf_10bit_tag_enable_reg && !cap_10bit_tag_supported) begin
            $error("SR-IOV Control: 10-bit tag enabled without capability support");
        end
        if (vf_14bit_tag_enable_reg && !cap_14bit_tag_supported) begin
            $error("SR-IOV Control: 14-bit tag enabled without capability support");
        end
        
        // Check non-posted request restriction
        if (has_outstanding_nonposted_requests && 
            (vf_10bit_tag_enable_reg != $past(vf_10bit_tag_enable_reg) ||
             vf_14bit_tag_enable_reg != $past(vf_14bit_tag_enable_reg))) begin
            $error("SR-IOV Control: Tag enables modified with outstanding non-posted requests");
        end
    end
    // synthesis translate_on

endmodule