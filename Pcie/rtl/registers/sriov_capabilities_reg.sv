// SR-IOV Capabilities Register
// Implements PCI Express Base Specification 6.0.1 Figure 9-12/Table 9-3
module sriov_capabilities_reg (
    // Inputs
    input wire        clk,
    input wire        rst_n,
    input wire [11:0] addr,     // Configuration space address
    input wire        wr_en,    // Write enable
    input wire [31:0] wr_data,  // Write data
    
    // Device Capabilities dependency inputs
    input wire        dev_cap2_10bit_tag_supported,
    input wire        dev_cap2_14bit_tag_supported,
    
    // Outputs
    output reg [31:0] rd_data,  // Read data
    output wire       vf_10bit_tag_support_enabled,
    output wire       vf_14bit_tag_support_enabled
);

    // Register bit positions
    localparam VF_MIGRATION_INT_NUM_POS = 21;
    localparam VF_MIGRATION_INT_NUM_WIDTH = 11;
    localparam RSVDP_POS = 4;
    localparam RSVDP_WIDTH = 17;
    
    // Internal registers for HwInit fields
    reg vf_10bit_tag_support;
    reg vf_14bit_tag_support;

    // Hardwired values as per spec
    wire vf_migration_capable = 1'b0;        // Deprecated, hardwired to 0
    wire ari_hierarchy_preserved = 1'b0;     // Must be 0 for FLIT
    wire [10:0] vf_migration_int_num = 11'd0;// Hardwired to 0 for new designs

    // Read logic
    always @(*) begin
        rd_data = 32'h0;  // Default value
        
        // Bit 0: VF Migration Capable (RO, hardwired to 0)
        rd_data[0] = vf_migration_capable;
        
        // Bit 1: ARI Capable Hierarchy Preserved (RO, hardwired to 0)
        rd_data[1] = ari_hierarchy_preserved;
        
        // Bit 2: VF 10-Bit Tag Requester Supported (HwInit)
        rd_data[2] = vf_10bit_tag_support;
        
        // Bit 3: VF 14-Bit Tag Requester Supported (HwInit)
        rd_data[3] = vf_14bit_tag_support;
        
        // Bits [20:4]: Reserved, Preserve
        rd_data[RSVDP_POS +: RSVDP_WIDTH] = 17'h0;
        
        // Bits [31:21]: VF Migration Interrupt Message Number (RO, hardwired to 0)
        rd_data[VF_MIGRATION_INT_NUM_POS +: VF_MIGRATION_INT_NUM_WIDTH] = vf_migration_int_num;
    end

    // HwInit fields initialization and dependency logic
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            vf_10bit_tag_support <= 1'b0;
            vf_14bit_tag_support <= 1'b0;
        end else begin
            // 10-bit Tag Support dependency
            if (!dev_cap2_10bit_tag_supported) begin
                vf_10bit_tag_support <= 1'b0;  // Must be clear if not supported in Device Cap 2
            end
            
            // 14-bit Tag Support dependency
            if (!dev_cap2_14bit_tag_supported) begin
                vf_14bit_tag_support <= 1'b0;  // Must be clear if not supported in Device Cap 2
            end
        end
    end

    // Output assignments for tag support status
    assign vf_10bit_tag_support_enabled = vf_10bit_tag_support;
    assign vf_14bit_tag_support_enabled = vf_14bit_tag_support;

    // Assertions
    // synthesis translate_off
    always @(posedge clk) begin
        // Check Device Capabilities 2 dependencies
        if (vf_10bit_tag_support && !dev_cap2_10bit_tag_supported) begin
            $error("SR-IOV Cap: 10-bit Tag Support enabled without Device Cap 2 support");
        end
        if (vf_14bit_tag_support && !dev_cap2_14bit_tag_supported) begin
            $error("SR-IOV Cap: 14-bit Tag Support enabled without Device Cap 2 support");
        end
    end
    // synthesis translate_on

endmodule