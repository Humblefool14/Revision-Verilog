// SR-IOV Extended Capability Header
// Implements PCI Express Base Specification 6.0.1 Figure 9-11
module sriov_cap_header (
    // Inputs
    input wire        clk,
    input wire        rst_n,
    input wire [11:0] addr,     // Configuration space address
    input wire        wr_en,    // Write enable
    input wire [31:0] wr_data,  // Write data
    
    // Outputs
    output reg [31:0] rd_data,  // Read data
    
    // Next capability offset interface
    input  wire [11:0] next_cap_offset,  // Offset to next capability
    output wire        is_last_cap       // Indicates if this is the last capability
);

    // Constants
    localparam SRIOV_CAP_ID     = 16'h0010;  // SR-IOV Extended Capability ID
    localparam SRIOV_CAP_VER    = 4'h1;      // Version 1h as specified
    localparam MIN_OFFSET       = 12'h0FF;    // Minimum offset value when not last

    // Register bit positions
    localparam NEXT_CAP_POS     = 31;
    localparam NEXT_CAP_WIDTH   = 12;
    localparam CAP_VER_POS      = 16;
    localparam CAP_VER_WIDTH    = 4;
    localparam CAP_ID_POS       = 0;
    localparam CAP_ID_WIDTH     = 16;

    // Internal signals
    reg [11:0] next_cap_offset_reg;

    // Determine if this is the last capability
    assign is_last_cap = (next_cap_offset == 12'h000);

    // Read logic
    always @(*) begin
        rd_data = 32'h0;  // Default value
        
        rd_data[CAP_ID_POS +: CAP_ID_WIDTH] = SRIOV_CAP_ID;
        rd_data[CAP_VER_POS +: CAP_VER_WIDTH] = SRIOV_CAP_VER;
        rd_data[NEXT_CAP_POS -: NEXT_CAP_WIDTH] = next_cap_offset_reg;
    end

    // Next capability offset register logic
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            next_cap_offset_reg <= 12'h000;  // Reset to null terminator
        end else begin
            if (next_cap_offset == 12'h000) begin
                next_cap_offset_reg <= 12'h000;  // Terminating list
            end else begin
                // Ensure offset is >= 0FFh when not terminating
                next_cap_offset_reg <= (next_cap_offset < MIN_OFFSET) ? 
                                     MIN_OFFSET : next_cap_offset;
            end
        end
    end

    // Assertions
    // synthesis translate_off
    always @(posedge clk) begin
        if (!is_last_cap && next_cap_offset_reg < MIN_OFFSET) begin
            $error("SR-IOV Cap Header: Non-terminating offset must be >= 0FFh");
        end
    end
    // synthesis translate_on

endmodule