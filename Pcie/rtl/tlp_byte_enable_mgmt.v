// Separate Byte Enable Module
module tlp_byte_enable_mgmt (
    input  wire [9:0]           tlp_length,        // TLP Length field (10 bits)
    input  wire [3:0]           first_be,          // First DW Byte Enable
    input  wire [3:0]           last_be,           // Last DW Byte Enable
    input  wire                 is_qword_aligned,  // QW alignment indicator
    input  wire [4:0]           tlp_type,          // TLP Type field
    input  wire                 is_write_request,  // Indicates if this is a write request
    
    output wire                 is_be_valid,       // Byte Enable validity
    output wire [31:0]          enabled_bytes,     // Enabled bytes mask
    output wire [7:0]           be_byte_7          // Byte 7 containing BE fields
);

    // Internal signals
    reg [3:0] first_dw_be;
    reg [3:0] last_dw_be;
    reg be_valid_internal;
    
    // Basic BE validation
    always @* begin
        first_dw_be = first_be;
        last_dw_be = last_be;
        be_valid_internal = 1'b1;
        
        // 1 DW request handling
        if (tlp_length == 10'h1) begin
            // Last BE must be 0000b for 1 DW
            if (last_be != 4'h0) begin
                be_valid_internal = 1'b0;
            end
            // Allow zero first_be only for write requests
            if (first_be == 4'h0 && !is_write_request) begin
                be_valid_internal = 1'b0;
            end
        end
        // Multi DW request handling
        else if (tlp_length > 10'h1) begin
            // Neither BE field can be 0000b for >1 DW
            if (first_be == 4'h0 || last_be == 4'h0) begin
                be_valid_internal = 1'b0;
            end
            
            // Handle QW aligned special cases
            if (is_qword_aligned && tlp_length == 10'h2) begin
                // Allow non-contiguous patterns for QW aligned
                case (first_be)
                    4'b1010, 4'b0101, 4'b1001, 4'b1011, 4'b1101: begin
                        be_valid_internal = 1'b1;
                    end
                endcase
            end 
            // Non-QW aligned must have contiguous bytes
            else if (!is_qword_aligned && (tlp_length == 10'h2 || tlp_length >= 10'h3)) begin
                // Check first_be contiguity
                if ((first_be & (first_be + 1)) != first_be) begin
                    be_valid_internal = 1'b0;
                end
                // Check last_be contiguity
                if ((last_be & (last_be + 1)) != last_be) begin
                    be_valid_internal = 1'b0;
                end
            end
        end
    end

    // Generate byte 7 containing both BE fields
    assign be_byte_7 = {last_dw_be, first_dw_be};

    // Generate enabled_bytes mask
    genvar i;
    generate
        // First DW bytes
        for (i = 0; i < 4; i = i + 1) begin : gen_first_dw_mask
            assign enabled_bytes[i] = first_dw_be[i];
        end
        // Middle bytes (all enabled for requests > 2 DW)
        for (i = 4; i < 28; i = i + 1) begin : gen_middle_bytes
            assign enabled_bytes[i] = (tlp_length > 10'h2) ? 1'b1 : 1'b0;
        end
        // Last DW bytes
        for (i = 0; i < 4; i = i + 1) begin : gen_last_dw_mask
            assign enabled_bytes[28+i] = last_dw_be[i];
        end
    endgenerate

    // Special case: Write request with length=1 and no bytes enabled is allowed
    wire write_no_be_exception;
    assign write_no_be_exception = (tlp_length == 10'h1) && 
                                 (first_be == 4'h0) && 
                                 is_write_request;

    // Final BE validity
    assign is_be_valid = be_valid_internal || write_no_be_exception;

endmodule
