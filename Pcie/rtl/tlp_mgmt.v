module tlp_module #(
    parameter SUPPORT_10BIT_TAG = 0  // 0: 8-bit tag only, 1: 10-bit tag support
)
(
    input  wire                  clk,
    input  wire                  rst,
    
    // Byte 0-1: Format, Type, and control bits
    input  wire  [2:0]           tlp_fmt,
    input  wire  [4:0]           tlp_type,
    input  wire                  th,
    input  wire  [2:0]           tlp_TC,
    input  wire                  tlp_T9,
    input  wire                  tlp_T8,
    input  wire                  tlp_TD,
    input  wire                  tlp_EP,
    input  wire  [1:0]           tlp_Attr,      // Attr[1:0]
    input  wire                  tlp_A2,        // Attr[2]
    input  wire  [1:0]           tlp_AT,
    input  wire  [9:0]           tlp_length,
    
    input  wire  [15:0]          requester_id,  // For Requests
    input  wire  [15:0]          completer_id,  // For Completions
    
    input  wire  [9:0]           tlp_tag,       // 10-bit tag (or [7:0] for 8-bit)
    input  wire  [3:0]           first_dw_be,   // First DW Byte Enable
    input  wire  [3:0]           last_dw_be,    // Last DW Byte Enable
    
    // Address 
    input  wire  [63:0]          tlp_address,
    input  wire  [1:0]           tlp_ph,        // Processing Hint
    
    input  wire  [2:0]           cpl_status,    // Completion Status
    input  wire                  bcm,           // Byte Count Modified
    input  wire  [11:0]          byte_count,    // Byte Count
    input  wire  [6:0]           lower_addr,    // Lower Address for Completions
    
    input  wire  [7:0]           msg_code,      // Message Code
    input  wire  [5:0]           reg_num,       // Register Number
    input  wire  [3:0]           ext_reg_num,   // Extended Register Number
    input  wire  [31:0]          data_dw,       // Data payload (for writes)
    
    // **Prefix fields (if TPH/PASID support needed)**
    input  wire                  prefix_present,
    input  wire  [31:0]          prefix_data,
    
    // ARI support
    input  wire                  ari_enabled,
    input  wire  [7:0]           bus_num,
    input  wire  [4:0]           device_num,
    input  wire  [2:0]           fnc_num,
    input  wire  [7:0]           ari_fnc_num
);
/*module tlp_module #(
    parameter SUPPORT_10BIT_TAG = 0  // 0: 8-bit tag only, 1: 10-bit tag support
)
(
    input  wire                  clk,           // Clock input
    input  wire                  rst,           // Reset input
    input  wire  [2:0]           tlp_fmt,      // TLP Format field (3 bits)
    input  wire  [4:0]           tlp_type,     // TLP Type field (5 bits)
    input  wire                  th,           // TH bit (1 bit)
    input  wire                  R,            // R bit (1 bit)
    input  wire                  tlp_A2,       // TLP A2 bit (1 bit)
    input  wire                  tlp_T8,       // TLP T8 bit (1 bit)
    input  wire  [2:0]           tlp_TC,       // TLP TC field (3 bits)
    input  wire                  tlp_T9,       // TLP T9 bit (1 bit)
    input  wire                  tlp_TD,       // TLP TD bit (1 bit)
    input  wire                  tlp_EP,       // TLP EP bit (1 bit)
    input  wire  [1:0]           tlp_Attr,     // TLP Attribute field (2 bits)
    input  wire  [1:0]           tlp_AT, 
    input  wire  [9:0]           tlp_length,   // TLP Length field (10 bits)
    input  wire  [63:0]          tlp_address,  // TLP Upper Address field (64 bits)
    input  wire  [9:0]           tlp_tag    , 
    input  wire                  ari_enabled,   // ARI enable signal
    input  wire  [7:0]           bus_num,      // Bus number
    input  wire  [4:0]           device_num,   // Device number (used in non-ARI mode)
    input  wire  [2:0]           fnc_num,      // Function number (used in non-ARI mode)
    input  wire  [7:0]           ari_fnc_num   // ARI Function number (used in ARI mode)
);
*/ 
    wire td; 
    wire ep; 

    reg is_memory_read;
    reg is_memory_read_locked;
    reg is_io_read;
    reg is_io_write;
    reg is_config_read_type0;
    reg is_config_write_type0;
    reg is_deprecated;
    reg is_message_request;
    reg is_message_data_load;
    reg is_completion_request;
    reg is_completion_data_request;
    reg is_end_to_end_tlp;
    reg is_completion_locked_memory;
    reg is_completion_locked_memory_data;
    reg is_fetch_and_add_request;
    reg is_unconditional_swap_request;
    reg is_compare_and_swap_request;
    reg is_local_tlp;

    // Requester ID generation based on ARI mode
    wire [15:0] tlp_hdr_requester_id;

    // Requester ID with ARI (Alternative Routing-ID Interpretation) support
    assign tlp_hdr_requester_id[15:8] = bus_num;                             // Bus Number always [15:8]
    assign tlp_hdr_requester_id[7:0]  = ari_enabled ? 
                                        ari_fnc_num :                         // ARI: 8-bit Function Number
                                        {device_num, fnc_num};                // Non-ARI: 5-bit Device + 3-bit Function
    reg tag_valid;
    wire [9:0] validated_tag;
    
    always @* begin
        tag_valid = 1'b1;
        
        if (!SUPPORT_10BIT_TAG) begin
            // For 8-bit tag support only, bits [9:8] must be 00
            if (tag[9:8] != 2'b00) begin
                tag_valid = 1'b0;
            end
        end
    end

    // Assign validated tag based on support
    assign validated_tag = SUPPORT_10BIT_TAG ? tag : {2'b00, tag[7:0]};
    assign tag_error = !tag_valid;

     tlp_byte_enable_mgmt be_mgmt (
        .tlp_length(tlp_length),
        .first_be(first_be),
        .last_be(last_be),
        .is_qword_aligned(is_qword_aligned),
        .tlp_type(tlp_type),
        .is_write_request(is_write_request),
        .is_be_valid(is_be_valid),
        .enabled_bytes(enabled_bytes),
        .be_byte_7(be_byte_7)
    );

    // TLP decoder instantiation
    tlp_fmt_decoder tlp_decoder_inst (
        .tlp_fmt(tlp_fmt),
        .tlp_type(tlp_type),
        .is_memory_read(is_memory_read),
        .is_memory_read_locked(is_memory_read_locked),
        .is_io_read(is_io_read),
        .is_io_write(is_io_write),
        .is_config_read_type0(is_config_read_type0),
        .is_config_write_type0(is_config_write_type0),
        .is_deprecated(is_deprecated),
        .is_message_request(is_message_request),
        .is_message_data_load(is_message_data_load),
        .is_completion_request(is_completion_request),
        .is_completion_data_request(is_completion_data_request),
        .is_completion_locked_memory(is_completion_locked_memory),
        .is_completion_locked_memory_data(is_completion_locked_memory_data),
        .is_fetch_and_add_request(is_fetch_and_add_request),
        .is_unconditional_swap_request(is_unconditional_swap_request),
        .is_compare_and_swap_request(is_compare_and_swap_request),
        .is_local_tlp(is_local_tlp),
        .is_end_to_end_tlp(is_end_to_end_tlp)
    );

    reg [61:0] tlp_add_r;
    always @* begin
        for(int i = 0; i < 62; i=i+1) begin 
            tlp_add_r[i+0] = tlp_address[64-1-i]; 
        end 
    end 

    always_comb begin 
        case(tlp_kind) 
            IOREQ: begin 
                /*
                assign tlp_hdr_dw = 8'b0000xxxx; 
                assign tlp_hdr_attr = 3'bx00; 
                assign tlp_hdr_lth = 9'b000000001; 
                assign tlp_hdr_tff_cls = 3'b0; 
                // Use generated requester_id
                assign tlp_hdr_addr = {30'b(tlp_addr_r),2'b00}; // Need only 30 bits. 
                assign tlp_hdr_td = td; 
                assign tlp_hdr_ep = ep;  
                assign tlp_hdr_fmt = pkt_fmt; 
                assign tlp_hdr_tc = 2'b00; 
                */ 
                            // IO Request (Read/Write) TLP header assignments
                assign tlp_hdr_fmt = pkt_fmt;                         // 2'b00 (3DW no data) or 2'b10 (3DW with data)
                assign tlp_hdr_type = is_io_read ? 5'b00010 : 5'b00011; // IO Read or IO Write
                assign tlp_hdr_tc = 3'b000;                           // Traffic Class (3 bits, not 2)
                assign tlp_hdr_attr = 3'b000;                         // Attributes (3 bits: Attr[2], LN, Attr[0])
                assign tlp_hdr_th = 1'b0;                             // TLP Hint
                assign tlp_hdr_td = td;                               // TLP Digest
                assign tlp_hdr_ep = ep;                               // Poisoned bit
                assign tlp_hdr_attr2 = 2'b00;                         // Attr[2:1]
                assign tlp_hdr_at = 2'b00;                            // Address Type
                assign tlp_hdr_length = 10'b0000000001;               // Length is 10 bits, always 1 DW for IO
                
                // DW1: Requester ID, Tag, Byte Enables
                assign tlp_hdr_req_id = requester_id;                 // 16-bit Requester ID
                assign tlp_hdr_tag = tag[7:0];                        // 8-bit Tag
                assign tlp_hdr_first_be = first_dw_be;                // 4-bit First DW Byte Enable
                assign tlp_hdr_last_be = 4'b0000;                     // Last BE = 0 for single DW
                
                // DW2: Address (32-bit aligned)
                assign tlp_hdr_addr = {tlp_addr_r[31:2], 2'b00};      // 32-bit IO address, bits [1:0] = 00
                
                // DW3: Data (only for IO Write)
                assign tlp_hdr_dw = data_dw;                          // 32-bit data for IO Write
            end 



            MRW: begin
                /*
                assign tlp_hdr_dw = 8'b0000xxxx; 
                assign tlp_hdr_attr = {ordering, snoop_bit}; 
                assign tlp_hdr_lth = length; 
                assign tlp_hdr_tff_cls = 3{tff_cls}; 
                assign tlp_hdr_addr_lo = {30'b(addr),2'b00}; 
                assign tlp_hdr_addr_hi = {addr[64-1:32]}; 
                assign tlp_hdr_td = td; 
                assign tlp_hdr_ep = ep;  
                assign tlp_hdr_fmt = pkt_fmt; 
                */ 
                // Memory Read/Write TLP header assignments
                assign tlp_hdr_fmt = pkt_fmt;                         // 3-bit: 3'b010 (3DW+data), 3'b011 (4DW+data), 3'b000 (3DW no data), 3'b001 (4DW no data)
                assign tlp_hdr_type = 5'b00000;                       // Memory Read/Write type
                assign tlp_hdr_tc = tff_cls;                          // 3-bit Traffic Class (was incorrectly replicated)
                assign tlp_hdr_attr = 3'b000;                         // 3-bit Attributes
                assign tlp_hdr_th = 1'b0;                             // TLP Processing Hint
                assign tlp_hdr_td = td;                               // TLP Digest present
                assign tlp_hdr_ep = ep;                               // Poisoned data
                assign tlp_hdr_attr2 = {ordering, snoop_bit};         // Attr[2:1] - Relaxed Ordering, No Snoop
                assign tlp_hdr_at = 2'b00;                            // Address Type (untranslated)
                assign tlp_hdr_length = length;                       // 10-bit length in DW
                
                // Requester ID, Tag, Byte Enables (DW1)
                assign tlp_hdr_req_id = requester_id;                 // 16-bit Requester ID
                assign tlp_hdr_tag = tag;                             // 8-bit Tag
                assign tlp_hdr_first_be = first_dw_be;                // 4-bit First DW Byte Enable
                assign tlp_hdr_last_be = last_dw_be;                  // 4-bit Last DW Byte Enable
                
                // Address fields (DW2 for 32-bit, DW2-DW3 for 64-bit)
                assign tlp_hdr_addr_lo = {addr[31:2], 2'b00};         // 32-bit: bits [31:2] of address, [1:0] = 00
                assign tlp_hdr_addr_hi = (pkt_fmt[0]) ? addr[63:32] : 32'h0;  // 64-bit: upper 32 bits (if 4DW format)
                
                // Data payload (for writes)
                assign tlp_hdr_data = write_data;                     // Data payload for Memory Write
            end 

            CFGRQ0: begin 
                /*
                assign tlp_hdr_dw = 8'b0000xxxx; 
                assign tlp_hdr_attr = 2'b00; 
                assign tlp_hdr_lth = length; 
                assign tlp_hdr_tff_cls = 3'b0;
                assign tlp_hdr_addr_lo = {30'b(addr),2'b00}; 
                assign tlp_hdr_addr_hi = {addr[64-1:32]}; 
                assign tlp_hdr_td = td; 
                assign tlp_hdr_ep = ep;  
                assign tlp_hdr_fmt = pkt_fmt;
                assign tlp_hdr_type = 3'b000; 
                assign tlp_cfg_reg = reg_num; 
                assign tlp_cfg_ext_reg = reg_ext_num; 
                assign tlp_hdr_fmt = pkt_fmt;              // 2'b00 for 3DW, no data
                */ 
                assign tlp_hdr_type = 5'b00100;            // CfgRd0 or appropriate type
                assign tlp_hdr_tff_cls = 3'b000;                // Traffic Class
                assign tlp_hdr_attr = 3'b000;              // Attributes (LN=0, TH=0, Attr[0])
                assign tlp_hdr_th = 1'b0;                  // Reserved for Config
                assign tlp_hdr_td = 1'b0;                  // No TLP digest typically
                assign tlp_hdr_ep = 1'b0;                  // No poisoning
                assign tlp_hdr_attr2 = 2'b00;              // Attr[2:1]
                assign tlp_hdr_at = 2'b00;                 // Address Type
                assign tlp_hdr_length = 10'b0000000001;    // 1 DW length
                
                // Config-specific fields
                assign tlp_hdr_req_id = requester_id;      // 16-bit Requester ID
                assign tlp_hdr_tag = tag;                  // 8-bit tag
                assign tlp_hdr_be = 4'b1111;               // Byte enables
                assign tlp_hdr_bus = bus_num;              // 8-bit bus number
                assign tlp_hdr_dev = dev_num;              // 5-bit device number
                assign tlp_hdr_func = func_num;            // 3-bit function number
                assign tlp_hdr_reg = reg_num[5:0];         // 6-bit register number
                assign tlp_hdr_ext_reg = reg_ext_num[3:0]; // 4-bit extended register
                assign tlp_hdr_dw = data_dw;               // 32-bit data (for writes)
            end 

            CFGRQ1: begin 
                assign tlp_hdr_dw = 8'b0000xxxx; 
                assign tlp_hdr_attr = 2'b00; 
                assign tlp_hdr_lth = length; 
                assign tlp_hdr_tff_cls = 3'b0;
                assign tlp_hdr_addr_lo = {30'b(addr),2'b00}; 
                assign tlp_hdr_addr_hi = {addr[64-1:32]}; 
                assign tlp_hdr_td = td; 
                assign tlp_hdr_ep = ep;  
                assign tlp_hdr_fmt = pkt_fmt;
                assign tlp_hdr_type = 3'b001; 
            end 

            CMPL: begin 
                /*
                assign tlp_hdr_dw = 8'b0000xxxx; 
                assign tlp_hdr_attr = 2'b00; 
                assign tlp_hdr_lth = length; 
                assign tlp_hdr_tff_cls = 3'b0;
                assign tlp_hdr_td = td; 
                assign tlp_hdr_ep = ep;  
                assign tlp_hdr_fmt = 1'b0;
                assign tlp_hdr_type = 3'b001; 
                */ 
                // Completion TLP header assignments
                assign tlp_hdr_fmt = has_data ? 3'b010 : 3'b000;      // 3DW with data or 3DW without data
                assign tlp_hdr_type = 5'b01010;                       // Completion type (CplD if data, Cpl if no data)
                assign tlp_hdr_tc = 3'b000;                           // Traffic Class
                assign tlp_hdr_attr = 3'b000;                         // Attributes (bit 2, LN, TH)
                assign tlp_hdr_th = 1'b0;                             // TLP Hint
                assign tlp_hdr_td = 1'b0;                             // TLP Digest
                assign tlp_hdr_ep = 1'b0;                             // Poisoned
                assign tlp_hdr_attr2 = 2'b00;                         // Attr[2:1]
                assign tlp_hdr_at = 2'b00;                            // Address Type
                assign tlp_hdr_length = length;                       // 10-bit length in DW
                
                // Completion-specific fields (DW1)
                assign tlp_hdr_cmpl_id = completer_id;                // 16-bit Completer ID
                assign tlp_hdr_cmpl_status = compl_status;            // 3-bit Completion Status
                assign tlp_hdr_bcm = byte_count_modified;             // BCM bit
                assign tlp_hdr_byte_count = byte_count;               // 12-bit Byte Count
                
                // DW2 fields
                assign tlp_hdr_req_id = requester_id;                 // 16-bit Requester ID
                assign tlp_hdr_tag = tag;                             // 8-bit Tag
                assign tlp_hdr_lower_addr = lower_addr[6:0];          // 7-bit Lower Address
            end 

            MSG: begin 
                /*
                assign tlp_hdr_dw = 8'b000000001; 
                assign tlp_hdr_attr = 2'b00; 
                assign tlp_hdr_lth = 10'b0; 
                assign tlp_hdr_tff_cls = 3'b0;
                assign tlp_hdr_td = td; 
                assign tlp_hdr_ep = ep;  
                assign tlp_hdr_fmt = 1'b0;
                assign tlp_hdr_type = 5'b10000; 
                */
                // Message TLP header assignments
                assign tlp_hdr_fmt = has_data ? 3'b011 : 3'b001;      // 3-bit: 3'b011 (4DW+data), 3'b001 (4DW no data)
                assign tlp_hdr_type = {2'b10, msg_routing};           // 5-bit: 2'b10 + 3-bit message routing
                assign tlp_hdr_tc = 3'b000;                           // 3-bit Traffic Class
                assign tlp_hdr_attr = 3'b000;                         // 3-bit Attributes
                assign tlp_hdr_th = 1'b0;                             // TLP Processing Hint
                assign tlp_hdr_td = td;                               // TLP Digest present
                assign tlp_hdr_ep = ep;                               // Poisoned data
                assign tlp_hdr_attr2 = 2'b00;                         // Attr[2:1]
                assign tlp_hdr_at = 2'b00;                            // Address Type
                assign tlp_hdr_length = length;                       // 10-bit length in DW (0 for no data, >0 for data)
                
                // Requester ID, Tag, Message Code (DW1)
                assign tlp_hdr_req_id = requester_id;                 // 16-bit Requester ID
                assign tlp_hdr_tag = tag;                             // 8-bit Tag
                assign tlp_hdr_msg_code = message_code;               // 8-bit Message Code
                
                // Lower/Upper Address or other fields (DW2-DW3)
                assign tlp_hdr_addr_lo = lower_addr;                  // 32-bit Lower Address
                assign tlp_hdr_addr_hi = upper_addr;                  // 32-bit Upper Address
                
                // Data payload (for messages with data)
                assign tlp_hdr_data = msg_data;                       // Message data payload
            end 

            PM_Active_State_Nak: begin
                /*
                assign tlp_hdr_dw = 8'b000000001; 
                assign tlp_hdr_attr = 2'b00; 
                assign tlp_hdr_lth = 10'bxxxxxxxxxx;  
                assign tlp_hdr_tff_cls = 3'b0; 
                assign tlp_hdr_td = td; 
                assign tlp_hdr_ep = ep;  
                assign tlp_hdr_fmt = 1'b0;
                assign tlp_hdr_type = 5'b10000; 
                */ 
                // PM_Active_State_Nak Message TLP header assignments
                assign tlp_hdr_fmt = 3'b001;                          // 3-bit: 4DW header, no data
                assign tlp_hdr_type = 5'b10100;                       // 5-bit: Message type with Local routing (2'b10 + 3'b100)
                assign tlp_hdr_tc = 3'b000;                           // 3-bit Traffic Class
                assign tlp_hdr_attr = 3'b000;                         // 3-bit Attributes
                assign tlp_hdr_th = 1'b0;                             // TLP Processing Hint
                assign tlp_hdr_td = td;                               // TLP Digest present
                assign tlp_hdr_ep = ep;                               // Poisoned data
                assign tlp_hdr_attr2 = 2'b00;                         // Attr[2:1]
                assign tlp_hdr_at = 2'b00;                            // Address Type
                assign tlp_hdr_length = 10'b0000000000;               // 0 DW - no data payload
                
                // Requester ID, Tag, Message Code (DW1)
                assign tlp_hdr_req_id = requester_id;                 // 16-bit Requester ID
                assign tlp_hdr_tag = 8'h00;                           // 8-bit Tag (typically 0 for PM messages)
                assign tlp_hdr_msg_code = 8'h14;                      // 8-bit Message Code: 0x14 for PM_Active_State_Nak
                
                // Address fields (DW2-DW3) - Reserved for this message
                assign tlp_hdr_addr_lo = 32'h00000000;                // Reserved
                assign tlp_hdr_addr_hi = 32'h00000000;                // Reserved
            end 
        endcase 
    end 
    
    /*always_comb begin 
    case(tlp_fmt)
        2'b01: begin 
            assign tlp_hdr_addr_lo = {30'b(addr),2'b00}; 
            assign tlp_hdr_addr_hi = {addr[64-1:32]}; 
        end  
        2'b00: begin 
            assign tlp_hdr_addr_lo = {30'b(addr),2'b00}; 
        end  
    endcase 
    end  

    case(status_code) 
        3'b000: assign completion_success = 1; 
        3'b001: assign completion_success = 0; 
        3'b010: assign config_re_entry = 1; 
        default: assign status_code = 0; 
    endcase 
*/ 

    always_comb begin
    // Default assignments
    tlp_hdr_addr_lo = 32'h0;
    tlp_hdr_addr_hi = 32'h0;
    completion_success = 1'b0;
    config_re_entry = 1'b0;
    
    // Address assignment based on format
    case(tlp_fmt)
        2'b01: begin  // 4DW addressing (64-bit)
            tlp_hdr_addr_lo = {addr[31:2], 2'b00};
            tlp_hdr_addr_hi = addr[63:32];
        end
        2'b00: begin  // 3DW addressing (32-bit)
            tlp_hdr_addr_lo = {addr[31:2], 2'b00};
            tlp_hdr_addr_hi = 32'h0;
        end
        default: begin
            tlp_hdr_addr_lo = 32'h0;
            tlp_hdr_addr_hi = 32'h0;
        end
    endcase
    
    // Completion status decode
    case(status_code)
        3'b000: begin  // Successful Completion (SC)
            completion_success = 1'b1;
            config_re_entry = 1'b0;
        end
        3'b001: begin  // Unsupported Request (UR)
            completion_success = 1'b0;
            config_re_entry = 1'b0;
        end
        3'b010: begin  // Configuration Request Retry Status (CRS)
            completion_success = 1'b0;
            config_re_entry = 1'b1;
        end
        default: begin
            completion_success = 1'b0;
            config_re_entry = 1'b0;
        end
    endcase
  end
    
    function automatic is_tag_supported;
        input [9:0] tag_value;
        begin
            is_tag_supported = SUPPORT_10BIT_TAG ? 1'b1 : (tag_value[9:8] == 2'b00);
        end
    endfunction

endmodule
