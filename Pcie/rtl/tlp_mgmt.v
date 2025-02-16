module tlp_module #(
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
    
    always @* begin
        if (ari_enabled) begin
            // ARI mode: 8-bit bus number + 8-bit function number
            tlp_hdr_requester_id[15:8] = bus_num;
            tlp_hdr_requester_id[7:0] = ari_fnc_num;
        end else begin
            // Non-ARI mode: 8-bit bus number + 5-bit device number + 3-bit function number
            tlp_hdr_requester_id[15:8] = bus_num;
            tlp_hdr_requester_id[7:3] = device_num;
            tlp_hdr_requester_id[2:0] = fnc_num;
        end
    end

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
            end 

            MRW: begin 
                assign tlp_hdr_dw = 8'b0000xxxx; 
                assign tlp_hdr_attr = {ordering, snoop_bit}; 
                assign tlp_hdr_lth = length; 
                assign tlp_hdr_tff_cls = 3{tff_cls}; 
                assign tlp_hdr_addr_lo = {30'b(addr),2'b00}; 
                assign tlp_hdr_addr_hi = {addr[64-1:32]}; 
                assign tlp_hdr_td = td; 
                assign tlp_hdr_ep = ep;  
                assign tlp_hdr_fmt = pkt_fmt; 
            end 

            CFGRQ0: begin 
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
                assign tlp_hdr_dw = 8'b0000xxxx; 
                assign tlp_hdr_attr = 2'b00; 
                assign tlp_hdr_lth = length; 
                assign tlp_hdr_tff_cls = 3'b0;
                assign tlp_hdr_td = td; 
                assign tlp_hdr_ep = ep;  
                assign tlp_hdr_fmt = 1'b0;
                assign tlp_hdr_type = 3'b001; 
            end 

            MSG: begin 
                assign tlp_hdr_dw = 8'b000000001; 
                assign tlp_hdr_attr = 2'b00; 
                assign tlp_hdr_lth = 10'b0; 
                assign tlp_hdr_tff_cls = 3'b0;
                assign tlp_hdr_td = td; 
                assign tlp_hdr_ep = ep;  
                assign tlp_hdr_fmt = 1'b0;
                assign tlp_hdr_type = 5'b10000; 
            end 

            PM_Active_State_Nak: begin
                assign tlp_hdr_dw = 8'b000000001; 
                assign tlp_hdr_attr = 2'b00; 
                assign tlp_hdr_lth = 10'bxxxxxxxxxx;  
                assign tlp_hdr_tff_cls = 3'b0; 
                assign tlp_hdr_td = td; 
                assign tlp_hdr_ep = ep;  
                assign tlp_hdr_fmt = 1'b0;
                assign tlp_hdr_type = 5'b10000; 
            end 
        endcase 
    end 
    always_comb begin 
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

    function automatic is_tag_supported;
        input [9:0] tag_value;
        begin
            is_tag_supported = SUPPORT_10BIT_TAG ? 1'b1 : (tag_value[9:8] == 2'b00);
        end
    endfunction

endmodule