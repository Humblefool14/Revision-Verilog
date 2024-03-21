module tlp_module (
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
    input  wire  [9:0]           tlp_length,   // TLP Length field (10 bits)
    input  wire  [64:0]          tlp_address_hi // TLP Upper Address field (32 bits)
);
    // Implement your TLP module logic here
wire td; 
wire ep; 

reg is_memory_read            ; 
reg is_memory_read_locked     ; 
reg is_io_read                ; 
reg is_io_write               ; 
reg is_config_read_type0      ; 
reg is_config_write_type0     ; 
reg is_deprecated             ; 
reg is_message_request        ; 
reg is_message_data_load      ; 
reg is_completion_request     ; 
reg is_completion_data_request; 
reg is_end_to_end_tlp         ; 
reg is_completion_locked_memory; // Completion for locked memory without data request
reg is_completion_locked_memory_data; // Completion for locked memory with data request
reg is_fetch_and_add_request; // Fetch and Add request
reg is_unconditional_swap_request; // Unconditional Swap request
reg is_compare_and_swap_request; // Compare and Swap request
reg is_local_tlp;         // Local TLP request


    // Instantiate tlp_decoder module
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
endmodule



// • For any TLP, a value of 100b in the Fmt[2:0] field in byte 0 of the TLP indicates the presence of a TLP Prefix and the Type[4] bit indicates the type of TLP Prefix.
// • The format for bytes 1 through 3 of a TLP Prefix is defined by its TLP Prefix type.

always @* begin
if(tlp_fmt == 3'b100)begin 
    if(tlp_type[4]==1)begin
        tlp_type_ctxt <= END_END_TLP;
        // ◦ A value of 1b in the Type[4] bit indicates the presence of an End-End TLP Prefix
    end else begin 
         tlp_type_ctxt <= LCL_TLP; 
         //  A value of 0b in the Type[4] bit indicates the presence of a Local TLP Prefix
       end 
   end 
end


reg [61:0] tlp_add_r;
always @* begin
    // only if the tlp is of memory/io request. 
    for(int i =0; i < 62; i=i+1)begin 
        assign tlp_add_r[i+0]  = tlp_address_hi[64-1-i]; 
    end 
end 
// reversal of address. 



// NFM ---> Non Flit Mode 
// FM ---> Flit mode. 
//lth ---> length. 

// Any tlp shouldn't ask cross more than 4K boundary. 
always_comb begin 
case(tlp_kind) 
    IOREQ: begin 
    assign tlp_hdr_dw                       = 8'b0000xxxx; 
    assign tlp_hdr_attr                     = 3'bx00; 
    assign tlp_hdr_lth                      = 9'b000000001; 
    assign tlp_hdr_tff_cls                  = 3'b0; 
    assign tlp_hdr_requester_id[7+:0]       = 8{bus_num}; 
    assign tlp_hdr_requester_id[16-1:10]    = 5{device_num}; 
    assign tlp_hdr_requested_id[9:7]        = 3{fnc_num}; 
    assign tlp_hdr_addr                     = {30'b(addr),2'b00};
    assign tlp_hdr_td                       = td; 
    assign tlp_hdr_ep                       = ep;  
    assign tlp_hdr_fmt                      = pkt_fmt; 
    assign tlp_hdr_type                     = 
    assign tlp_hdr_tc                       = 2b'00; 
    end 

    MRW:  begin // Read requests // 
    assign tlp_hdr_dw                       = 8'b0000xxxx; 
    assign tlp_hdr_attr                     = {ordering, snoop_bit}; 
    assign tlp_hdr_lth                      = length; 
    //For Memory Read Requests, Length must not exceed the value specified by Max_Read_Request_Size
    assign tlp_hdr_tff_cls                  = 3{tff_cls}; 
    assign tlp_hdr_requester_id[7+:0]       = 8{bus_num}; 
    assign tlp_hdr_requester_id[16-1:10]    = 5{device_num}; 
    assign tlp_hdr_requested_id[9:7]        = 3{fnc_num}; 
    assign tlp_hdr_addr_lo                  = {30'b(addr),2'b00}; 
    assign tlp_hdr_addr_hi                  = {addr[64-1:32]}; 
    assign tlp_hdr_td                       = td; 
    assign tlp_hdr_ep                       = ep;  
    assign tlp_hdr_fmt                      = pkt_fmt; 
    end 
    CFGRQ0 : begin 
    assign tlp_hdr_dw                       = 8'b0000xxxx; 
    assign tlp_hdr_attr                     = 2'b00; 
    assign tlp_hdr_lth                      = length; 
    assign tlp_hdr_tff_cls                  = 3'b0; // Config requests
    assign tlp_hdr_requester_id[7+:0]       = 8{bus_num}; 
    assign tlp_hdr_requester_id[16-1:10]    = 5{device_num}; 
    assign tlp_hdr_requested_id[9:7]        = 3{fnc_num}; 
    assign tlp_hdr_addr_lo                  = {30'b(addr),2'b00}; 
    assign tlp_hdr_addr_hi                  = {addr[64-1:32]}; 
    assign tlp_hdr_td                       = td; 
    assign tlp_hdr_ep                       = ep;  
    assign tlp_hdr_fmt                      = pkt_fmt;  // 00 ---> Read No data sent // 1 --> Write request. 
    assign tlp_hdr_type                     = 000; 
    assign tlp_cfg_reg                      = reg_num; 
    assign tlp_cfg_ext_reg                  = reg_ext_num; 
    end 
    CFGRQ1 : begin 
    assign tlp_hdr_dw                       = 8'b0000xxxx; 
    assign tlp_hdr_attr                     = 2'b00; 
    assign tlp_hdr_lth                      = length; 
    assign tlp_hdr_tff_cls                  = 3'b0; // Config requests
    assign tlp_hdr_requester_id[7+:0]       = 8{bus_num}; 
    assign tlp_hdr_requester_id[16-1:10]    = 5{device_num}; 
    assign tlp_hdr_requested_id[9:7]        = 3{fnc_num}; 
    assign tlp_hdr_addr_lo                  = {30'b(addr),2'b00}; 
    assign tlp_hdr_addr_hi                  = {addr[64-1:32]}; 
    assign tlp_hdr_td                       = td; 
    assign tlp_hdr_ep                       = ep;  
    assign tlp_hdr_fmt                      = pkt_fmt;  // 00 ---> Read No data sent // 1 --> Write request. 
    assign tlp_hdr_type                     = 001; 
    end 
    CMPL:  begin 
    assign tlp_hdr_dw                       = 8'b0000xxxx; 
    assign tlp_hdr_attr                     = 2'b00; 
    assign tlp_hdr_lth                      = length; 
    assign tlp_hdr_tff_cls                  = 3'b0; // Config requests
    assign tlp_hdr_requester_id[7+:0]       = 8{bus_num}; 
    assign tlp_hdr_requester_id[16-1:10]    = 5{device_num}; 
    assign tlp_hdr_requested_id[9:7]        = 3{fnc_num}; 
    assign tlp_hdr_td                       = td; 
    assign tlp_hdr_ep                       = ep;  
    assign tlp_hdr_fmt                      = 0x0;  // x0 ---> Read No data sent // 1 --> Write request. 
    assign tlp_hdr_type                     = 001; 
    end 
    MSG:  begin 
    assign tlp_hdr_dw                       = 8'b000000001; 
    assign tlp_hdr_attr                     = 2'b00; 
    assign tlp_hdr_lth                      = 10'b{0}; 
    assign tlp_hdr_tff_cls                  = 3'b0; // Config requests
    assign tlp_hdr_requester_id[7+:0]       = 8{bus_num}; 
    assign tlp_hdr_requester_id[16-1:10]    = 5{device_num}; 
    assign tlp_hdr_requested_id[9:7]        = 3{fnc_num}; 
    assign tlp_hdr_td                       = td; 
    assign tlp_hdr_ep                       = ep;  
    assign tlp_hdr_fmt                      = 0x0;  // x0 ---> Read No data sent // 1 --> Write request. 
    assign tlp_hdr_type                     = 0x10000; 
    end 

    PM_Active_State_Nak: begin
        assign tlp_hdr_dw                       = 8'b000000001; 
        assign tlp_hdr_attr                     = 2'b00; 
        assign tlp_hdr_lth                      = 10'bxxxxxxxxxx;  
        assign tlp_hdr_tff_cls                  = 3'b0; 
        assign tlp_hdr_requester_id[7+:0]       = 8{bus_num}; 
        assign tlp_hdr_requester_id[16-1:10]    = 5{device_num}; 
        assign tlp_hdr_requested_id[9:7]        = 3{fnc_num}; 
        assign tlp_hdr_td                       = td; 
        assign tlp_hdr_ep                       = ep;  
        assign tlp_hdr_fmt                      = 0x0;  // x0 ---> Read No data sent // 1 --> Write request. 
        assign tlp_hdr_type                     = 0x10000; 

    end 
endcase 
end 


case(tlp_fmt) begin 
    0x1: begin 
    assign tlp_hdr_addr_lo                  = {30'b(addr),2'b00}; 
    assign tlp_hdr_addr_hi                  = {addr[64-1:32]}; 
    end  
    0x0: begin 
    assign tlp_hdr_addr_lo                  = {30'b(addr),2'b00}; 
    end  

    // Two address formats are specified, a 64-bit format used with a 4 DW header 
    // and a 32-bit format used with a 3 DW header 
  end 
endcase 


//completion header: 

case(status_code): 
    000: completion_success <= 1; 
    001: completion_success <= 0; 
    010: config_re_entry    <= 1; 
    default : status_code   <= 0; 
endcase 


// Otherwise, for an ARI Device, the Tx_MPS_Limit must be the MPS setting in Function 0. The MPS settings in other Functions of an MFD must be ignored. 

  endmodule 