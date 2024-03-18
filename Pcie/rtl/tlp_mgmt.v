
wire td; 
wire ep; 

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