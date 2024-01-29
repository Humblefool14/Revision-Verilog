
wire td; 
wire ep; 

// NFM ---> Non Flit Mode 
// FM ---> Flit mode. 

always_comb begin 
case(tlp_kind) 
    IOREQ: begin 
    assign tlp_hdr_dw                       = 8'b0000xxxx; 
    assign tlp_hdr_attr                     = 2'b00; 
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
    end 
    MRW:  begin 
    assign tlp_hdr_dw                       = 8'b0000xxxx; 
    assign tlp_hdr_attr                     = {ordering, snoop_bit}; 
    assign tlp_hdr_lth                      = length; 
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
endcase 
end 