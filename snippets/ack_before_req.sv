property p_ack_anytime_before_next_req;     
   @(posedge clk) disable iff(!rst_n)         
     ($rose(req)) |-> (s_eventually(ack) throughout (!req)); 
endproperty

