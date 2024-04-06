



assign trans_pending   = !hresp && !hready_out; 
assign trans_completed = !hresp  && hready_out; 
assign trans_err_cycle     =  hresp && !hready_out;
assign trans_err_cycles    =  hresp && hready_out; 

error_in_second_cycle : assert property @(posedge clk) disable iff (!rst_n) (hresp && hreadyout) |-> $error("Error occurred in the second cycle!");  
error_in_first_cycle  : assert property @(posedge clk) disable iff (!rst_n) (hresp && !hreadyout) |-> $error("Error occurred in the first cycle!");  