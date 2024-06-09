module fsm(
    input clk; 
    input ack;
    input req; 
    output req_out; 
)
 
 reg state = 0; 
 reg next_state = 0; 

always @(posedge clk )
    state <= next_state; 

assign next_state = state ? ~ack : req; 
assign req_out = state; 


endmodule 