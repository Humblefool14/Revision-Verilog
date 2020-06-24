module sequential(curr_state,flag);
   input [0:1] curr_state;
   output reg[0:1] flag;
   always@(curr_state)
       begin
          case(curr_state)
            0,1 : flag =2;
            3   : flag =0;
          endcase 
       end
endmodule
