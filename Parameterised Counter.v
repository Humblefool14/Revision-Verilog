// N bit counter 
module counter(clear,clk,count);
   input clk,clear;
   output reg[0:N] count;
   paramter N =7;
   always@(negedge clk)
       begin
          if(clear)
                count <=0;
          else
                count <= count+1;
       end
endmodule
