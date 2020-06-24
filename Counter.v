// 4 bit counter with Asynchronous reset
module counter(clk,rst,count);
   input clk,rst;
   output reg[3:0] count;

   always@(posedge clk or posedge rst)
       begin
          if(rst)
                count <=0;
          else
                count <= count+1;
       end
endmodule
