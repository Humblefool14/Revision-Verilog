module ringcounter(init, clk,count);
	input init;
	input clk;
	output reg [7:0] count;
	
           always@(posedge clk)
		begin 
    			if(init) count= 8'b10000000;
          else begin
                      count <= count << 1;
                      count[0] <= count[7];
           			end 
		end
endmodule		
