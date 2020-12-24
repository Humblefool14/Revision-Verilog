module adder(a,b,c); //DUT code start 
input [15:0] a; 
input [15:0] b; 
output [16:0] c; 

assign c = a + b; 

endmodule //DUT code end 

module top(); //TestBench code start 
reg [15:0] a; 
reg [15:0] b; 
wire [16:0] c; 

adder DUT(a,b,c); //DUT Instantiation 

initial 
begin 
a = 16'h45; //apply the stimulus 
b = 16'h12; 
#10 $display(" a=%0d,b=%0d,c=%0d",a,b,c); 
//send the output to terminal for visual inspection 
end 
endmodule //TestBench code end 
