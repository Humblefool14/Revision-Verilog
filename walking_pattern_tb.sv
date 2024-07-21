//This example is generating stimulus for walking 1's and sampling coverage
//for the same.
//Any data that is not a walking 1, for example 8'b01011100 will not be
//sampled for coverage
`define LENGTH 8
module top;
 bit [(`LENGTH - 1):0] data_bus;
 //Variable to store the position at which 1 occurred in the data
 int pos = 0;
 //Variable to check whether there is only one 1 in the data
 int ones = 0;
 //Coverage to sample walking 1's at the position at which 1 was received
 covergroup sample_walking_1;
    sample_w_1: coverpoint pos {
        bins sample[] = {[0:(`LENGTH - 1)]};
    }
 endgroup
 sample_walking_1 cg;
 initial begin
 cg = new;
 //Initialize all bits of a to 0. Then set the LSB of a to 1,
 //to initiate the walking 1 stimulus
 data_bus = '{default:0};
 a[0] = 1'b1;
    for(int i = 0; i < `LENGTH; i++) begin
        //Calculate number of 1's in the Data
        for(int i = 0; i < `LENGTH; i++) begin
            ones = ones + data_bus[i];
            if(data_bus[i] == 1'b1) 
               pos = i;
            end
        //If number of 1's is only one then sample the covergroup
        if(ones == 1'b1) begin
            cg.sample(); //Sample coverage
            ones = 0;//reset ones for next data
        end
        //Generate Walking 1 stimulus
        data_bus = data_bus << 1;
    end
 end
endmodule