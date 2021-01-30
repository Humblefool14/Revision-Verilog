`timescale 1ns/1ps
module regfile_tb; 
    reg [31:0] Ip1; 
    reg [3:0] Sel_i1;
    reg [3:0] Sel_02;
    reg [3:0] Sel_o1; 
    wire [31:0] OP1;
    wire [31:0] OP2; 
    reg RD; 
    reg WR; 
    reg rst; 
    reg EN;
    reg clk; 
    
    regfile Dut(.*);
    initial begin 
        Ip1 = 32'b0; 
        Sel_i1 = 4'b0; 
        Sel_o2 = 4'b0;
        Sel_o1 = 4'b0; 
        RD = 1'b0; 
        WR = 1'b0; 
        EN = 1'b0; 
        rst = 1'b1; 
        clk = 1'b0; 

    #100; 
        
        // Stimulus written 
        rst = 1'b0; 
        EN = 1'b1;
        #20;
        WR = 1'b1; 
        RD = 1'b0; 
        IP1 = 32'habcd_efab; 
        Sel_i1 = 4'h0; 

        #20; 
        Ip1 = 32'h0123_4567; 
        Sel_i1 = 4'h1; 

        #20; 
        WR = 1'b0; 
        RD = 1'b1; 
        Sel_o1 = 4'h0; 
        Sel_o2 = 4'h1; 
    end 

    always begin 
        #10; 
        clk = ~clk; 
    end 
endmodule 
