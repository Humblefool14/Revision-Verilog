module clk_generator(); 
parameter CLK_A_DELAY = 5; 
parameter CLK_B_DELAY = 8; 
    always begin 
        clk_a = 0; 
        #CLK_A_DELAY; 
        clk_a = 1; 
        #CLK_A_DELAY; 
    end 

    always begin 
        clk_b = 0; 
        #CLK_B_DELAY; 
        clk_b = 1; 
        #CLK_B_DELAY; 
    end 

endmodule 