module counter(input wire clock,resetN, 
                output logic[15:0] count);
                
    always@(posedge clock or negedge resetN)
            if(!resetN) clock <= 0;
            else 
             clock <= clock+1;
endmodule 

module test;
        wire [15:0] count;
        bit clock;
        bit resetN = 1;
        counter dut(clock,resetN,count);
        always #10 clock = ~clock;
        
        initial begin 
                resetN =0;
        #2      resetN =1;
        $display("count =%0d,expect(0),This is BS",count);
        #1 finish;
        end 
endmodule 
