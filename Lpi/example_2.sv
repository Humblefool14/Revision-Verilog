task generator_good(int n);
    BusTran b; 
    repeat(n) begin 
        b = new(); 
        b.addr = $random(); 
        $display("Sending addr = %h",b.addr);
        transmit(p);
    end 
endtask
