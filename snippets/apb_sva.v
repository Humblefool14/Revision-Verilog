assert property (
    @(posedge apb_clk) disable iff (!apb_psel || !apb_pwrite) 
    apb_pready && apb_psel && apb_pwrite 
    |-> !apb_pslverr
) else $error("Invalid write operation detected!");

assert property (
    @(posedge apb_clk) disable iff (!apb_psel || apb_pwrite) 
    apb_pready && apb_psel && !apb_pwrite 
    |-> !apb_pslverr
) else $error("Invalid read operation detected!");

assert property (
    @(posedge apb_clk) disable iff (!apb_psel) 
    apb_paddr >= 0 && apb_paddr <= MAX_ADDRESS
) else $error("Invalid address range detected!");

assert property (
    @(posedge apb_clk) disable iff (!apb_psel) 
    (!apb_pwrite || $countones(apb_pwdata) <= DATA_WIDTH)
) else $error("Invalid data width detected!");

assert property (
    @(posedge apb_clk) disable iff (!apb_psel) 
    apb_psel |-> apb_pready
) else $error("PREADY not asserted when PSEL is high!");

// Assertion to check that the PREADY signal is de-asserted when the PSEL signal is de-asserted
assert property (
    @(posedge apb_clk) disable iff (apb_psel) 
    !apb_psel |-> !apb_pready
) else $error("PREADY not de-asserted when PSEL is low!");

// Assertion to check the validity of read data
assert property (
    @(posedge apb_clk) disable iff (!apb_psel || apb_pwrite) 
    apb_pready && apb_psel && !apb_pwrite 
    |-> $stable(apb_prdata)
) else $error("Unstable read data detected!");