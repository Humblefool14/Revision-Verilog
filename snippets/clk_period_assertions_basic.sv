property clk_period;
    time curr_time;                    // Local variable to store timestamp
    @(posedge clk1)                   // Trigger on positive edge of clk1
    (1, curr_time = $time)            // Action: store current simulation time
    ##1                               // Wait exactly 1 clock cycle
    (($time - curr_time) == 10ns);    // Check: time difference equals 10ns
endproperty

