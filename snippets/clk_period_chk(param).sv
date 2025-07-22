// Property with clock and period parameters
property clk_period_check(clk, time_period);
    time curr_time;
    @(posedge clk)
    (1, curr_time = $time)
    ##1
    (($time - curr_time) == time_period);
endproperty

// Assertions for different clocks
check_clk1_100mhz: assert property(clk_period_check(clk1, 10ns));    // 100MHz
check_clk2_10mhz:  assert property(clk_period_check(clk2, 100ns));   // 10MHz  
check_clk3_90mhz:  assert property(clk_period_check(clk3, 11.11ns)); // 90MHz
check_clk4_1000mhz: assert property(clk_period_check(clk4, 1ns));    // 1000MHz
