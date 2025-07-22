// Property with clock and frequency parameters
property clk_freq_check(clk, real freq_mhz);
    time curr_time;
    time expected_period;
    @(posedge clk)
    (1, curr_time = $time, expected_period = 1000ns / freq_mhz)  // Convert MHz to period
    ##1
    (($time - curr_time) == expected_period);
endproperty

// Assertions with frequency parameters
check_clk1_100mhz: assert property(clk_freq_check(clk1, 100.0));   // 100MHz
check_clk2_10mhz:  assert property(clk_freq_check(clk2, 10.0));    // 10MHz
check_clk3_90mhz:  assert property(clk_freq_check(clk3, 90.0));    // 90MHz
check_clk4_1000mhz: assert property(clk_freq_check(clk4, 1000.0)); // 1000MHz
