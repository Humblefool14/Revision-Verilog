property p_enable_feature_go_low_within_5_cycles;
    @(posedge clk) disable iff(!rst_n)
        // If enable_feature transitions from low to high ($rose(enable_feature))
        $rose(enable_feature) |->
        // Then, enable_feature must be low within 0 to 5 cycles after that initial high.
        // This sequence says: 0 to 4 cycles where enable_feature stays high,
        // followed by 1 cycle where enable_feature goes low.
        (enable_feature [*0:4] ##1 !enable_feature);
        // The [*0:4] allows it to go low immediately (0 cycles high after rose)
        // or stay high for 1, 2, 3, or 4 cycles, then go low (max 5 cycles high total).
endproperty

assert property (p_enable_feature_go_low_within_5_cycles) else $error("enable_feature stayed high for too long!");
