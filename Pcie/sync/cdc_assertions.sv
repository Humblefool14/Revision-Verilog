
property cdc_no_glitch(clk, sig);
    logic data =0; 
    (@sig) ($time!=0, data!=sig)  |=> @(posedge clk) (sig == data); 
endproperty : cdc_no_glitch

property cdc_stability(clk, sig, period);
   @(posedge clk) !$stable(sig)  |=> $stable(sig)[*period]; 
endproperty :cdc_stability

property cdc_data_stability(clk, sig, enable);
   @(posedge clk) enable |=> (!$stable(sig) | !enable); 
endproperty :cdc_data_stability

