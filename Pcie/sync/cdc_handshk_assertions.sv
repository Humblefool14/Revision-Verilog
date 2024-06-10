property cdc_hdshk_data_stability(clk, req, ack, data);
   @(posedge clk) (req & ~ack) |=> $stable(data); 
endproperty :cdc_hdshk_data_stability

property cdc_hs_protocol(clk,  req, ack);
   @(posedge clk) $rose(req)  |=> req[*1::$] ##0 $rose(ack);  
endproperty :cdc_hs_protocol 