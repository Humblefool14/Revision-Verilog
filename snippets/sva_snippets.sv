
// if data bits is x 
 property p1;
  @(posedge clk) $isunknown(data);
 endproperty

// when clock enables are low, clocks should be toggle. 
property p1;
 $fell(enable) |-> $changed(clk);
endproperty

// same cycle --> valid and ready should become high
property high_same_cyl;
 @(posedge clk)
 $rose(valid) |-> ready;
endproperty

// next cycle ready should be high 
 property high_ready;
 @(posedge clk)
   $rose(valid) |=> ready;
 endproperty

// readdy high for five cycles. 
property p1;
 @(posedge clk)
  $rose(valid) |-> [*5]ready;
endproperty

// ready high for 5 non-consecutive cycles. 
property p1;
 @(posedge clk)
 $rose(valid) |-> [=5]ready;
 endproperty

// ready high in next 3,4 cycles. 
property p1;
@(posedge clk)
$rose(valid) |-> ##[3:4]ready;
endproperty

sequence seq_name
#[1:5](awready==1);
endsequence 

property axi_handshake; 
   // @(posedge clk) (awvalid == 1) |-> [1:5] (awready==1); 
    @(posedge clk) (awvalid == 1) |-> seq_name; 
endproperty

p1: assert property(axi_handshake); 