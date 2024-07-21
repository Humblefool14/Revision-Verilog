property atb_handshake; 
     @(posedge clk) ( atvalid && atready); 
endproperty

// stable_atvalid 
property stable_atvalid;
  @(posedge clk)
    (atvalid && !atready) |=> atvalid;
endproperty

property stable_atvalid;
  @(posedge clk) disable iff(!atrest_n) // check atatresetn
    (atvalid && !atready) |=> atvalid;
endproperty

property stable_afvalid;
  @(posedge clk)
    (afvalid && !afready) |=> afvalid;
endproperty

//AFVALID must be deasserted on the following cycle, unless an additional flush is required. 
property afvalid_deassert_after_afready;
  @(posedge clk)
    afready |=> !afvalid or $stable(afvalid);
endproperty


// ATBYTES should remain stable throughout a transaction
property stable_atbytes;
  @(posedge clk) disable iff (!atresetn)
    (atvalid && !atready) |=> $stable(atbytes);
endproperty

// ATBYTES should be non-zero when ATVALID is asserted
property non_zero_atbytes;
  @(posedge clk) disable iff (!atresetn)
    atvalid |-> (atbytes != '0);
endproperty

// ATID should be within valid range (assuming 8-bit ATID)
property valid_atid_range;
  @(posedge clk) disable iff (!atresetn)
    atvalid |-> (atid inside {[0:255]});
endproperty
// atid 

// defined by the values of m and n in ATBYTES[m:0] and ATDATA[n:0]
// m = log2(n+1) -4 

property valid_atid_values;
  @(posedge clk) disable iff (!resetn)
    atvalid |-> (atid inside {[8'h01:8'h6F]);
endproperty

// Assert the property
assert property (valid_atid_values) else $error("ATID is 0x00 or 0x70");
// Assert the properties
assert property (stable_atid);
assert property (stable_atbytes);
assert property (non_zero_atbytes);
assert property (valid_atid_range);