class lowbits_item extends uvm_sequence_item;
  rand bit [3:0] x;
  `uvm_object_utils(lowbits_item)

  function new(string name = "lowbits_item");
    super.new(name);
  endfunction

  constraint c_low {
    x[1:0] dist { 2'b00 := 1,
                  2'b11 := 1,
                  2'b01 := 19,
                  2'b10 := 19 };   // total 40: same = 2/40 = 5%
  }
  // x[3:2] unconstrained -> uniform, independent of x[1:0]
endclass
