class seq_item extends uvm_sequence_item;
    uvm_object_utils(seq_item)
    function new(string name="seq_item");
       //TODO: Constructor
       super.(name)
    endfunction

    // TODO: Declare rand variable
class bit_var_gen;
  rand bit [3:0] x;

  constraint lower_bits_prob_c {
    x[1:0] dist {
      2'b00 := 25,
      2'b11 := 25,
      2'b01 := 475,
      2'b10 := 475
    };
  }
endclass

endclass
