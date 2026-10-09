class dv_seq_item extends uvm_sequence_item;
  `uvm_object_utils(dv_seq_item)

  typedef bit [9:0] number_t;
  localparam int WINDOW = 4;

  rand number_t number;
  number_t      recent_numbers[$];   // newest at [0], at most WINDOW entries

  constraint c_value      { number inside {[0:31]}; }
  constraint c_not_recent { !(number inside {recent_numbers}); }

  function new(string name = "dv_seq_item");
    super.new(name);
  endfunction

  function void post_randomize();
    recent_numbers.push_front(number);
    if (recent_numbers.size() > WINDOW)
      void'(recent_numbers.pop_back());
  endfunction
endclass
