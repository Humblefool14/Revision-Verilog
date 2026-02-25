class triplicate_array;

  rand bit [7:0] arr[10];

  // duplicate value
  rand bit [7:0] x;

  // number of duplicates required
  localparam int COUNT = 3;

  // -------------------------
  // Constraints
  // -------------------------
  constraint c_domain {
    x inside {[0:255]};
  }

  constraint c_remaining_unique {

    // Remaining 7 values must be in domain
    foreach (arr[i])
      if (i >= COUNT)
        arr[i] inside {[0:255]};

    // Remaining 7 values must be unique
    unique { arr[3], arr[4], arr[5], arr[6],
             arr[7], arr[8], arr[9] };

    // Remaining values must differ from x
    foreach (arr[i])
      if (i >= COUNT)
        arr[i] != x;
  }

  // -------------------------
  // Pre-randomization
  // -------------------------
  function void pre_randomize();
    // Assign first 3 elements to duplicate value
    for (int i = 0; i < COUNT; i++)
      arr[i] = x;
  endfunction

  // -------------------------
  // Post-randomization
  // -------------------------
  function void post_randomize();
    // Randomize placement of triplicates
    arr.shuffle();
  endfunction

endclass
