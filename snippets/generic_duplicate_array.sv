class generic_duplicate_array #(int N = 10, int K = 3);

  // Main array
  rand bit [7:0] arr[N];

  // Duplicate value
  rand bit [7:0] dup_val;

  // Constraint: basic sanity
  constraint c_valid {
    K > 0;
    K < N;
    dup_val inside {[0:255]};
  }

  // Constraint: remaining elements
  constraint c_remaining {

    // Domain for remaining elements
    foreach (arr[i])
      if (i >= K)
        arr[i] inside {[0:255]};

    // Remaining values unique
    if (N-K > 1)
      unique { arr[K:N-1] };

    // Remaining values different from duplicate
    foreach (arr[i])
      if (i >= K)
        arr[i] != dup_val;
  }

  // ---------------------------------
  // Pre-randomize: assign duplicates
  // ---------------------------------
  function void pre_randomize();
    for (int i = 0; i < K; i++)
      arr[i] = dup_val;
  endfunction

  // ---------------------------------
  // Post-randomize: shuffle positions
  // ---------------------------------
  function void post_randomize();
    arr.shuffle();
  endfunction

endclass
