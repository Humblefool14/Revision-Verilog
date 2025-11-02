class tx_coefficients;

  // Randomized coefficients
  rand int C_minus_1;  // Pre-cursor
  rand int C0;         // Main tap
  rand int C_plus_1;   // Post-cursor
  rand bit swing_mode; // 0: reduced swing, 1: full swing
  rand int FS;         // Full swing value

  // Low-frequency emphasis limit (externally provided)
  int LF;

  // Constraints
  constraint valid_coefficients {
    // a) |C-1| ≤ Floor(FS/4)
    abs(C_minus_1) <= FS/4;

    // b) |C-1| + |C0| + |C+1| = FS
    abs(C_minus_1) + abs(C0) + abs(C_plus_1) == FS;

    // c) Main tap must maintain minimum LF margin
    C0 - abs(C_minus_1) - abs(C_plus_1) >= LF;

    // d) FS ranges by mode
    if (swing_mode)
      FS inside {[24:63]}; // full swing
    else
      FS inside {[12:63]}; // reduced swing
  }

  // Practical search space to aid solver
  constraint reasonable_ranges {
    C_minus_1 inside {[-63:63]};
    C0 inside {[0:63]};
    C_plus_1 inside {[-63:63]};
  }

  // Helper absolute value
  function int abs(int val);
    return (val < 0) ? -val : val;
  endfunction

  // Optional: post_randomize check
  function void post_randomize();
    assert(FS == abs(C_minus_1) + abs(C0) + abs(C_plus_1))
      else $warning("Mismatch: FS constraint not consistent with coefficients");
  endfunction

endclass
