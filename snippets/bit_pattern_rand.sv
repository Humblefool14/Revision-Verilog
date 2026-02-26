// ============================================================================
// UVM SV Constraint: Generate random numbers with exactly 5 bits set
// - 80% probability: 5 bits are consecutive (contiguous run)
// - 20% probability: 5 bits are non-consecutive (spread out)
// ============================================================================

class bit_pattern_rand extends uvm_object;
  `uvm_object_utils(bit_pattern_rand)

  // Word width definition
  parameter int WORD_WIDTH = 32;  // Can be 16, 32, 64 as needed

  // Constraint fields
  rand bit [WORD_WIDTH-1:0] value;
  rand bit mode;  // 0=consecutive (80%), 1=non_consecutive (20%)
  
  // Calculated fields (not randomized, used for constraint validation)
  rand bit [4:0] run_start;     // Start position of consecutive run (0 to WORD_WIDTH-5)

  // ========================================================================
  // CONSTRAINTS
  // ========================================================================

  // Constraint 1: Mode distribution (80% consecutive, 20% non-consecutive)
  constraint mode_dist {
    mode dist { 0 := 80, 1 := 20 };
  }

  // Constraint 2: POPCOUNT constraint - exactly 5 bits set ALWAYS
  constraint exactly_5_bits {
    $countones(value) == 5;
  }

  // Constraint 3: Consecutive mode (80% of time)
  // Generate a contiguous run of 5 bits starting at position run_start
  constraint consecutive_mode {
    if (mode == 0) {
      // run_start can be 0 to WORD_WIDTH-5 (ensuring 5 bits fit)
      run_start inside { [0 : WORD_WIDTH-5] };
      
      // Create the bit pattern: set exactly 5 consecutive bits
      // value = {upper_bits[WORD_WIDTH-1:run_start+5], 5'b11111, lower_bits[run_start-1:0]}
      foreach (value[i]) {
        if (i >= run_start && i < run_start + 5) {
          value[i] == 1'b1;  // Bits within the run must be 1
        } else {
          value[i] == 1'b0;  // All other bits must be 0
        }
      }
    }
  }

  // Constraint 4: Non-consecutive mode (20% of time)
  // Ensure 5 bits are set but NO contiguous run of 5 exists
  constraint non_consecutive_mode {
    if (mode == 1) {
      // Popcount is already constrained to 5 by exactly_5_bits
      // Now ensure NO run of 5 consecutive 1's exists
      // Check all possible windows of 5 bits
      foreach (value[i]) {
        if (i <= WORD_WIDTH - 5) {
          // Check if bits [i+4:i] form a consecutive run of 5 ones
          // This must NOT be true in non-consecutive mode
          !(value[i] & value[i+1] & value[i+2] & value[i+3] & value[i+4]);
        }
      }
    }
  }

  // ========================================================================
  // METHODS
  // ========================================================================

  function new(string name = "bit_pattern_rand");
    super.new(name);
  endfunction

  // Helper function: Check if value has a run of at least 5 consecutive 1's
  function bit has_consecutive_run();
    for (int i = 0; i <= WORD_WIDTH - 5; i++) {
      if ((value[i+4:i] == 5'b11111)) begin
        return 1'b1;
      end
    end
    return 1'b0;
  endfunction

  // Helper function: Get the popcount
  function int get_popcount();
    return $countones(value);
  endfunction

  // Helper function: Print value as binary
  function string to_binary_string();
    string result = "";
    for (int i = WORD_WIDTH - 1; i >= 0; i--) begin
      result = {result, value[i] ? "1" : "0"};
      if ((i % 8 == 0) && (i != 0)) result = {result, "_"};  // Group by 8 bits
    end
    return result;
  endfunction

  // Helper function: Detect if 5 bits are consecutive
  function bit detect_consecutive();
    for (int i = 0; i <= WORD_WIDTH - 5; i++) begin
      if ((value[i+4:i] == 5'b11111)) begin
        return 1'b1;
      end
    end
    return 1'b0;
  endfunction

  // Override to_string for better display
  function string to_string();
    string s;
    s = $sformatf("value=0x%0h (binary: %s) | popcount=%0d | mode=%s | consecutive=%s",
      value, to_binary_string(), get_popcount(),
      (mode == 0 ? "consecutive" : "non-consec"),
      (detect_consecutive() ? "YES" : "NO"));
    return s;
  endfunction

endclass : bit_pattern_rand
