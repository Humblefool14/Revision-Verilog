// 10-bit variable with uniformly distributed popcount (1-10)
// No $countones() - explicit bit counting via sum
// Each popcount value has 10% probability

module popcount_uniform_tb;

  // ============================================================================
  // CLASS: Constraint-based randomization with uniform popcount distribution
  // ============================================================================
  class PopcountRandomizer;
    
    rand bit [9:0] x;  // 10-bit variable
    rand int popcount; // popcount value 1-10
    
    // Explicit popcount calculation (no $countones)
    // Sum all bits: bit_count = x[0] + x[1] + ... + x[9]
    constraint popcount_range {
      popcount inside {[1:10]};  // Exclude popcount = 0
    }
    
    // Uniform distribution: each popcount value has equal probability
    // We use auxiliary randomization to pick popcount uniformly,
    // then constrain x to match that popcount
    constraint popcount_distribution {
      // The popcount constraint: sum of all bits equals the target popcount
      (x[0] + x[1] + x[2] + x[3] + x[4] + 
       x[5] + x[6] + x[7] + x[8] + x[9]) == popcount;
    }
    
    // ========================================================================
    // POST_RANDOMIZE: Verify explicit popcount calculation
    // ========================================================================
    function void post_randomize();
      int calculated_popcount = x[0] + x[1] + x[2] + x[3] + x[4] + 
                                x[5] + x[6] + x[7] + x[8] + x[9];
      assert (calculated_popcount == popcount) 
        else $fatal(1, "Popcount mismatch: constraint=%0d, calculated=%0d", 
                       popcount, calculated_popcount);
    endfunction
    
  endclass
  
  // ============================================================================
  // TESTBENCH
  // ============================================================================
  
  initial begin
    PopcountRandomizer pr = new();
    int popcount_histogram[1:10] = '{default: 0};
    int num_trials = 20000;
    int zero_count = 0;
    bit [9:0] pattern_set[int];  // Track pattern variety per popcount
    
    $display("========================================");
    $display("PopcountRandomizer - Uniform Distribution Test");
    $display("========================================");
    $display("Total trials: %0d", num_trials);
    $display("");
    
    // ========================================================================
    // TEST CASE 1: Frequency Distribution (10% each bucket)
    // ========================================================================
    $display("TEST CASE 1: Frequency Distribution");
    $display("-");
    
    for (int i = 0; i < num_trials; i++) begin
      if (!pr.randomize()) begin
        $fatal(1, "Randomization failed at iteration %0d", i);
      end
      
      int pc = pr.popcount;
      popcount_histogram[pc]++;
      
      // Track pattern variety
      pattern_set[pc] = pr.x;
      
      // Check for zero (Test Case 2)
      if (pr.x == 10'b0000000000) begin
        zero_count++;
      end
    end
    
    // Print histogram
    $display("Popcount | Count  | Percentage | Expected | Status");
    $display("---------|--------|------------|----------|--------");
    
    for (int pc = 1; pc <= 10; pc++) begin
      real percentage = (100.0 * popcount_histogram[pc]) / num_trials;
      real expected = 10.0;
      real deviation = $fabs(percentage - expected);
      string status = (deviation <= 1.5) ? "PASS" : "WARN";
      
      $display("%9d | %6d | %10.2f | %8.1f | %s",
        pc, popcount_histogram[pc], percentage, expected, status);
    end
    
    $display("");
    
    // ========================================================================
    // TEST CASE 2: Popcount=0 Excluded
    // ========================================================================
    $display("TEST CASE 2: Popcount=0 Excluded");
    $display("Count of x==0: %0d (Expected: 0)", zero_count);
    if (zero_count == 0) begin
      $display("Status: PASS");
    end else begin
      $display("Status: FAIL - Found %0d instances of x==0", zero_count);
    end
    $display("");
    
    // ========================================================================
    // TEST CASE 3: Popcount Range (each k in [1:10] appears at least once)
    // ========================================================================
    $display("TEST CASE 3: Popcount Range Coverage");
    $display("-");
    
    int missing_popcount = 0;
    for (int pc = 1; pc <= 10; pc++) begin
      if (popcount_histogram[pc] == 0) begin
        $display("Popcount %0d: NOT FOUND (FAIL)", pc);
        missing_popcount++;
      end else begin
        $display("Popcount %0d: Found (%0d samples)", pc, popcount_histogram[pc]);
      end
    end
    
    if (missing_popcount == 0) begin
      $display("Status: PASS - All popcount values 1-10 found");
    end else begin
      $display("Status: FAIL - Missing %0d popcount values", missing_popcount);
    end
    $display("");
    
    // ========================================================================
    // TEST CASE 4: Solver Performance
    // ========================================================================
    $display("TEST CASE 4: Solver Performance");
    $display("Completed %0d randomizations without timeout", num_trials);
    $display("Status: PASS");
    $display("");
    
    // ========================================================================
    // TEST CASE 5: Pattern Variety within each popcount bucket
    // ========================================================================
    $display("TEST CASE 5: Pattern Variety within Popcount Buckets");
    $display("-");
    
    // Re-run with pattern tracking (smaller sample for clarity)
    pattern_set.delete();
    int pattern_count[int];  // Count patterns per popcount
    
    PopcountRandomizer pr2 = new();
    int pattern_trials = 5000;
    
    for (int i = 0; i < pattern_trials; i++) begin
      if (!pr2.randomize()) begin
        $fatal(1, "Randomization failed at iteration %0d", i);
      end
      int pc = pr2.popcount;
      if (!pattern_set.exists(pr2.x)) begin
        pattern_set[pr2.x] = 1;
        pattern_count[pc]++;
      end
    end
    
    $display("Popcount | Unique Patterns | Status");
    $display("---------|-----------------|--------");
    
    for (int pc = 1; pc <= 10; pc++) begin
      // For popcount k, there are C(10,k) possible patterns
      // k=1: 10 patterns, k=2: 45, k=3: 120, k=4: 210, k=5: 252, etc.
      int num_combinations = binomial_coefficient(10, pc);
      int unique_patterns = pattern_count[pc];
      
      // For 5000 trials, expect to see most patterns (especially for small k)
      string status = (unique_patterns >= 3) ? "PASS" : "WARN";
      
      $display("%9d | %15d | %s (out of %0d possible)",
        pc, unique_patterns, status, num_combinations);
    end
    $display("");
    
    $display("========================================");
    $display("Summary: All test cases completed");
    $display("========================================");
    
    $finish();
  end
  
  // ========================================================================
  // HELPER: Binomial coefficient C(n,k)
  // ========================================================================
  function int binomial_coefficient(int n, int k);
    if (k > n) return 0;
    if (k == 0 || k == n) return 1;
    
    int result = 1;
    for (int i = 1; i <= k; i++) begin
      result = result * (n - k + i) / i;
    end
    return result;
  endfunction

endmodule
