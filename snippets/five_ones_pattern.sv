class five_ones_pattern;

  // ── Core payload ─────────────────────────────────────────
  rand bit [99:0] x;          // 100-bit pattern (output)
  rand int unsigned start;    // run start position [0..95]

  // ── Constraints ──────────────────────────────────────────

  // 1. Start must be in legal range so run fits inside 100 bits
  constraint c_start_range {
    start inside {[0:95]};
  }

  // 2. Build the pattern: only bits [start+4 : start] are 1
  //    Use post_randomize to derive x from start cleanly
  //    (avoids 96 unrolled implication constraints)

  // 3. Keep solver happy: x is driven entirely by post_randomize,
  //    so we tell the solver to treat x as 0 (overwritten anyway)
  constraint c_x_zero {
    x == 100'b0;              // placeholder; post_randomize overwrites
  }

  // ── Post-randomize: build exact bit pattern ───────────────
  function void post_randomize();
    x = 100'b0;
    // Set exactly 5 consecutive bits starting at 'start'
    for (int i = 0; i < 5; i++) begin
      x[start + i] = 1'b1;
    end
  endfunction

  // ── Convenience: force a specific start (boundary tests) ──
  function void force_start(int unsigned s);
    assert(s <= 95) else $fatal(1, "start=%0d out of range [0:95]", s);
    start = s;
    post_randomize();         // rebuild x from forced start
  endfunction

  // ── Checker: all 5 test cases ─────────────────────────────
  function void check_all(string tag = "");
    automatic int ones[$];
    automatic int pop = 0;

    // ── collect indices of 1-bits ──────────────────────────
    for (int i = 0; i < 100; i++)
      if (x[i]) begin
        ones.push_back(i);
        pop++;
      end

    // Test Case 3 – popcount exactly 5
    assert(pop == 5)
      else $error("[%s] TC3 FAIL: popcount=%0d (expected 5)", tag, pop);

    // Test Case 1 – indices are exactly {start, start+1, ..., start+4}
    assert(ones.size() == 5)
      else $error("[%s] TC1 FAIL: found %0d one-bits", tag, ones.size());

    for (int k = 0; k < 5; k++)
      assert(ones[k] == start + k)
        else $error("[%s] TC1 FAIL: ones[%0d]=%0d, expected %0d",
                    tag, k, ones[k], start + k);

    // Test Case 4 – no run of length 6
    begin
      automatic int run = 0;
      automatic int max_run = 0;
      for (int i = 0; i < 100; i++) begin
        run = x[i] ? run + 1 : 0;
        if (run > max_run) max_run = run;
      end
      assert(max_run == 5)
        else $error("[%s] TC4 FAIL: max run length=%0d", tag, max_run);
    end

    $display("[%s] PASS: start=%0d  x=%b", tag, start, x);
  endfunction

endclass


// ============================================================
// Testbench
// ============================================================
module tb_five_ones;

  initial begin
    automatic five_ones_pattern pkt = new();
    automatic int unsigned starts_seen[int];   // histogram
    automatic int unsigned ITERATIONS = 500;

    // ── Test Case 2a : boundary start = 0 ─────────────────
    pkt.force_start(0);
    assert(x_matches_start(pkt.x, 0))
      else $error("TC2a FAIL: start=0 pattern wrong");
    pkt.check_all("TC2a start=0");

    // ── Test Case 2b : boundary start = 95 ────────────────
    pkt.force_start(95);
    assert(x_matches_start(pkt.x, 95))
      else $error("TC2b FAIL: start=95 pattern wrong");
    pkt.check_all("TC2b start=95");

    // ── Test Case 2c : boundary start = 47 (mid) ──────────
    pkt.force_start(47);
    pkt.check_all("TC2c start=47");

    // ── Test Cases 1,3,4,5 : random iterations ────────────
    repeat (ITERATIONS) begin
      assert(pkt.randomize())
        else $fatal(1, "randomize() failed");
      pkt.check_all("RAND");
      starts_seen[pkt.start]++;
    end

    // ── Test Case 5 : distribution check ──────────────────
    // Expect ~500/96 ≈ 5.2 hits per bucket; flag if any bucket
    // is missing entirely (astronomically unlikely with 500 runs
    // but would catch a broken constraint)
    begin
      automatic int missing = 0;
      for (int s = 0; s <= 95; s++)
        if (!starts_seen.exists(s)) missing++;
      if (missing > 0)
        $warning("TC5 WARN: %0d start positions never seen in %0d iters",
                 missing, ITERATIONS);
      else
        $display("TC5 PASS: all 96 start positions observed in %0d iters",
                 ITERATIONS);
    end

    $display("ALL TESTS COMPLETE");
    $finish;
  end

  // ── Helper: build expected pattern and compare ───────────
  function automatic bit x_matches_start(bit [99:0] x, int unsigned s);
    bit [99:0] expected = 100'b0;
    for (int i = 0; i < 5; i++) expected[s+i] = 1'b1;
    return (x === expected);
  endfunction

endmodule
