// ============================================================================
// five_ones_pattern
//   Random WIDTH-bit word with exactly 5 bits set.
//     80% : the 5 ones form one contiguous run   (e.g. ...0011111000...)
//     20% : the 5 ones are spread out, no two set bits adjacent
//           (e.g. ...0100101001010...)
//   WIDTH must be >= 9 (smallest word that fits 1010101010 -> 5 isolated ones).
// ============================================================================
`include "uvm_macros.svh"
import uvm_pkg::*;

class five_ones_pattern #(int WIDTH = 32) extends uvm_object;

  localparam int                NUM_ONES = 5;
  localparam bit [WIDTH-1:0]    RUN5     = {NUM_ONES{1'b1}};   // zero-extended 5'b11111

  // ── Random fields ─────────────────────────────────────────
  rand bit [WIDTH-1:0] x;               // output pattern
  rand bit             is_consecutive;  // mode select
  rand int unsigned    start;           // LSB of the run (consecutive mode only)

  // ── Constraints ───────────────────────────────────────────
  // Mode: 80 / 20 split
  constraint c_mode_dist {
    is_consecutive dist { 1 := 80, 0 := 20 };
  }

  // Exactly 5 ones in every case
  constraint c_popcount {
    $countones(x) == NUM_ONES;
  }

  // Shape of the pattern
  constraint c_shape {
    if (is_consecutive) {
      start inside {[0 : WIDTH-NUM_ONES]};
      x == (RUN5 << start);              // one run of 5 at [start+4:start]
    } else {
      start == 0;                        // unused in this mode, pinned for clean logs
      (x & (x >> 1)) == '0;              // no two set bits adjacent
    }
  }

  // Pick the mode first so the 80/20 split is not skewed by the
  // (much larger) solution space of the spread-out case
  constraint c_order {
    solve is_consecutive before x, start;
  }

  // ── UVM plumbing ──────────────────────────────────────────
  `uvm_object_param_utils_begin(five_ones_pattern #(WIDTH))
    `uvm_field_int(x,              UVM_ALL_ON | UVM_BIN)
    `uvm_field_int(is_consecutive, UVM_ALL_ON)
    `uvm_field_int(start,          UVM_ALL_ON | UVM_DEC)
  `uvm_object_utils_end

  function new(string name = "five_ones_pattern");
    super.new(name);
    if (WIDTH < 2*NUM_ONES - 1)
      `uvm_fatal("WIDTH", $sformatf("WIDTH=%0d too small; need >= %0d", WIDTH, 2*NUM_ONES-1))
  endfunction

  // Self-check, usable from post_randomize or a scoreboard
  function bit is_legal();
    if ($countones(x) != NUM_ONES) return 0;
    if (is_consecutive)            return (x == (RUN5 << start));
    else                           return ((x & (x >> 1)) == '0);
  endfunction

  function void post_randomize();
    if (!is_legal())
      `uvm_error("ILLEGAL", $sformatf("bad pattern %b (consec=%0b start=%0d)",
                                      x, is_consecutive, start))
  endfunction

  function string convert2string();
    return $sformatf("%s x=%b start=%0d",
                     is_consecutive ? "CONSEC" : "SPREAD", x, start);
  endfunction

endclass


// ============================================================================
// Quick distribution check
// ============================================================================
module tb_five_ones;
  initial begin
    five_ones_pattern #(32) p = new("p");
    int n = 10000, n_consec = 0;

    repeat (n) begin
      if (!p.randomize()) `uvm_fatal("RAND", "randomize() failed")
      n_consec += p.is_consecutive;
    end
    $display("consecutive: %0d/%0d (%.1f%%)", n_consec, n, 100.0*n_consec/n);

    repeat (8) begin
      void'(p.randomize());
      $display("%s", p.convert2string());
    end

    // Inline constraints compose cleanly because x is solved, not overwritten
    void'(p.randomize() with { is_consecutive == 0; x[0] == 1; });
    $display("forced: %s", p.convert2string());
    $finish;
  end
endmodule
