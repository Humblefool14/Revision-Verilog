// ---------------------------------------------------------------------------
// 10-bit value whose popcount is uniform over 1..10 (10% each), popcount 0
// excluded. No $countones() used inside constraints.
//
// Key idea:
//   1. Pick the popcount first (aux var `k`, uniform over 1..10).
//   2. Constrain x so its explicit bit-sum equals k.
//   3. `solve k before x` forces k to be chosen uniformly *before* x.
//      Without it, the solver picks uniformly over all (k, x) solutions,
//      which tracks C(10,k): popcount 5 (252 patterns) would dominate and
//      popcount 10 (1 pattern) would almost never appear.
//   Within a bucket, x is uniform over the C(10,k) patterns with k ones.
// ---------------------------------------------------------------------------

class popcount_item extends uvm_sequence_item;

  rand bit [9:0] x;
  rand bit [3:0] k;   // target popcount; 4 bits is enough for 0..15

  `uvm_object_utils_begin(popcount_item)
    `uvm_field_int(x, UVM_ALL_ON | UVM_BIN)
    `uvm_field_int(k, UVM_ALL_ON | UVM_DEC)
  `uvm_object_utils_end

  function new(string name = "popcount_item");
    super.new(name);
  endfunction

  // Bucket selection: 1..10, equal weight each (10%).
  constraint c_k_range {
    k dist { [1:10] :/ 100 };   // :/ splits 100 evenly -> 10 per value
  }

  // Explicit popcount: sum of individual bits.
  // Each bit is cast to 4 bits so the sum can't truncate on any tool,
  // regardless of how it sizes the expression context.
  constraint c_popcount {
    ( 4'(x[0]) + 4'(x[1]) + 4'(x[2]) + 4'(x[3]) + 4'(x[4])
    + 4'(x[5]) + 4'(x[6]) + 4'(x[7]) + 4'(x[8]) + 4'(x[9]) ) == k;
  }

  // Makes the *popcount* uniform rather than the bit pattern.
  constraint c_order {
    solve k before x;
  }

endclass


// ---------------------------------------------------------------------------
// Alternative if your solver is happier with array reductions:
// randomize an unpacked bit array and pack it in post_randomize().
// ---------------------------------------------------------------------------
class popcount_item_arr extends uvm_sequence_item;

  rand bit       b[10];
  rand bit [3:0] k;
       bit [9:0] x;   // packed result

  `uvm_object_utils(popcount_item_arr)

  function new(string name = "popcount_item_arr");
    super.new(name);
  endfunction

  constraint c_k     { k inside {[1:10]}; }   // inside -> uniform over values
  constraint c_sum   { b.sum() with (4'(item)) == k; }
  constraint c_order { solve k before b; }

  function void post_randomize();
    foreach (b[i]) x[i] = b[i];
  endfunction

endclass


// ---------------------------------------------------------------------------
// Self-check: randomize N times, histogram popcount, verify ~10% per bucket.
// $countones is fine here — it's procedural, not inside a constraint.
// ---------------------------------------------------------------------------
module tb_popcount;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  initial begin
    popcount_item it = popcount_item::type_id::create("it");
    int unsigned  hist[11];
    int unsigned  N = 100_000;

    repeat (N) begin
      if (!it.randomize()) `uvm_fatal("RAND", "randomize failed")
      if ($countones(it.x) != it.k)
        `uvm_error("CHK", $sformatf("x=%b popcount=%0d k=%0d",
                                    it.x, $countones(it.x), it.k))
      hist[$countones(it.x)]++;
    end

    if (hist[0] != 0) `uvm_error("CHK", "popcount 0 generated")

    for (int p = 1; p <= 10; p++)
      $display("popcount %2d : %6d  (%5.2f%%)", p, hist[p], 100.0*hist[p]/N);
  end
endmodule
