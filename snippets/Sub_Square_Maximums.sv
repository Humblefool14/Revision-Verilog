// ---------------------------------------------------------------------------
// Odd-sized N x N matrix, tiled into non-overlapping S x S sub-squares.
//
// Partitioning (documented):
//   N = 9, S = 3  ->  B = N/S = 3 blocks per side, B*B = 9 regions.
//   Cell (i,j) belongs to block (i/S, j/S), flattened region id
//       region(i,j) = (i/S)*B + (j/S)            // 0 .. B*B-1
//   Local position inside its block: (i%S)*S + (j%S)  // 0 .. S*S-1
//   S must be an odd divisor of N. For prime N the only tilings are
//   S = 1 (every cell its own region) or S = N (one region).
//
// Construction (no counting, no factorial domains):
//   1. sub_max[r]  : the region's maximum, all pairwise distinct (unique)
//   2. max_pos[r]  : which of the S*S cells holds it
//   3. that cell == sub_max[r]; every other cell in the region < sub_max[r]
//   Since every other cell is strictly less, the max appears exactly once,
//   so no sum()/or() "exactly one" constraint is needed. The solver deals
//   only with linear comparisons, so it scales to full 32-bit values.
// ---------------------------------------------------------------------------

class dv_seq_item #(int N = 9, int S = 3) extends uvm_sequence_item;
  `uvm_object_param_utils(dv_seq_item #(N, S))

  localparam int B = N / S;     // blocks per side
  localparam int R = B * B;     // number of regions

  rand bit [31:0]   mm[N][N];
  rand bit [31:0]   sub_max[R];   // flattened 1-D: unique{} on 1-D arrays is portable
  rand int unsigned max_pos[R];   // 0 .. S*S-1, position of the max inside region

  function new(string name = "dv_seq_item");
    super.new(name);
    if (N % 2 == 0) `uvm_fatal("CFG", $sformatf("N=%0d must be odd", N))
    if (N % S != 0) `uvm_fatal("CFG", $sformatf("S=%0d must divide N=%0d", S, N))
  endfunction

  // Region membership (used by the checker; the constraint inlines the same
  // arithmetic so the solver sees plain index expressions on loop variables)
  static function int region(int i, int j);
    return (i / S) * B + (j / S);
  endfunction

  constraint c_pos {
    foreach (max_pos[r]) max_pos[r] < S * S;
  }

  constraint c_main {
    foreach (mm[i, j]) {
      if ((i % S) * S + (j % S) == max_pos[(i / S) * B + (j / S)])
        mm[i][j] == sub_max[(i / S) * B + (j / S)];   // the one max cell
      else
        mm[i][j] <  sub_max[(i / S) * B + (j / S)];   // everything else strictly below
    }
  }

  constraint c_max_distinct {
    unique {sub_max};
  }

  // Pick the max position first so it is uniform over the S*S cells,
  // independent of how many value solutions each position admits.
  constraint c_order {
    solve max_pos before mm;
  }

  // -------------------------------------------------------------------------
  // Checker for the three test cases. Recomputes everything from mm alone,
  // so it doesn't trust sub_max / max_pos (the things under test).
  // -------------------------------------------------------------------------
  function bit check();
    bit [31:0]   mx  [R];
    int unsigned cnt [R];
    bit          seen[R];
    check = 1;

    // TC1/TC2: find each region's true max and how many cells hit it
    foreach (mm[i, j]) begin
      int r = region(i, j);
      if (!seen[r] || mm[i][j] > mx[r]) begin mx[r] = mm[i][j]; cnt[r] = 0; seen[r] = 1; end
      if (mm[i][j] == mx[r]) cnt[r]++;
    end
    foreach (cnt[r])
      if (cnt[r] != 1) begin
        `uvm_error("TC1", $sformatf("region %0d max %0d appears %0d times", r, mx[r], cnt[r]))
        check = 0;
      end

    // TC3: maxima pairwise distinct
    for (int a = 0; a < R; a++)
      for (int b = a + 1; b < R; b++)
        if (mx[a] == mx[b]) begin
          `uvm_error("TC3", $sformatf("regions %0d and %0d share max %0d", a, b, mx[a]))
          check = 0;
        end
  endfunction

  function void post_randomize();
    void'(check());
  endfunction

endclass
