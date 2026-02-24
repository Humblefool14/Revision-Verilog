`include "uvm_macros.svh"
import uvm_pkg::*;

// ─────────────────────────────────────────────────────────────────────────────
// Transaction
// ─────────────────────────────────────────────────────────────────────────────
class transaction #(parameter int M = 4, parameter int N = 4)
    extends uvm_sequence_item;

    `uvm_object_param_utils(transaction #(M, N))

    // ── data ──────────────────────────────────────────────────────────────────
    rand int unsigned mm[M][N];   // M×N array, values in [0:100]
    rand int unsigned row_max[M]; // per-row maximum (auxiliary rand variable)

    // ── constructor ───────────────────────────────────────────────────────────
    function new(string name = "transaction");
        super.new(name);
    endfunction

    // =========================================================================
    // CONSTRAINTS
    // =========================================================================

    // (1) Every cell lives in [0, 100]
    constraint c_elem_range {
        foreach (mm[i, j])
            mm[i][j] inside {[0:100]};
    }

    // (2) row_max[i] equals the true maximum of row i
    //     Expressed as: row_max[i] is IN the row AND >= every element
    constraint c_row_max_definition {
        foreach (mm[i]) {
            // row_max[i] must appear at least once in the row
            mm[i].or() with (item == row_max[i]);   // ← at-least-one member equals max

            // row_max[i] is an upper bound for every element
            foreach (mm[i][j])
                mm[i][j] <= row_max[i];
        }
    }

    // (3) Strict maximum: exactly ONE cell per row equals row_max[i]
    //     Equivalently: the number of cells equal to row_max[i] is exactly 1
    constraint c_strict_max {
        foreach (mm[i]) {
            mm[i].sum() with (int'(item == row_max[i])) == 1;
        }
    }

    // (4) Cross-row uniqueness: all row maxima are distinct
    constraint c_cross_row_unique {
        unique {row_max};
    }

    // =========================================================================
    // HELPER – post_randomize consistency check (not a constraint, just a guard)
    // =========================================================================
    function void post_randomize();
        foreach (mm[i]) begin
            int unsigned computed_max = 0;
            int          cnt          = 0;
            foreach (mm[i][j])
                if (mm[i][j] > computed_max) computed_max = mm[i][j];
            foreach (mm[i][j])
                if (mm[i][j] == computed_max) cnt++;

            if (computed_max !== row_max[i])
                `uvm_fatal("ROW_MAX_MISMATCH",
                    $sformatf("row %0d: declared max=%0d but computed=%0d",
                              i, row_max[i], computed_max))
            if (cnt !== 1)
                `uvm_fatal("STRICT_MAX_FAIL",
                    $sformatf("row %0d: max value %0d appears %0d times (expected 1)",
                              i, computed_max, cnt))
        end
    endfunction

    // ── pretty printer ────────────────────────────────────────────────────────
    function string convert2string();
        string s = "\n";
        foreach (mm[i]) begin
            s = {s, $sformatf("  row[%0d] max=%-3d | ", i, row_max[i])};
            foreach (mm[i][j])
                s = {s, $sformatf("%3d ", mm[i][j])};
            s = {s, "\n"};
        end
        return s;
    endfunction

endclass


// ─────────────────────────────────────────────────────────────────────────────
// Test bench  (5 test cases)
// ─────────────────────────────────────────────────────────────────────────────
module tb;

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    localparam int M = 4;
    localparam int N = 4;

    typedef transaction #(M, N) trans_t;

    // ── utilities ─────────────────────────────────────────────────────────────
    function automatic int unsigned row_true_max(trans_t t, int row);
        int unsigned mx = 0;
        for (int j = 0; j < N; j++)
            if (t.mm[row][j] > mx) mx = t.mm[row][j];
        return mx;
    endfunction

    function automatic int count_occurrences(trans_t t, int row, int unsigned val);
        int cnt = 0;
        for (int j = 0; j < N; j++)
            if (t.mm[row][j] == val) cnt++;
        return cnt;
    endfunction

    // ── check helpers ─────────────────────────────────────────────────────────
    task automatic check_tc1_row_unique_max(trans_t t, string tag);
        foreach (t.mm[i]) begin
            int unsigned mx  = row_true_max(t, i);
            int          cnt = count_occurrences(t, i, mx);
            if (cnt !== 1)
                `uvm_error(tag,
                    $sformatf("TC1 FAIL row %0d: max=%0d appears %0d times", i, mx, cnt))
            else
                `uvm_info(tag,
                    $sformatf("TC1 PASS row %0d: max=%0d appears exactly once", i, mx),
                    UVM_MEDIUM)
        end
    endtask

    task automatic check_tc2_strict_inequality(trans_t t, string tag);
        foreach (t.mm[i]) begin
            int unsigned mx = row_true_max(t, i);
            foreach (t.mm[i][j]) begin
                if (t.mm[i][j] == mx) continue;
                if (t.mm[i][j] >= mx)
                    `uvm_error(tag,
                        $sformatf("TC2 FAIL row %0d col %0d: val=%0d >= max=%0d",
                                  i, j, t.mm[i][j], mx))
            end
        end
        `uvm_info(tag, "TC2 PASS: all non-max elements strictly less than row max", UVM_MEDIUM)
    endtask

    task automatic check_tc3_cross_row_uniqueness(trans_t t, string tag);
        int unsigned maxima[M];
        foreach (t.mm[i]) maxima[i] = row_true_max(t, i);
        for (int a = 0; a < M; a++)
            for (int b = a+1; b < M; b++)
                if (maxima[a] === maxima[b])
                    `uvm_error(tag,
                        $sformatf("TC3 FAIL: row %0d and row %0d share max=%0d",
                                  a, b, maxima[a]))
        `uvm_info(tag, "TC3 PASS: all row maxima are distinct", UVM_MEDIUM)
    endtask

    task automatic check_tc5_distribution(string tag);
        // Randomize many times; collect all row-maxima; verify spread
        trans_t       t   = new("tc5");
        int unsigned  seen[int];
        int           REPS = 20;

        for (int r = 0; r < REPS; r++) begin
            if (!t.randomize()) begin
                `uvm_error(tag, "TC5: randomize() failed"); return;
            end
            foreach (t.mm[i]) begin
                int unsigned mx = row_true_max(t, i);
                seen[mx] = 1;
            end
        end

        `uvm_info(tag,
            $sformatf("TC5 PASS: %0d distinct max values observed across %0d randomizations",
                      seen.size(), REPS),
            UVM_MEDIUM)
        if (seen.size() < M)
            `uvm_warning(tag, "TC5: fewer distinct maxima than rows – solver may be stuck")
    endtask

    // =========================================================================
    // Main test sequence
    // =========================================================================
    initial begin
        trans_t t;

        // ── TC 1 / 2 / 3 – normal randomization ──────────────────────────────
        begin : tc123
            t = new("tc123");
            repeat (5) begin
                if (!t.randomize())
                    `uvm_fatal("TB", "TC1/2/3: randomize() failed unexpectedly")
                `uvm_info("TB", t.convert2string(), UVM_MEDIUM)
                check_tc1_row_unique_max     (t, "TC1");
                check_tc2_strict_inequality  (t, "TC2");
                check_tc3_cross_row_uniqueness(t, "TC3");
            end
        end

        // ── TC 4 – UNSAT corner: force all cells to the same value ─────────────
        begin : tc4
            t = new("tc4");
            // Inline constraint forces all cells to 5 → solver must fail because
            // it cannot produce M distinct row-maxima when every cell is 5.
            if (t.randomize() with {
                    foreach (mm[i,j]) mm[i][j] == 5;
                })
                `uvm_error("TC4", "FAIL: randomize() succeeded but should be UNSAT")
            else
                `uvm_info("TC4",
                    "PASS: randomize() correctly returned 0 (UNSAT) when all cells forced to 5",
                    UVM_MEDIUM)
        end

        // ── TC 5 – distribution ────────────────────────────────────────────────
        check_tc5_distribution("TC5");

        `uvm_info("TB", "All test cases complete.", UVM_MEDIUM)
        $finish;
    end

endmodule
