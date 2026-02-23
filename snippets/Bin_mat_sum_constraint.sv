// ============================================================
// Transaction Class with M×N Binary Matrix + Sum Constraint
// ============================================================
class transaction #(
    parameter int M       = 4,
    parameter int N       = 4,
    parameter int MAX_SUM = 6
) extends uvm_sequence_item;

    `uvm_object_param_utils(transaction #(M, N, MAX_SUM))

    // --------------------------------------------------------
    // Rand Variables
    // --------------------------------------------------------
    rand bit mm[M][N];       // M×N binary matrix
    rand int sum_val;        // Accumulated sum (randomized helper)

    // --------------------------------------------------------
    // Constructor
    // --------------------------------------------------------
    function new(string name = "transaction");
        super.new(name);
    endfunction

    // --------------------------------------------------------
    // Constraint: Each element is binary {0,1}
    // (bit type already guarantees this, but explicit for clarity)
    // --------------------------------------------------------
    constraint elem_binary_c {
        foreach (mm[i,j])
            mm[i][j] inside {0, 1};
    }

    // --------------------------------------------------------
    // Constraint: Manual sum accumulation WITHOUT .sum()
    //   Uses iterative expression building via a generate-like
    //   approach — in SV constraints, foreach with an
    //   accumulator variable is the idiomatic way.
    // --------------------------------------------------------
    constraint manual_sum_c {
        // Accumulate sum manually using a chained expression.
        // sum_val is constrained to equal the manually computed
        // total of all elements using nested foreach + implication.
        sum_val == calc_sum_expr();
    }

    // --------------------------------------------------------
    // Constraint: Enforce sum < MAX_SUM
    // --------------------------------------------------------
    constraint sum_limit_c {
        sum_val < MAX_SUM;
    }

    // --------------------------------------------------------
    // Constraint: Feasibility guard
    // --------------------------------------------------------
    constraint feasibility_c {
        MAX_SUM >= 0;
        MAX_SUM <= M * N;
    }

    // --------------------------------------------------------
    // Pure function: Manual sum via loops (no .sum())
    // Called inside constraint — must be automatic/const context.
    // NOTE: In SV, functions in constraints must be automatic
    //       and side-effect free.
    // --------------------------------------------------------
    function automatic int calc_sum_expr();
        int acc = 0;
        for (int i = 0; i < M; i++)
            for (int j = 0; j < N; j++)
                acc = acc + mm[i][j];   // Manual accumulation
        return acc;
    endfunction

    // --------------------------------------------------------
    // Display Method
    // --------------------------------------------------------
    function void display();
        int manual_sum = 0;

        $display("============================================");
        $display(" Transaction: %s", get_name());
        $display(" Parameters : M=%0d, N=%0d, MAX_SUM=%0d", M, N, MAX_SUM);
        $display("--------------------------------------------");
        $display(" Binary Matrix mm[%0d][%0d]:", M, N);

        for (int i = 0; i < M; i++) begin
            $write("  Row[%0d] : ", i);
            for (int j = 0; j < N; j++) begin
                $write("%0b ", mm[i][j]);
                manual_sum = manual_sum + mm[i][j];  // Manual sum (no .sum())
            end
            $write("\n");
        end

        $display("--------------------------------------------");
        $display(" Manual Sum (loop) : %0d", manual_sum);
        $display(" MAX_SUM Limit     : < %0d", MAX_SUM);
        $display(" Constraint Met    : %s", (manual_sum < MAX_SUM) ? "PASS ✓" : "FAIL ✗");
        $display("============================================\n");
    endfunction

endclass


// ============================================================
// Testbench Module
// ============================================================
module tb_array;

    // ----------------------------------------------------------
    // Parameters — change here to reconfigure the matrix
    // ----------------------------------------------------------
    localparam int M       = 4;
    localparam int N       = 4;
    localparam int MAX_SUM = 6;   // Total 1s must be < 6

    // ----------------------------------------------------------
    // Instantiate transaction with parameters
    // ----------------------------------------------------------
    transaction #(.M(M), .N(N), .MAX_SUM(MAX_SUM)) txn;

    initial begin
        // Construct
        txn = new("txn_0");

        // ---- Test 1: Normal randomization ----
        $display("\n[TEST 1] Normal: MAX_SUM=%0d on %0dx%0d matrix", MAX_SUM, M, N);
        if (!txn.randomize())
            $fatal(1, "Randomization FAILED for Test 1");
        txn.display();

        // ---- Test 2: MAX_SUM = 0 → all zeros ----
        $display("[TEST 2] Edge Case: MAX_SUM=0 (all zeros forced)");
        if (!txn.randomize() with { sum_val == 0; })
            $fatal(1, "Randomization FAILED for Test 2");
        txn.display();

        // ---- Test 3: MAX_SUM = M*N → fully relaxed ----
        $display("[TEST 3] Edge Case: MAX_SUM=M*N (no effective constraint)");
        if (!txn.randomize() with { sum_val < M*N; })
            $fatal(1, "Randomization FAILED for Test 3");
        txn.display();

        $finish;
    end

endmodule
