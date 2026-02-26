/*
 * UVM SystemVerilog Constraint for Contiguous 1-Bit Runs
 * 
 * Pattern: [0s...] [1s...contiguous...] [0s...]
 * Ensures all 1-bits form a single contiguous run with no gaps.
 * 
 * Parameters:
 *   WIDTH (W): Bit width (e.g., 8, 16, 32, 64)
 *   ALLOW_ALL_ZEROS: Allow all-0s pattern (run_length=0)
 *   ALLOW_ALL_ONES: Allow all-1s pattern (run_length=W)
 */

//============================================================================
// CLASS: contiguous_ones_randomizer
// PURPOSE: Randomize value with contiguous 1-bit run constraint
//============================================================================
class contiguous_ones_randomizer #(
    int WIDTH = 16,
    bit ALLOW_ALL_ZEROS = 1,
    bit ALLOW_ALL_ONES = 1
) extends uvm_object;

    // Randomizable fields
    rand logic [WIDTH-1:0] value;           // The generated number
    rand int unsigned run_start;            // Start position of 1-run [0:W-1]
    rand int unsigned run_length;           // Length of 1-run [0:W]

    `uvm_object_param_utils(contiguous_ones_randomizer#(WIDTH, ALLOW_ALL_ZEROS, ALLOW_ALL_ONES))

    //------------------------------------------------------------------------
    // Constraints
    //------------------------------------------------------------------------

    // Constraint 1: run_start is within valid range [0:W-1]
    constraint c_run_start_valid {
        run_start < WIDTH;
    }

    // Constraint 2: run_length is within valid range [0:W]
    constraint c_run_length_valid {
        run_length <= WIDTH;
    }

    // Constraint 3: Start + length must not exceed WIDTH
    constraint c_no_overflow {
        (run_start + run_length) <= WIDTH;
    }

    // Constraint 4: Edge case - disallow all-zeros if not allowed
    constraint c_disallow_all_zeros {
        if (!ALLOW_ALL_ZEROS) {
            run_length > 0;
        }
    }

    // Constraint 5: Edge case - disallow all-ones if not allowed
    constraint c_disallow_all_ones {
        if (!ALLOW_ALL_ONES) {
            !(run_length == WIDTH && run_start == 0);
        }
    }

    // Constraint 6: Generate contiguous 1-run mask
    // For position i:
    //   value[i] = 1 if i >= run_start AND i < (run_start + run_length)
    //   value[i] = 0 otherwise
    constraint c_contiguous_ones {
        foreach (value[i]) {
            if (i >= run_start && i < (run_start + run_length)) {
                value[i] == 1'b1;
            } else {
                value[i] == 1'b0;
            }
        }
    }

    //------------------------------------------------------------------------
    // Methods
    //------------------------------------------------------------------------

    function new(string name="contiguous_ones_randomizer");
        super.new(name);
    endfunction

    // Verify contiguity post-randomization
    function bit verify_contiguous();
        int first_one, last_one;
        bit found_first = 0;
        bit found_last = 0;
        int i;

        // Find first 1-bit (from LSB)
        for (i = 0; i < WIDTH; i++) begin
            if (value[i] == 1'b1) begin
                first_one = i;
                found_first = 1;
                break;
            end
        end

        // Find last 1-bit (from MSB)
        for (i = WIDTH-1; i >= 0; i--) begin
            if (value[i] == 1'b1) begin
                last_one = i;
                found_last = 1;
                break;
            end
        end

        // Case: all zeros
        if (!found_first && !found_last) begin
            if (!ALLOW_ALL_ZEROS) begin
                `uvm_error("VERIFY", "All-zeros detected but not allowed")
                return 0;
            end
            return 1;
        end

        // Case: has 1-bits
        if (found_first && found_last) begin
            // All bits between first and last must be 1
            for (i = first_one; i <= last_one; i++) begin
                if (value[i] != 1'b1) begin
                    `uvm_error("VERIFY", $sformatf(
                        "Gap detected: bit[%0d]=0 between first_one=%0d and last_one=%0d",
                        i, first_one, last_one))
                    return 0;
                end
            end
            return 1;
        end

        `uvm_error("VERIFY", "Invalid state")
        return 0;
    endfunction

    // Get run parameters (useful for debugging)
    function void get_run_parameters(output int unsigned start, output int unsigned length);
        start = run_start;
        length = run_length;
    endfunction

    // Get popcount (number of 1-bits)
    function int unsigned get_popcount();
        return run_length;
    endfunction

endclass


//============================================================================
// CLASS: contiguous_ones_test
// PURPOSE: Testbench to verify constraint behavior
//============================================================================
class contiguous_ones_test #(int WIDTH = 16) extends uvm_test;

    `uvm_component_utils(contiguous_ones_test#(WIDTH))

    contiguous_ones_randomizer#(WIDTH, 1, 1) randomizer_both;
    contiguous_ones_randomizer#(WIDTH, 0, 1) randomizer_no_zeros;
    contiguous_ones_randomizer#(WIDTH, 1, 0) randomizer_no_ones;

    int num_iterations = 100;
    int num_patterns_seen = 0;

    function new(string name="contiguous_ones_test", uvm_component parent=null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        randomizer_both = contiguous_ones_randomizer#(WIDTH, 1, 1)::type_id::create("randomizer_both");
        randomizer_no_zeros = contiguous_ones_randomizer#(WIDTH, 0, 1)::type_id::create("randomizer_no_zeros");
        randomizer_no_ones = contiguous_ones_randomizer#(WIDTH, 1, 0)::type_id::create("randomizer_no_ones");
    endfunction

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        `uvm_info("TEST", "=== Test 1: Both edge cases allowed ===", UVM_MEDIUM)
        test_randomizer(randomizer_both, "Both");

        `uvm_info("TEST", "=== Test 2: No all-zeros ===", UVM_MEDIUM)
        test_randomizer(randomizer_no_zeros, "No-Zeros");

        `uvm_info("TEST", "=== Test 3: No all-ones ===", UVM_MEDIUM)
        test_randomizer(randomizer_no_ones, "No-Ones");

        `uvm_info("TEST", $sformatf("Total unique patterns seen: %0d", num_patterns_seen), UVM_MEDIUM)

        phase.drop_objection(this);
    endtask

    task test_randomizer(
        contiguous_ones_randomizer#(WIDTH, ?, ?) randomizer,
        string test_name
    );
        bit [WIDTH-1:0] prev_value = '0;
        bit [WIDTH-1:0] patterns [bit [WIDTH-1:0]];
        int unsigned start_pos, run_len;
        bit is_valid;

        for (int iter = 0; iter < num_iterations; iter++) begin
            if (!randomizer.randomize()) begin
                `uvm_error("TEST", $sformatf("%s: Randomization failed at iteration %0d", test_name, iter))
                continue;
            end

            is_valid = randomizer.verify_contiguous();
            if (!is_valid) begin
                `uvm_error("TEST", $sformatf(
                    "%s: Verification failed for value=0x%x at iteration %0d",
                    test_name, randomizer.value, iter))
            end

            // Track unique patterns
            if (!patterns.exists(randomizer.value)) begin
                patterns[randomizer.value] = 1;
                num_patterns_seen++;

                randomizer.get_run_parameters(start_pos, run_len);
                `uvm_info("TEST", $sformatf(
                    "%s [%0d]: value=0x%x (binary=%b), start=%0d, length=%0d, popcount=%0d",
                    test_name, iter, randomizer.value, randomizer.value,
                    start_pos, run_len, randomizer.get_popcount()),
                    UVM_HIGH)
            end
        end

        `uvm_info("TEST", $sformatf("%s: Generated %0d unique patterns from %0d iterations",
            test_name, patterns.size(), num_iterations), UVM_MEDIUM)
    endtask

endclass


//============================================================================
// TESTBENCH: Top-level simulation
//============================================================================
module tb_contiguous_ones();

    initial begin
        uvm_config_db#(int)::set(null, "uvm_test_top*", "num_iterations", 500);
        run_test("contiguous_ones_test#(.WIDTH(16))");
    end

endmodule
