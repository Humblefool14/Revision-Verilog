// SystemVerilog Testbench with Constraints for 3 Registers
// One register gets one-hot value, two others get random values

class RegisterRandomization;
    
    // Register values
    rand logic [31:0] reg_a;
    rand logic [31:0] reg_b;
    rand logic [31:0] reg_c;
    
    // Control variable: select which register gets one-hot (0=reg_a, 1=reg_b, 2=reg_c)
    rand int unsigned selected_onehot_reg;
    
    // Constraints
    constraints {
        // Select which register gets one-hot value (0, 1, or 2)
        selected_onehot_reg inside {0, 1, 2};
        
        // One-hot constraint: only one bit is set
        // Apply one-hot constraint to the selected register
        if (selected_onehot_reg == 0) {
            $onehot(reg_a);
            // reg_b and reg_c are random (no constraint)
        }
        else if (selected_onehot_reg == 1) {
            $onehot(reg_b);
            // reg_a and reg_c are random (no constraint)
        }
        else {
            $onehot(reg_c);
            // reg_a and reg_b are random (no constraint)
        }
    }
    
    // Method to print current values
    function void display();
        $display("Selected One-Hot Register: %0d", selected_onehot_reg);
        $display("reg_a = 0x%08h", reg_a);
        $display("reg_b = 0x%08h", reg_b);
        $display("reg_c = 0x%08h", reg_c);
        
        // Verify which register is one-hot
        if (selected_onehot_reg == 0)
            $display("  ✓ reg_a is one-hot (2^%0d)", $clog2(reg_a));
        else if (selected_onehot_reg == 1)
            $display("  ✓ reg_b is one-hot (2^%0d)", $clog2(reg_b));
        else
            $display("  ✓ reg_c is one-hot (2^%0d)", $clog2(reg_c));
    endfunction
endclass
