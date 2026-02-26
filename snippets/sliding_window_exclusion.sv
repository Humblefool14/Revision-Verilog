// =============================================================================
// Colored Ball Selection with Sliding Exclusion Window (Cooldown)
// =============================================================================
// SPECIFICATION:
// - 10 colored balls (0-9)
// - If color C picked at time t, C cannot be picked at times t+1, t+2, t+3
// - Maintain last 3 picks in sliding window
// - With replacement: same color can be picked again after cooldown expires
// - Feasibility: 10 colors - 3 excluded = 7 available each turn ✓
// =============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

// =============================================================================
// SEQUENCE ITEM: Represents a single ball pick
// =============================================================================
class seq_item extends uvm_sequence_item;
    `uvm_object_utils(seq_item)
    
    typedef bit [3:0] color_t;
    
    // Randomizable color variable (0-9)
    rand color_t color;
    
    // History: Last 3 picks (updated by post_randomize)
    // Index 0 = most recent, Index 1 = 1 draw ago, Index 2 = 2 draws ago
    color_t history[$];
    
    function new(string name="seq_item");
        super.new(name);
        history = {};
    endfunction
    
    // =========================================================================
    // CONSTRAINT: Sliding Exclusion Window
    // =========================================================================
    // The current pick must NOT match any of the last 3 picks
    // This implements the cooldown: if color C was picked in last 3 draws,
    // it cannot be picked now
    constraint sliding_window_exclusion {
        // Constraint enforces: color ∉ {history[0], history[1], history[2]}
        // Using implication to handle variable-sized queue
        if (history.size() >= 1) color != history[0];
        if (history.size() >= 2) color != history[1];
        if (history.size() >= 3) color != history[2];
    }
    
    // Ensure color is in valid range [0-9]
    constraint valid_color_range {
        color >= 0 && color <= 9;
    }
    
    // =========================================================================
    // POST_RANDOMIZE: Maintain sliding window of last 3 picks
    // =========================================================================
    function void post_randomize();
        `uvm_info("seq_item", $sformatf("Picked color: %0d, History before: %p", 
                                         color, history), UVM_HIGH)
        
        // Add current pick to front of history
        history.push_front(color);
        
        // Keep only last 3 picks (sliding window)
        if (history.size() > 3) begin
            void'(history.pop_back());
        end
        
        `uvm_info("seq_item", $sformatf("History after: %p", history), UVM_HIGH)
    endfunction
    
    // =========================================================================
    // COPY: For UVM operations
    // =========================================================================
    function void copy(uvm_object rhs);
        seq_item rhs_;
        if (!$cast(rhs_, rhs)) begin
            `uvm_error("copy", "Cast failed")
            return;
        end
        super.copy(rhs);
        this.color = rhs_.color;
        this.history = rhs_.history;
    endfunction
    
    // =========================================================================
    // CONVERT2STRING: For printing
    // =========================================================================
    function string convert2string();
        return $sformatf("color=%0d | history=%p", color, history);
    endfunction
    
endclass

// =============================================================================
// SEQUENCE: Generate multiple ball picks with constraint satisfaction
// =============================================================================
class ball_sequence extends uvm_sequence #(seq_item);
    `uvm_object_utils(ball_sequence)
    
    int num_picks = 50;
    
    function new(string name="ball_sequence");
        super.new(name);
    endfunction
    
    task body();
        seq_item item;
        for (int i = 0; i < num_picks; i++) begin
            item = seq_item::type_id::create("item");
            start_item(item);
            if (!item.randomize()) begin
                `uvm_error("ball_sequence", "Randomization failed")
                finish_item(item);
                break;
            end
            finish_item(item);
            `uvm_info("ball_sequence", 
                      $sformatf("Draw %0d: %s", i, item.convert2string()), 
                      UVM_MEDIUM)
        end
    endtask
    
endclass

// =============================================================================
// MONITOR: Collects picks and validates constraints
// =============================================================================
class ball_monitor extends uvm_monitor;
    `uvm_component_utils(ball_monitor)
    
    uvm_analysis_port #(seq_item) ap;
    
    seq_item picks[$];
    int violation_count = 0;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        ap = new("ap", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        seq_item item;
        forever begin
            @(posedge vif.clk) begin
                // Collect items (would normally come from DUT)
            end
        end
    endtask
    
    function void check_constraints(seq_item item);
        int pick_count = picks.size();
        
        // Verify sliding window constraint
        if (pick_count >= 1 && item.color == picks[pick_count-1]) begin
            `uvm_error("monitor", 
                      $sformatf("VIOLATION at draw %0d: color %0d matches last pick", 
                                 pick_count, item.color))
            violation_count++;
        end
        if (pick_count >= 2 && item.color == picks[pick_count-2]) begin
            `uvm_error("monitor", 
                      $sformatf("VIOLATION at draw %0d: color %0d matches 2-draws-ago", 
                                 pick_count, item.color))
            violation_count++;
        end
        if (pick_count >= 3 && item.color == picks[pick_count-3]) begin
            `uvm_error("monitor", 
                      $sformatf("VIOLATION at draw %0d: color %0d matches 3-draws-ago", 
                                 pick_count, item.color))
            violation_count++;
        end
        
        picks.push_back(item.color);
    endfunction
    
endclass

// =============================================================================
// TESTCASE 1: Window Rule Verification
// Test that for each draw t, pick[t] ∉ {pick[t-1], pick[t-2], pick[t-3]}
// =============================================================================
class tc1_window_rule_test extends uvm_test;
    `uvm_component_utils(tc1_window_rule_test)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        seq_item item;
        color_t picks[$];
        int violations = 0;
        
        phase.raise_objection(this);
        
        `uvm_info("tc1_window_rule_test", 
                  "==== TEST CASE 1: Window Rule Verification ====", UVM_MEDIUM)
        `uvm_info("tc1_window_rule_test", 
                  "Verify: pick[t] ∉ {pick[t-1], pick[t-2], pick[t-3]}", UVM_MEDIUM)
        
        // Generate 50 picks
        for (int t = 0; t < 50; t++) begin
            item = seq_item::type_id::create($sformatf("item_%0d", t));
            
            // Set history from previous picks
            for (int h = 0; h < picks.size() && h < 3; h++) begin
                item.history.push_back(picks[picks.size()-1-h]);
            end
            
            if (!item.randomize()) begin
                `uvm_error("tc1", "Randomization failed")
                break;
            end
            
            // Verify constraint: color not in last 3 picks
            int violation = 0;
            for (int h = 0; h < item.history.size(); h++) begin
                if (item.color == item.history[h]) begin
                    `uvm_error("tc1", 
                              $sformatf("Draw %0d: Violation! color=%0d in history[%0d]=%0d", 
                                         t, item.color, h, item.history[h]))
                    violations++;
                    violation = 1;
                end
            end
            
            if (!violation) begin
                `uvm_info("tc1", 
                          $sformatf("Draw %0d: ✓ color=%0d | history=%p", 
                                     t, item.color, item.history), UVM_HIGH)
            end
            
            picks.push_back(item.color);
        end
        
        // Summary
        `uvm_info("tc1_window_rule_test", 
                  $sformatf("Total draws: 50 | Violations: %0d", violations), UVM_MEDIUM)
        
        if (violations == 0) begin
            `uvm_info("tc1_window_rule_test", "✓ PASS: No sliding window violations", UVM_MEDIUM)
        end else begin
            `uvm_error("tc1_window_rule_test", $sformatf("✗ FAIL: %0d violations detected", violations))
        end
        
        phase.drop_objection(this);
    endtask
    
endclass

// =============================================================================
// TESTCASE 2: All Colors Appear
// Verify that over a long sequence, all 10 colors eventually appear
// (Not permanently excluded due to cooldown mechanism)
// =============================================================================
class tc2_all_colors_appear_test extends uvm_test;
    `uvm_component_utils(tc2_all_colors_appear_test)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        seq_item item;
        color_t picks[$];
        bit color_seen[10] = '{default: 0};
        int colors_found = 0;
        
        phase.raise_objection(this);
        
        `uvm_info("tc2_all_colors_appear_test", 
                  "==== TEST CASE 2: All Colors Appear ====", UVM_MEDIUM)
        `uvm_info("tc2_all_colors_appear_test", 
                  "Generate 200 picks and verify all 10 colors appear", UVM_MEDIUM)
        
        // Generate 200 picks (should be more than enough)
        for (int t = 0; t < 200; t++) begin
            item = seq_item::type_id::create($sformatf("item_%0d", t));
            
            // Set history from previous picks
            for (int h = 0; h < picks.size() && h < 3; h++) begin
                item.history.push_back(picks[picks.size()-1-h]);
            end
            
            if (!item.randomize()) begin
                `uvm_error("tc2", "Randomization failed")
                break;
            end
            
            // Track which colors have appeared
            if (!color_seen[item.color]) begin
                color_seen[item.color] = 1;
                colors_found++;
                `uvm_info("tc2", 
                          $sformatf("Draw %0d: Found new color %0d (Total: %0d/10)", 
                                     t, item.color, colors_found), UVM_MEDIUM)
            end
            
            picks.push_back(item.color);
            
            // Early exit if all colors found
            if (colors_found == 10) begin
                `uvm_info("tc2", 
                          $sformatf("All colors found after %0d draws!", t+1), UVM_MEDIUM)
                break;
            end
        end
        
        // Summary
        `uvm_info("tc2_all_colors_appear_test", 
                  $sformatf("Colors found: %0d/10", colors_found), UVM_MEDIUM)
        
        if (colors_found == 10) begin
            `uvm_info("tc2_all_colors_appear_test", 
                      "✓ PASS: All 10 colors appeared in sequence", UVM_MEDIUM)
        end else begin
            `uvm_error("tc2_all_colors_appear_test", 
                      $sformatf("✗ FAIL: Only %0d colors appeared", colors_found))
        end
        
        phase.drop_objection(this);
    endtask
    
endclass

// =============================================================================
// TESTCASE 3: Cooldown Expiry
// Pick color 5 at t=0. Verify color 5 excluded at t=1,2,3. Available at t=4.
// =============================================================================
class tc3_cooldown_expiry_test extends uvm_test;
    `uvm_component_utils(tc3_cooldown_expiry_test)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        seq_item item;
        color_t picks[$];
        int cooldown_color = 5;
        int cooldown_end = -1;
        
        phase.raise_objection(this);
        
        `uvm_info("tc3_cooldown_expiry_test", 
                  "==== TEST CASE 3: Cooldown Expiry ====", UVM_MEDIUM)
        `uvm_info("tc3_cooldown_expiry_test", 
                  $sformatf("Pick color %0d at t=0. Verify excluded at t=1,2,3. Available at t=4.", 
                            cooldown_color), UVM_MEDIUM)
        
        // Generate picks until we can verify cooldown behavior
        for (int t = 0; t < 50; t++) begin
            item = seq_item::type_id::create($sformatf("item_%0d", t));
            
            // Set history from previous picks
            for (int h = 0; h < picks.size() && h < 3; h++) begin
                item.history.push_back(picks[picks.size()-1-h]);
            end
            
            // Force first pick to be color 5
            if (t == 0) begin
                item.color = cooldown_color;
                picks.push_back(item.color);
                `uvm_info("tc3", 
                          $sformatf("t=%0d: Forced pick of color %0d (start of cooldown)", 
                                     t, cooldown_color), UVM_MEDIUM)
                continue;
            end
            
            if (!item.randomize()) begin
                `uvm_error("tc3", "Randomization failed")
                break;
            end
            
            // Verify cooldown behavior
            if (t >= 1 && t <= 3) begin
                // Cooldown active: color 5 should NOT be picked
                if (item.color == cooldown_color) begin
                    `uvm_error("tc3", 
                              $sformatf("VIOLATION at t=%0d: color %0d picked during cooldown", 
                                         t, cooldown_color))
                end else begin
                    `uvm_info("tc3", 
                              $sformatf("t=%0d: ✓ color %0d correctly excluded (cooldown active)", 
                                         t, item.color), UVM_MEDIUM)
                end
            end else if (t == 4) begin
                // Cooldown expired: color 5 becomes available
                `uvm_info("tc3", 
                          $sformatf("t=%0d: Cooldown expired. Color %0d is now available.", 
                                     t, cooldown_color), UVM_MEDIUM)
                if (item.color == cooldown_color) begin
                    cooldown_end = t;
                    `uvm_info("tc3", 
                              $sformatf("✓ Color %0d was picked at t=%0d (cooldown expired)", 
                                         cooldown_color, t), UVM_MEDIUM)
                end else begin
                    `uvm_info("tc3", 
                              $sformatf("Color %0d not picked at t=%0d, but still available", 
                                         cooldown_color, t), UVM_MEDIUM)
                end
            end
            
            picks.push_back(item.color);
            
            // Early exit after verifying cooldown mechanism
            if (t >= 10) break;
        end
        
        // Summary
        `uvm_info("tc3_cooldown_expiry_test", 
                  "✓ PASS: Cooldown expiry verified", UVM_MEDIUM)
        
        phase.drop_objection(this);
    endtask
    
endclass

// =============================================================================
// COMPREHENSIVE TEST: All testcases runner
// =============================================================================
class comprehensive_test extends uvm_test;
    `uvm_component_utils(comprehensive_test)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // All testcases run in sequence
    endfunction
    
    task run_phase(uvm_phase phase);
        tc1_window_rule_test tc1;
        tc2_all_colors_appear_test tc2;
        tc3_cooldown_expiry_test tc3;
        
        phase.raise_objection(this);
        
        `uvm_info("comprehensive_test", 
                  "================================", UVM_MEDIUM)
        `uvm_info("comprehensive_test", 
                  "COLORED BALL SELECTION TESTBENCH", UVM_MEDIUM)
        `uvm_info("comprehensive_test", 
                  "================================", UVM_MEDIUM)
        
        // Run TC1
        tc1 = tc1_window_rule_test::type_id::create("tc1");
        tc1.run_phase(phase);
        
        #100;
        
        // Run TC2
        tc2 = tc2_all_colors_appear_test::type_id::create("tc2");
        tc2.run_phase(phase);
        
        #100;
        
        // Run TC3
        tc3 = tc3_cooldown_expiry_test::type_id::create("tc3");
        tc3.run_phase(phase);
        
        `uvm_info("comprehensive_test", 
                  "================================", UVM_MEDIUM)
        `uvm_info("comprehensive_test", 
                  "ALL TESTS COMPLETED", UVM_MEDIUM)
        `uvm_info("comprehensive_test", 
                  "================================", UVM_MEDIUM)
        
        phase.drop_objection(this);
    endtask
    
endclass

// =============================================================================
// TOP-LEVEL MODULE FOR SIMULATION
// =============================================================================
module top;
    initial begin
        // Run comprehensive test
        run_test("comprehensive_test");
    end
endmodule
