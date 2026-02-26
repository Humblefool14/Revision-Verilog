module assertion_template (
    input logic clk,
    input logic rst_n,
    // TODO: Define input here
);

    property check_property;
        @(posedge clk) disable iff (!rst_n)
           vld |-> data;
    endproperty

    assert property (check_property)
        else $error("Assertion failed at time %0t:$time);

endmodule

//Write UVM SystemVerilog assertion to verify that signal "data" is high (logic 1) whenever signal "valid" is asserted (logic 1). 
//This is a basic implication property: when valid=1, data must equal 1 in the same clock cycle.
/*
Test Case 1 - Basic Pass: valid=1, data=1 for several cycles. Assertion passes.
Test Case 2 - Basic Fail: valid=1, data=0 for one cycle. Assertion fails.
Test Case 3 - No Implication: valid=0, data=0 or data=1. Assertion passes (antecedent false, property vacuously true).
Test Case 4 - X/Z Handling: Drive valid=X or data=X. Verify assertion behavior per chosen handling (gated or fails).
Test Case 5 - Reset Behavior: Assert reset. Drive valid=1, data=0. Assertion should NOT fail (disabled during reset). Release reset, repeat. Assertion should fail.
*/ 
