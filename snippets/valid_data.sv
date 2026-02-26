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
