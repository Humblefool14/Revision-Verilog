// Testbench
module noc_router_tb;
    parameter WIDTH = 32;
    parameter X_SIZE = 4;
    parameter Y_SIZE = 4;
    parameter X_BITS = $clog2(X_SIZE);
    parameter Y_BITS = $clog2(Y_SIZE);

    reg clk, rst;
    reg [WIDTH-1:0] data_in;
    reg [X_BITS-1:0] current_x, dest_x;
    reg [Y_BITS-1:0] current_y, dest_y;
    wire [WIDTH-1:0] data_out;
    wire [2:0] direction;

    noc_router #(
        .WIDTH(WIDTH),
        .X_SIZE(X_SIZE),
        .Y_SIZE(Y_SIZE)
    ) dut (
        .clk(clk),
        .rst(rst),
        .data_in(data_in),
        .current_x(current_x),
        .current_y(current_y),
        .dest_x(dest_x),
        .dest_y(dest_y),
        .data_out(data_out),
        .direction(direction)
    );

    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    initial begin
        rst = 1;
        data_in = 32'hDEADBEEF;
        current_x = 0; current_y = 0;
        dest_x = 3; dest_y = 3;
        #10 rst = 0;

        #10 $display("Time=%0t, Direction=%b", $time, direction);
        #10 current_x = 1; $display("Time=%0t, Direction=%b", $time, direction);
        #10 current_x = 2; $display("Time=%0t, Direction=%b", $time, direction);
        #10 current_x = 3; current_y = 1; $display("Time=%0t, Direction=%b", $time, direction);
        #10 current_y = 2; $display("Time=%0t, Direction=%b", $time, direction);
        #10 current_y = 3; $display("Time=%0t, Direction=%b", $time, direction);

        #10 $finish;
    end

endmodule