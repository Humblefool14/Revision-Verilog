module msi_x_message_data_register (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        write_enable,
    input  logic [31:0] write_data,
    output logic [31:0] read_data
);

    logic [31:0] message_data;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            message_data <= 32'h0;  // Reset to zero (undefined state)
        end else if (write_enable) begin
            message_data <= write_data;
        end
    end

    assign read_data = message_data;

    // Assertions for validation
    assert property (@(posedge clk) disable iff (!rst_n)
        write_enable |-> $stable(message_data) ##1 (message_data == $past(write_data)))
        else $error("Write operation failed");

    assert property (@(posedge clk) disable iff (!rst_n)
        write_enable |-> (write_data[31:0] == write_data[31:0]))
        else $error("All 4 Byte Enables must be set for MSI-X messages");

    initial begin
        $display("Default value of Message Data is undefined (initialized to 0)");
    end

endmodule