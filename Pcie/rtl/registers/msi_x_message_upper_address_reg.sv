module msi_x_message_upper_address_register (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        write_enable,
    input  logic [31:0] write_data,
    output logic [31:0] read_data,
    output logic        is_64bit_addressing
);

    logic [31:0] message_upper_address;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            message_upper_address <= 32'h0;  // Reset to zero (undefined state)
        end else if (write_enable) begin
            message_upper_address <= write_data;
        end
    end

    assign read_data = message_upper_address;
    assign is_64bit_addressing = |message_upper_address;  // Non-zero if any bit is set

    // Assertions for validation
    assert property (@(posedge clk) disable iff (!rst_n)
        write_enable |-> $stable(message_upper_address) ##1 (message_upper_address == $past(write_data)))
        else $error("Write operation failed");

    initial begin
        $display("Default value of Message Upper Address is undefined (initialized to 0)");
    end

endmodule