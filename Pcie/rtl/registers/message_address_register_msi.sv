module message_address_register_msi (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        msi_enable,
    input  logic [31:0] write_data,
    input  logic        write_enable,
    output logic [31:0] read_data
);

    logic [31:2] message_address;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            message_address <= 30'b0;
        end else if (write_enable && msi_enable) begin
            message_address <= write_data[31:2];
        end
    end

    always_comb begin
        read_data = {message_address, 2'b00};
    end

endmodule