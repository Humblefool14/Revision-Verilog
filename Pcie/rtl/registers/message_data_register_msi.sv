module message_data_register_msi (
    input wire clk,
    input wire rst_n,
    input wire msi_enable,
    input wire [2:0] multiple_message_enable,
    input wire [15:0] write_data,
    input wire write_enable,
    output reg [15:0] read_data
);

    reg [15:0] message_data;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            message_data <= 16'h0000;
        end else if (write_enable && msi_enable) begin
            case (multiple_message_enable)
                3'b000: message_data <= message_data; // No modification allowed
                3'b001: message_data <= {message_data[15:1], write_data[0]};
                3'b010: message_data <= {message_data[15:2], write_data[1:0]};
                3'b011: message_data <= {message_data[15:3], write_data[2:0]};
                3'b100: message_data <= {message_data[15:4], write_data[3:0]};
                default: message_data <= write_data; // Full modification for 101 and above
            endcase
        end
    end

    always @(*) begin
        read_data = message_data;
    end

endmodule