module frs_queueing_status_register #(
    parameter int REGISTER_WIDTH = 16
) (
    input logic clk,
    input logic rst_n,
    input logic link_dl_down,
    input logic frs_message_received_set,
    input logic frs_message_overflow_set,
    input logic [REGISTER_WIDTH-1:0] write_data,
    input logic write_enable,
    output logic [REGISTER_WIDTH-1:0] read_data
);

    // Register bit fields
    logic frs_message_received;
    logic frs_message_overflow;
    logic [REGISTER_WIDTH-3:0] rsvdz;

    // RW1C logic for FRS Message Received
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            frs_message_received <= 1'b0; // Default value is 0b
        end else if (link_dl_down) begin
            frs_message_received <= 1'b0; // Clear when Link is DL_Down
        end else if (frs_message_received_set) begin
            frs_message_received <= 1'b1; // Set when new FRS Message is Received
        end else if (write_enable && write_data[0]) begin
            frs_message_received <= 1'b0; // Clear on write of 1
        end
    end

    // RW1C logic for FRS Message Overflow
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            frs_message_overflow <= 1'b0; // Default value is 0b
        end else if (link_dl_down) begin
            frs_message_overflow <= 1'b0; // Clear when Link is DL_Down
        end else if (frs_message_overflow_set) begin
            frs_message_overflow <= 1'b1; // Set if FRS Message queue is full and new message received
        end else if (write_enable && write_data[1]) begin
            frs_message_overflow <= 1'b0; // Clear on write of 1
        end
    end

    // Reserved bits are always read as 0
    assign rsvdz = '0;

    // Combine all fields into read_data
    assign read_data = {rsvdz, frs_message_overflow, frs_message_received};

endmodule