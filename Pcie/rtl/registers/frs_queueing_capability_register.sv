module frs_queueing_capability_register #(
    parameter int INITIAL_QUEUE_DEPTH = 1,
    parameter int MAX_QUEUE_DEPTH = 4095,
    parameter bit SUPPORT_MSI_X = 1
) (
    input logic clk,
    input logic rst_n,
    input logic [4:0] msi_message_count,
    input logic msi_x_enabled,
    input logic [5:0] msi_x_table_size,
    input logic [11:0] hw_queue_depth,
    output logic [31:0] read_data
);

    // Register bit fields
    logic [11:0] frs_queue_max_depth;
    logic [4:0] frs_interrupt_message_number;
    logic [10:0] rsvdp_high;
    logic [3:0] rsvdp_low;

    // HwInit logic for FRS Queue Max Depth
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            frs_queue_max_depth <= INITIAL_QUEUE_DEPTH[11:0];
        end else begin
            // Hardware can update this value up to MAX_QUEUE_DEPTH
            frs_queue_max_depth <= (hw_queue_depth > MAX_QUEUE_DEPTH[11:0]) ? MAX_QUEUE_DEPTH[11:0] : hw_queue_depth;
        end
    end

    // RO logic for FRS Interrupt Message Number
    always_comb begin
        if (SUPPORT_MSI_X && msi_x_enabled) begin
            // For MSI-X, use the table size (up to 32)
            frs_interrupt_message_number = (msi_x_table_size > 5'd31) ? 5'd31 : msi_x_table_size;
        end else begin
            // For MSI, use the message count
            frs_interrupt_message_number = msi_message_count;
        end
    end

    // Reserved fields are always 0
    assign rsvdp_high = 11'b0;
    assign rsvdp_low = 4'b0;

    // Combine all fields into read_data
    assign read_data = {rsvdp_high, frs_interrupt_message_number, rsvdp_low, frs_queue_max_depth};

endmodule