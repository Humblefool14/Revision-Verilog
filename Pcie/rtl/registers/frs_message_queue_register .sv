module frs_message_queue_register #(
    parameter int QUEUE_DEPTH_WIDTH = 12,
    parameter int REASON_WIDTH = 4,
    parameter int FUNCTION_ID_WIDTH = 16,
    parameter int MAX_QUEUE_SIZE = 4096 // 2^12, matching QUEUE_DEPTH_WIDTH
) (
    input logic clk,
    input logic rst_n,
    input logic [31:0] write_data,
    input logic write_enable,
    input logic message_received,
    input logic [FUNCTION_ID_WIDTH-1:0] new_message_function_id,
    input logic [REASON_WIDTH-1:0] new_message_reason,
    output logic [31:0] read_data,
    output logic message_removed
);

    // Register bit fields
    logic [QUEUE_DEPTH_WIDTH-1:0] frs_message_queue_depth;
    logic [REASON_WIDTH-1:0] frs_message_queue_reason;
    logic [FUNCTION_ID_WIDTH-1:0] frs_message_queue_function_id;

    // Synthesizable queue implementation
    logic [FUNCTION_ID_WIDTH-1:0] function_id_queue [MAX_QUEUE_SIZE-1:0];
    logic [REASON_WIDTH-1:0] reason_queue [MAX_QUEUE_SIZE-1:0];
    logic [$clog2(MAX_QUEUE_SIZE)-1:0] queue_head, queue_tail;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            frs_message_queue_depth <= '0;
            frs_message_queue_reason <= '0;
            frs_message_queue_function_id <= '0;
            queue_head <= '0;
            queue_tail <= '0;
            message_removed <= 1'b0;
        end else begin
            message_removed <= 1'b0;

            if (message_received && frs_message_queue_depth < MAX_QUEUE_SIZE) begin
                // Add new message to queue
                function_id_queue[queue_tail] <= new_message_function_id;
                reason_queue[queue_tail] <= new_message_reason;
                queue_tail <= (queue_tail + 1) % MAX_QUEUE_SIZE;
                frs_message_queue_depth <= frs_message_queue_depth + 1;
            end

            if (write_enable && write_data[0] && frs_message_queue_depth > 0) begin
                // Remove oldest message from queue
                queue_head <= (queue_head + 1) % MAX_QUEUE_SIZE;
                frs_message_queue_depth <= frs_message_queue_depth - 1;
                message_removed <= 1'b1;
            end

            // Update register fields with oldest message in queue
            if (frs_message_queue_depth > 0) begin
                frs_message_queue_function_id <= function_id_queue[queue_head];
                frs_message_queue_reason <= reason_queue[queue_head];
            end else begin
                frs_message_queue_function_id <= '0;
                frs_message_queue_reason <= '0;
            end
        end
    end

    // Read data assignment
    assign read_data = {frs_message_queue_depth, frs_message_queue_reason, frs_message_queue_function_id};

endmodule