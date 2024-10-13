module replay_nak_control (
    input logic clk,
    input logic reset_n,

    // Replay control inputs
    input logic [15:0] ackd_flit_seq_num,         // Acknowledged FLIT sequence number
    input logic replay_scheduled_in,              // Replay scheduled flag (input to preserve external state)
    input logic replay_in_progress_in,            // Replay in progress flag (input to preserve external state)
    input logic [15:0] tx_retry_buffer_seq_num,   // Payload FLIT Sequence Number in TX Retry Buffer (N + 1)

    // Nak handling inputs
    input logic valid_nak_flit,                   // Valid Nak Flit received
    input logic [15:0] nak_flit_seq_num,          // Nak Flit Sequence Number N
    input logic [15:0] nak_ignore_flit_seq_num_in,// NAK Ignore Flit Sequence Number (input to preserve external state)
    input logic nak_ignore_window_elapsed,        // Nak Ignore Window elapsed flag
    input logic valid_standard_nak_flit,          // Standard Nak Flit flag
    input logic valid_selective_nak_flit,         // Selective Nak Flit flag

    // Outputs
    output logic replay_scheduled_out,            // Replay scheduled output
    output logic [1:0] replay_scheduled_type_out, // Replay type (STANDARD or SELECTIVE)
    output logic [15:0] tx_replay_flit_seq_num_out, // TX Replay FLIT Sequence Number
    output logic [15:0] nak_ignore_flit_seq_num_out,// Updated Nak Ignore Flit Sequence Number
    output logic replay_timeout_out,              // Replay timeout flag
    output logic replay_timer_timeout_error_out   // Replay Timer Timeout error
);

    // Replay types definition
    typedef enum logic [1:0] {
        STANDARD_REPLAY  = 2'b01,
        SELECTIVE_REPLAY = 2'b10
    } replay_type_t;

    // Intermediate signals
    logic replay_scheduled_internal;
    logic [15:0] nak_ignore_flit_seq_num_internal;
    logic [15:0] replay_timeout_flit_count;

    // Reset or maintain state
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            // Reset all outputs and internal signals
            replay_scheduled_out <= 1'b0;
            tx_replay_flit_seq_num_out <= 16'b0;
            replay_scheduled_type_out <= 2'b0;
            nak_ignore_flit_seq_num_out <= 16'b0;
            replay_timeout_out <= 1'b0;
            replay_timer_timeout_error_out <= 1'b0;
            replay_timeout_flit_count <= 16'b0;
        end else begin
            // Default to keeping state
            replay_scheduled_out <= replay_scheduled_in;
            nak_ignore_flit_seq_num_internal <= nak_ignore_flit_seq_num_in;

            // Replay scheduling logic (Nak handling)
            if (valid_nak_flit && !replay_scheduled_in && !replay_in_progress_in) begin
                if ((nak_ignore_flit_seq_num_in != nak_flit_seq_num) || nak_ignore_window_elapsed) begin
                    if (tx_retry_buffer_seq_num == (nak_flit_seq_num + 1)) begin
                        // Set replay scheduled and update relevant values
                        replay_scheduled_out <= 1'b1;
                        tx_replay_flit_seq_num_out <= nak_flit_seq_num + 1;
                        nak_ignore_flit_seq_num_internal <= nak_flit_seq_num;

                        // Set the type of replay based on Nak Flit type
                        if (valid_standard_nak_flit) begin
                            replay_scheduled_type_out <= STANDARD_REPLAY;
                        end else if (valid_selective_nak_flit) begin
                            replay_scheduled_type_out <= SELECTIVE_REPLAY;
                        end
                    end
                end
            end

            // Replay transition: from Selective Replay to Standard Replay
            if (valid_standard_nak_flit && 
                (nak_flit_seq_num + 1 == tx_replay_flit_seq_num_out) &&
                replay_scheduled_out && 
                !replay_in_progress_in && 
                (replay_scheduled_type_out == SELECTIVE_REPLAY)) begin
                
                // Switch to Standard Replay
                replay_scheduled_out <= 1'b1;
                tx_replay_flit_seq_num_out <= tx_replay_flit_seq_num_out; // Keep the same sequence number
                replay_scheduled_type_out <= STANDARD_REPLAY;
            end

            // Replay timeout logic
            if (replay_timeout_flit_count >= 16'd1500 && 
                replay_scheduled_out == 1'b0 && 
                replay_in_progress_in == 1'b0) begin
                replay_timeout_out <= 1'b1; // Set timeout flag
                replay_timer_timeout_error_out <= 1'b1; // Log timeout error
            end else begin
                replay_timeout_out <= 1'b0;
                replay_timer_timeout_error_out <= 1'b0;
            end

            // Increment the replay timeout FLIT count
            replay_timeout_flit_count <= replay_timeout_flit_count + 1;
        end
    end

endmodule
