module replay_timeout_counter (
    input  logic       clk,                      // Clock
    input  logic       rst_n,                    // Asynchronous reset (active low)
    input  logic       ack,                      // Acknowledgment signal
    input  logic       nak,                      // Negative acknowledgment signal
    input  logic       flit_transmitted,         // Signal for transmitted Payload/NOP flit
    input  logic       tx_retry_buffer_not_empty,// TX Retry Buffer not empty signal
    output logic [10:0] replay_timeout_flit_count // 11-bit Replay Timeout Flit Count
);

    // Counter process
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Asynchronous reset
            replay_timeout_flit_count <= 11'b0;
        end else if (ack || nak) begin
            // Reset counter upon ack or nak that purges the TX Retry Buffer
            replay_timeout_flit_count <= 11'b0;
        end else if (flit_transmitted && tx_retry_buffer_not_empty) begin
            // Increment the REPLAY_TIMEOUT_FLIT_COUNT when a flit is transmitted and the TX Retry Buffer is not empty
            if (replay_timeout_flit_count < 11'h7FF) begin
                replay_timeout_flit_count <= replay_timeout_flit_count + 1;
            end else begin
                // Saturate at 7FFh
                replay_timeout_flit_count <= 11'h7FF;
            end
        end
    end
endmodule