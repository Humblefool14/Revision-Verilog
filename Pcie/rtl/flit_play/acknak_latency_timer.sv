module acknak_latency_timer (
    input  logic clk,
    input  logic rst_n,
    input  logic dl_inactive,
    input  logic ack_nak_scheduled,
    input  logic all_tlps_acknowledged,
    input  logic tlp_received,
    input  logic tlp_nullified,
    input  logic lcrc_mismatch,
    input  logic tlp_forwarded,
    output logic [15:0] timer_value,  // Assuming a 16-bit timer, adjust as needed
    output logic timer_expired
);
    logic timer_running, start_timer;
    logic tlp_corrupt;

    // Determine if TLP is corrupt
    assign tlp_corrupt = tlp_nullified && lcrc_mismatch;

    logic timer_running;
    logic start_timer;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            timer_value <= 16'h0000;
            timer_running <= 1'b0;
        end else if (dl_inactive) begin
            timer_value <= 16'h0000;
            timer_running <= 1'b0;
        end else if (ack_nak_scheduled) begin
            timer_value <= 16'h0000;
            timer_running <= 1'b0;
        end else if (all_tlps_acknowledged) begin
            timer_value <= 16'h0000;
            timer_running <= 1'b0;
        end else if (start_timer) begin
            timer_value <= 16'h0001;  // Start counting from 1
            timer_running <= 1'b1;
        end else if (timer_running) begin
            timer_value <= timer_value + 1'b1;
        end
    end

    // Logic to start the timer when a TLP is received and forwarded
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            start_timer <= 1'b0;
        end else if (dl_inactive) begin
            start_timer <= 1'b0;
        end else if (tlp_received && !timer_running) begin
            start_timer <= tlp_forwarded;
        end else begin
            start_timer <= 1'b0;
        end
    end

    // Timer expiration logic (example threshold, adjust as needed)
    localparam TIMER_THRESHOLD = 16'h00FF;
    assign timer_expired = (timer_value >= TIMER_THRESHOLD);

endmodule