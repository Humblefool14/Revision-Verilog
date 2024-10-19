module tlp_receiver #(
    parameter SEQ_NUM_WIDTH = 12,
    parameter TIMER_WIDTH = 16,
    parameter TIMER_THRESHOLD = 16'h00FF
) (
    input  logic                     clk,
    input  logic                     rst_n,
    input  logic [SEQ_NUM_WIDTH-1:0] rx_seq_num,
    input  logic                     dl_inactive,
    input  logic                     ack_nak_scheduled,
    input  logic                     all_tlps_acknowledged,
    input  logic                     tlp_received,
    input  logic                     tlp_forwarded,
    input  logic                     tlp_nullified,
    input  logic                     lcrc_mismatch,
    input  logic                     received_lcrc,
    output logic [SEQ_NUM_WIDTH-1:0] next_rcv_seq,
    output logic                     nak_scheduled,
    output logic [TIMER_WIDTH-1:0]   timer_value,
    output logic                     timer_expired,
    output logic                     bad_tlp_error,
    output logic                     discard_tlp
);

    logic timer_running, start_timer;
    logic tlp_corrupt;

    // Determine if TLP is corrupt
    assign tlp_corrupt = tlp_nullified && lcrc_mismatch;

        // Check for sequence number mismatch
    assign sequence_mismatch = (rx_seq_num != next_rcv_seq);
    assign sequence_match    = (rx_seq_num == next_rcv_seq) && tlp_valid;


    // Check for duplicate TLP
    always_comb begin
        logic [SEQ_NUM_WIDTH:0] difference;
        difference = next_rcv_seq - rx_seq_num;
        duplicate_tlp = (difference[SEQ_NUM_WIDTH-1:0] <= 12'd2048) && sequence_mismatch;
    end

    // Next receive sequence logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n || dl_inactive) begin
            next_rcv_seq  <= '0;
            nak_scheduled <= 1'b0;
            ack_scheduled <= 1'b0;
            bad_tlp_error <= 1'b0;
            discard_tlp   <= 1'b0;
            report_error   <= 1'b0;
        end else begin
            if (tlp_received) begin
                if (calculated_lcrc != received_lcrc) begin
                    lcrc_mismatch <= 1'b1;
                    discard_tlp   <= 1'b1;
                    bad_tlp_error <= 1'b1;
                end 
                if (tlp_corrupt && !nak_scheduled) begin
                    nak_scheduled <= 1'b1;
                    bad_tlp_error <= 1'b1;
                    discard_tlp   <= 1'b1;
                end else if (sequence_match) begin
                // Forward the TLP to the Receive Transaction Layer
                forward_tlp     <= 1'b1;
                forward_tlp_start <= tlp_start;
                forward_tlp_end   <= tlp_end;
                forwarded_tlp_data <= tlp_data; // Note: Assumes header fields are removed externally
                
                // Increment NEXT_RCV_SEQ
                next_rcv_seq <= next_rcv_seq + 1'b1;
                
                // Clear NAK_SCHEDULED flag if set
                nak_scheduled <= 1'b0;
                discard_tlp   <= 1'b0;
                bad_tlp_error <= 1'b0;
                report_error  <= 1'b0;
                end else if (sequence_mismatch) begin
                    discard_tlp   <= 1'b1;
                    if (duplicate_tlp && !ack_scheduled) begin
                        ack_scheduled <= 1'b1;
                        nak_scheduled <= 1'b0;
                        bad_tlp_error <= 1'b0;
                        report_error  <= 1'b0;
                    end
                    end else if (out_of_sequence && !nak_scheduled) begin
                    nak_scheduled <= 1'b1;
                    bad_tlp_error <= 1'b1;
                    report_error  <= 1'b1;
                end
                else begin
                    next_rcv_seq <= rx_seq_num + 1'b1;
                    discard_tlp <= 1'b0;
                    ack_scheduled <= 1'b0; 
                end
            end

            if (ack_nak_scheduled) begin
                nak_scheduled <= 1'b0;
                ack_scheduled <= 1'b0;
            end
        end
    end


    // AckNak latency timer logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n || dl_inactive) begin
            timer_value   <= '0;
            timer_running <= 1'b0;
        end else if (ack_nak_scheduled || all_tlps_acknowledged) begin
            timer_value   <= '0;
            timer_running <= 1'b0;
        end else if (start_timer) begin
            timer_value   <= 1;  // Start counting from 1
            timer_running <= 1'b1;
        end else if (timer_running) begin
            timer_value   <= timer_value + 1'b1;
        end
    end

    // Timer start logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n || dl_inactive) begin
            start_timer <= 1'b0;
        end else if (tlp_received && !timer_running) begin
            start_timer <= tlp_forwarded;
        end
    end

    // Timer expiration logic
    assign timer_expired = (timer_value >= TIMER_THRESHOLD);

endmodule