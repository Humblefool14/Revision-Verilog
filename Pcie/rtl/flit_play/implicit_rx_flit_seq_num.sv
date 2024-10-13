module implicit_rx_flit_seq_num (
    input  logic        clk,
    input  logic        reset_n,
    
    // Input signals
    input  logic        validPayloadFlitReceived,
    input  logic        validNopFlitReceived,
    input  logic        validNonIdleExplicitSeqNumFlitReceived,
    input  logic        explicitSeqNumFlitReceived,
    input  logic        invalidFlitReceived,
    input  logic        nonIdleExplicitSeqNumFlitRcvd,
    input  logic        priorFlitWasPayload,
    input  logic        nakWithdrawalAllowed,
    input  logic        flitseqnum0,
    input  logic        idleFlitReceived,
    input  logic        nonExplicitSeqNumFlitReceived,
    input  logic [7:0]  flitSeqNum,
    
    // Output signal
    output logic [7:0]  implicitRxFlitSeqNum
);

    logic [7:0] next_implicitRxFlitSeqNum;

    always_comb begin
        // Default: maintain current value
        next_implicitRxFlitSeqNum = implicitRxFlitSeqNum;

        if (idleFlitReceived || 
            (explicitSeqNumFlitReceived && flitseqnum0) ||
            (!nonIdleExplicitSeqNumFlitRcvd && (invalidFlitReceived || nonExplicitSeqNumFlitReceived)) ||
            (validNopFlitReceived && !explicitSeqNumFlitReceived && 
             (!nakWithdrawalAllowed || (nakWithdrawalAllowed && priorFlitWasPayload))) ||
            (validPayloadFlitReceived && nakWithdrawalAllowed && !priorFlitWasPayload)) begin
            // No change to next_implicitRxFlitSeqNum
        end else if (validNonIdleExplicitSeqNumFlitReceived && flitSeqNum != 0) begin
            next_implicitRxFlitSeqNum = flitSeqNum;
        end else if (nonIdleExplicitSeqNumFlitRcvd) begin
            if ((validPayloadFlitReceived && !explicitSeqNumFlitReceived && !nakWithdrawalAllowed) ||
                (validPayloadFlitReceived && !explicitSeqNumFlitReceived && priorFlitWasPayload && nakWithdrawalAllowed) ||
                invalidFlitReceived) begin
                next_implicitRxFlitSeqNum = implicitRxFlitSeqNum + 1;
            end
        end else if (validNopFlitReceived && nakWithdrawalAllowed && !priorFlitWasPayload) begin
            next_implicitRxFlitSeqNum = implicitRxFlitSeqNum - 1;
        end
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            implicitRxFlitSeqNum <= '0;
        end else begin
            implicitRxFlitSeqNum <= next_implicitRxFlitSeqNum;
        end
    end

endmodule
