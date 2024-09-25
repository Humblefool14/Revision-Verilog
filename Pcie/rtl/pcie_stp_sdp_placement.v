module pcie_stp_sdp_placement #(
    parameter LINK_WIDTH = 16  // Supports 8 or 16
)(
    input wire clk,
    input wire rst_n,
    input wire [LINK_WIDTH-1:0] data_in,
    input wire stp_valid,
    input wire sdp_valid,
    output reg [LINK_WIDTH-1:0] data_out
);

    localparam STP_SYMBOL = 8'hFB;
    localparam SDP_SYMBOL = 8'h5C;

    reg [1:0] stp_lane;
    reg [1:0] sdp_lane;
    reg [2:0] lane_select;

    // Lane selection logic
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            lane_select <= 3'b000;
        end else if (stp_valid || sdp_valid) begin
            if (lane_select == (LINK_WIDTH/4 - 1)) begin
                lane_select <= 3'b000;
            end else begin
                lane_select <= lane_select + 1;
            end
        end
    end

    // Assign lanes for STP and SDP
    always @(*) begin
        stp_lane = {lane_select[1:0], 2'b00};  // Multiply by 4
        sdp_lane = stp_lane;
        
        // If both STP and SDP are valid, place SDP in the next available 4N lane
        if (stp_valid && sdp_valid) begin
            if (sdp_lane == (LINK_WIDTH - 4)) begin
                sdp_lane = 2'b00;
            end else begin
                sdp_lane = sdp_lane + 4;
            end
        end
    end

    // Place symbols in the appropriate lanes
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_out <= {LINK_WIDTH{1'b0}};
        end else begin
            data_out <= data_in;
            if (stp_valid) begin
                data_out[stp_lane*8 +: 8] <= STP_SYMBOL;
            end
            if (sdp_valid) begin
                data_out[sdp_lane*8 +: 8] <= SDP_SYMBOL;
            end
        end
    end

endmodule