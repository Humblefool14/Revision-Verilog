module Parameterized_DCache_Arbiter #(
    parameter NUM_PORTS = 2,
    parameter PORT_WIDTH = 1,  // Width of each port's request type
    parameter PRIORITY_SCHEME = "ROUND_ROBIN"  // Can be "ROUND_ROBIN", "FIXED", or "WEIGHTED"
) (
    input wire clk,
    input wire rst,
    
    // Request signals
    input wire [NUM_PORTS-1:0] req_valid,
    input wire [NUM_PORTS*PORT_WIDTH-1:0] req_type,
    input wire [NUM_PORTS-1:0] req_abort,
    
    // Response signals
    input wire resp_done,
    input wire resp_ready,
    
    // Arbiter output
    output reg [NUM_PORTS-1:0] grant,
    output wire [$clog2(NUM_PORTS)-1:0] selected_port,
    output wire [PORT_WIDTH-1:0] selected_type
);

    reg [NUM_PORTS-1:0] req_pending;
    reg [$clog2(NUM_PORTS)-1:0] last_granted;
    reg arbiter_busy;

    wire [NUM_PORTS-1:0] next_grant;
    reg [$clog2(NUM_PORTS)-1:0] next_port;

    // Priority encoder for FIXED priority scheme
    function [$clog2(NUM_PORTS)-1:0] priority_encode;
        input [NUM_PORTS-1:0] requests;
        integer i;
        begin
            priority_encode = 0;
            for (i = 0; i < NUM_PORTS; i = i + 1) begin
                if (requests[i]) begin
                    priority_encode = i[$clog2(NUM_PORTS)-1:0];
                    break;
                end
            end
        end
    endfunction

    // Round-robin arbiter
    function [NUM_PORTS-1:0] round_robin_arbiter;
        input [NUM_PORTS-1:0] requests;
        input [$clog2(NUM_PORTS)-1:0] last;
        integer i;
        reg [2*NUM_PORTS-1:0] double_req;
        begin
            double_req = {requests, requests};
            round_robin_arbiter = 0;
            for (i = 0; i < NUM_PORTS; i = i + 1) begin
                if (double_req[last + i + 1]) begin
                    round_robin_arbiter[last + i + 1 - NUM_PORTS] = 1'b1;
                    break;
                end
            end
        end
    endfunction

    // Arbiter logic
    always @(*) begin
        if (PRIORITY_SCHEME == "ROUND_ROBIN") begin
            next_grant = round_robin_arbiter(req_pending, last_granted);
            next_port = priority_encode(next_grant);
        end else if (PRIORITY_SCHEME == "FIXED") begin
            next_port = priority_encode(req_pending);
            next_grant = (1 << next_port);
        end else begin // WEIGHTED or other schemes can be implemented here
            next_grant = round_robin_arbiter(req_pending, last_granted);
            next_port = priority_encode(next_grant);
        end
    end

    // Update arbiter state
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            req_pending <= 0;
            last_granted <= 0;
            arbiter_busy <= 0;
            grant <= 0;
        end else begin
            if (resp_done || req_abort[selected_port]) begin
                req_pending[selected_port] <= 0;
                arbiter_busy <= 0;
                grant <= 0;
            end

            if (!arbiter_busy && resp_ready) begin
                req_pending <= req_pending | req_valid;
                if (|next_grant) begin
                    grant <= next_grant;
                    last_granted <= next_port;
                    arbiter_busy <= 1;
                end
            end
        end
    end

    // Output assignment
    assign selected_port = priority_encode(grant);
    assign selected_type = req_type[selected_port*PORT_WIDTH +: PORT_WIDTH];

endmodule