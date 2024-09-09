module priority_arbiter #(
    parameter NUM_PORTS = 4
)(
    input wire clk,
    input wire rst,
    input wire [NUM_PORTS-1:0] high_priority_req,
    input wire [NUM_PORTS-1:0] low_priority_req,
    output reg [NUM_PORTS-1:0] grant
);

    reg [NUM_PORTS-1:0] high_priority_mask;
    reg [NUM_PORTS-1:0] low_priority_mask;
    reg [NUM_PORTS-1:0] next_grant;
    wire [NUM_PORTS-1:0] high_priority_grant;
    wire [NUM_PORTS-1:0] low_priority_grant;
    
    // Round-robin arbiter for high priority requests
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            high_priority_mask <= {NUM_PORTS{1'b1}};
        end else if (|high_priority_req) begin
            high_priority_mask <= {high_priority_mask[NUM_PORTS-2:0], high_priority_mask[NUM_PORTS-1]};
        end
    end
    
    assign high_priority_grant = high_priority_req & high_priority_mask & (~high_priority_req + 1);
    
    // Round-robin arbiter for low priority requests
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            low_priority_mask <= {NUM_PORTS{1'b1}};
        end else if (|low_priority_req) begin
            low_priority_mask <= {low_priority_mask[NUM_PORTS-2:0], low_priority_mask[NUM_PORTS-1]};
        end
    end
    
    assign low_priority_grant = low_priority_req & low_priority_mask & (~low_priority_req + 1);
    
    // Priority selection logic
    always @(*) begin
        if (|high_priority_req) begin
            next_grant = high_priority_grant;
        end else begin
            next_grant = low_priority_grant;
        end
    end
    
    // Output register
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            grant <= {NUM_PORTS{1'b0}};
        end else begin
            grant <= next_grant;
        end
    end

endmodule