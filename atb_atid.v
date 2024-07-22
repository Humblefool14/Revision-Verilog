module atid_generator (
    input wire clk,
    input wire resetn,
    input wire increment,
    output reg [7:0] atid
);
    // Next ATID value
    reg [7:0] next_atid;

    always @(posedge clk or negedge resetn) begin
        if (!resetn) begin
            atid <= 8'h01;  // Initialize to the first valid ID
        end else if (increment) begin
            atid <= next_atid;
        end
    end

    always @(*) begin
        // Calculate the next ATID value
        if (atid == 8'h6F)
            next_atid = 8'h80;  // Skip 0x70 to 0x7F
        else if (atid == 8'hFF)
            next_atid = 8'h01;  // Wrap around, skipping 0x00
        else
            next_atid = atid + 8'h01;
    end
endmodule