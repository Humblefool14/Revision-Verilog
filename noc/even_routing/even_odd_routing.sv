module noc_router #(
    parameter WIDTH = 32,
    parameter X_SIZE = 4,
    parameter Y_SIZE = 4,
    parameter X_BITS = $clog2(X_SIZE),
    parameter Y_BITS = $clog2(Y_SIZE)
)(
    input wire clk,
    input wire rst,
    input wire [WIDTH-1:0] data_in,
    input wire [X_BITS-1:0] current_x,
    input wire [Y_BITS-1:0] current_y,
    input wire [X_BITS-1:0] dest_x,
    input wire [Y_BITS-1:0] dest_y,
    output reg [WIDTH-1:0] data_out,
    output reg [2:0] direction
);

    localparam EAST  = 3'b000;
    localparam WEST  = 3'b001;
    localparam NORTH = 3'b010;
    localparam SOUTH = 3'b011;
    localparam LOCAL = 3'b100;

    wire x_dimension_done, y_dimension_done;
    wire move_in_x, move_in_y;
    wire odd_column;

    assign x_dimension_done = (current_x == dest_x);
    assign y_dimension_done = (current_y == dest_y);
    assign move_in_x = !x_dimension_done;
    assign move_in_y = x_dimension_done && !y_dimension_done;
    assign odd_column = current_x[0];

    always @(posedge clk or posedge rst) begin
        if (rst) begin
            data_out <= 0;
            direction <= LOCAL;
        end else begin
            data_out <= data_in;
            if (x_dimension_done && y_dimension_done) begin
                direction <= LOCAL;
            end else if (move_in_x) begin
                if (current_x < dest_x) begin
                    if (!odd_column || current_x == X_SIZE-1) begin
                        direction <= EAST;
                    end else begin
                        direction <= move_in_y ? (current_y < dest_y ? NORTH : SOUTH) : EAST;
                    end
                end else begin
                    if (odd_column || current_x == 0) begin
                        direction <= WEST;
                    end else begin
                        direction <= move_in_y ? (current_y < dest_y ? NORTH : SOUTH) : WEST;
                    end
                end
            end else begin // move_in_y
                direction <= (current_y < dest_y) ? NORTH : SOUTH;
            end
        end
    end

endmodule

