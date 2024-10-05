module xy_router
#(
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 8,
    parameter X_WIDTH = 4,
    parameter Y_WIDTH = 4
)
(
    input wire clk,
    input wire rst,
    
    // Input port
    input wire [DATA_WIDTH-1:0] data_in,
    input wire [ADDR_WIDTH-1:0] addr_in,
    input wire valid_in,
    output wire ready_in,
    
    // Output ports (North, East, South, West, Local)
    output wire [4:0][DATA_WIDTH-1:0] data_out,
    output wire [4:0] valid_out,
    input wire [4:0] ready_out,
    
    // Router's own address
    input wire [X_WIDTH-1:0] router_x,
    input wire [Y_WIDTH-1:0] router_y
);

    // Extract destination coordinates from address
    wire [X_WIDTH-1:0] dest_x = addr_in[ADDR_WIDTH-1:ADDR_WIDTH-X_WIDTH];
    wire [Y_WIDTH-1:0] dest_y = addr_in[ADDR_WIDTH-X_WIDTH-1:ADDR_WIDTH-X_WIDTH-Y_WIDTH];

    // Determine output direction
    wire go_north = dest_y < router_y;
    wire go_east  = dest_x > router_x;
    wire go_south = dest_y > router_y;
    wire go_west  = dest_x < router_x;
    wire go_local = (dest_x == router_x) && (dest_y == router_y);

    // XY routing logic
    wire [4:0] route_to;
    assign route_to[4] = go_north;
    assign route_to[3] = !go_north && go_east;
    assign route_to[2] = !go_north && !go_east && go_south;
    assign route_to[1] = !go_north && !go_east && !go_south && go_west;
    assign route_to[0] = go_local;

    // Output assignment
    genvar i;
    generate
        for (i = 0; i < 5; i = i + 1) begin : gen_outputs
            assign data_out[i] = (route_to[i]) ? data_in : {DATA_WIDTH{1'b0}};
            assign valid_out[i] = valid_in && route_to[i];
        end
    endgenerate

    // Ready signal for input
    assign ready_in = |(ready_out & route_to);

endmodule