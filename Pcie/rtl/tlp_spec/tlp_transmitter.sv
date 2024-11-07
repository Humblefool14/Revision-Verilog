module tlp_transmitter (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         enable,            // Start TLP transmission
    input  wire [127:0] tlp_data,          // TLP data payload (assuming up to 4 DWs for simplicity)
    input  wire [1:0]   tlp_length,        // Number of DWs in TLP (1 to 4)
    input  wire         tlp_nullified,     // Indicates if TLP is nullified
    output reg          tlp_valid,         // TLP data is valid
    output reg  [7:0]   tlp_symbol,        // TLP symbol data
    output reg          transmission_done  // TLP transmission complete
);

    // States
    localparam IDLE      = 3'b000;
    localparam SEND_STP  = 3'b001;
    localparam SEND_TLP  = 3'b010;
    localparam SEND_EDB  = 3'b011;
    localparam COMPLETE  = 3'b100;

    reg [2:0] state, next_state;
    reg [1:0] dw_count;                    // Counts DWs for TLP transmission
    reg       stp_sent;                    // Flag to ensure STP is sent only once
    reg [127:0] tlp_data_reg;              // Stores TLP data for transmission

    // State machine for TLP transmission
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            dw_count <= 2'd0;
            tlp_valid <= 1'b0;
            tlp_symbol <= 8'h00;
            transmission_done <= 1'b0;
            stp_sent <= 1'b0;
            tlp_data_reg <= 128'h0;
        end else begin
            state <= next_state;
        end
    end

    // State transitions
    always @(*) begin
        case (state)
            IDLE: begin
                if (enable) begin
                    next_state = SEND_STP;
                end else begin
                    next_state = IDLE;
                end
            end

            SEND_STP: begin
                if (stp_sent) begin
                    next_state = SEND_TLP;
                end else begin
                    next_state = SEND_STP;
                end
            end

            SEND_TLP: begin
                if (dw_count == tlp_length - 1) begin
                    if (tlp_nullified) begin
                        next_state = SEND_EDB;
                    end else begin
                        next_state = COMPLETE;
                    end
                end else begin
                    next_state = SEND_TLP;
                end
            end

            SEND_EDB: begin
                next_state = COMPLETE;
            end

            COMPLETE: begin
                if (!enable) begin
                    next_state = IDLE;
                end else begin
                    next_state = COMPLETE;
                end
            end

            default: next_state = IDLE;
        endcase
    end

    // Output logic
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            tlp_valid <= 1'b0;
            tlp_symbol <= 8'h00;
            transmission_done <= 1'b0;
            dw_count <= 2'd0;
            stp_sent <= 1'b0;
            tlp_data_reg <= 128'h0;
        end else begin
            case (state)
                IDLE: begin
                    tlp_valid <= 1'b0;
                    tlp_symbol <= 8'h00;
                    transmission_done <= 1'b0;
                    dw_count <= 2'd0;
                    stp_sent <= 1'b0;
                    if (enable) begin
                        tlp_data_reg <= tlp_data;
                    end
                end

                SEND_STP: begin
                    if (!stp_sent) begin
                        tlp_valid <= 1'b1;
                        tlp_symbol <= 8'hFA; // Example STP token
                        stp_sent <= 1'b1;
                    end else begin
                        tlp_valid <= 1'b0;
                    end
                end

                SEND_TLP: begin
                    tlp_valid <= 1'b1;
                    case (dw_count)
                        2'd0: tlp_symbol <= tlp_data_reg[127:120];
                        2'd1: tlp_symbol <= tlp_data_reg[95:88];
                        2'd2: tlp_symbol <= tlp_data_reg[63:56];
                        2'd3: tlp_symbol <= tlp_data_reg[31:24];
                    endcase
                    dw_count <= dw_count + 1'b1;
                end

                SEND_EDB: begin
                    tlp_valid <= 1'b1;
                    tlp_symbol <= 8'hFB; // Example EDB token
                end

                COMPLETE: begin
                    tlp_valid <= 1'b0;
                    transmission_done <= 1'b1;
                end

                default: begin
                    tlp_valid <= 1'b0;
                    tlp_symbol <= 8'h00;
                end
            endcase
        end
    end

endmodule
