module power_management_decoder (
    input  logic [7:0] byte_0,
    output logic [2:0] pm_type
);

    // Decode Power Management type
    always_comb begin
        case (byte_0[7:3])
            5'b00100: begin
                case (byte_0[2:0])
                    3'b000: pm_type = 3'b000; // PM_Enter_L1
                    3'b001: pm_type = 3'b001; // PM_Enter_L23
                    3'b010: pm_type = 3'b010; // PM_Active_State_Request_L1
                    3'b100: pm_type = 3'b011; // PM_Request_Ack
                    default: pm_type = 3'b111; // Reserved
                endcase
            end
            default: pm_type = 3'b111; // Reserved
        endcase
    end

endmodule