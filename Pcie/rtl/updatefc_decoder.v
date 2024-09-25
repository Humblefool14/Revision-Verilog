module updatefc_decoder (
    input  logic [31:0] packet_data,
    output logic [2:0]  update_fc_type,
    output logic        flow_control_type,
    output logic [2:0]  vc,
    output logic [1:0]  hdr_scale,
    output logic [1:0]  data_scale,
    output logic [7:0]  hdr_fc,
    output logic [15:0] data_fc
);

    // Decode UpdateFC type
    always_comb begin
        case (packet_data[31:29])
            3'b100: update_fc_type = 3'b000; // UpdateFC2-P
            3'b101: update_fc_type = 3'b001; // UpdateFC2-NP
            3'b110: update_fc_type = 3'b010; // UpdateFC2-Cpl
            default: update_fc_type = 3'b111; // Reserved
        endcase
    end

    // Decode Flow Control Type
    assign flow_control_type = packet_data[28];

    // Decode VC
    assign vc = packet_data[27:25];

    // Decode Hdr Scale
    assign hdr_scale = packet_data[24:23];

    // Decode Data Scale
    assign data_scale = packet_data[22:21];

    // Decode HdrFC
    assign hdr_fc = packet_data[20:13];

    // Decode DataFC
    assign data_fc = packet_data[15:0];

    // Assertion to check if bits [31:29] are valid
    always_ff @(posedge clk) begin
        assert(packet_data[31:29] inside {3'b100, 3'b101, 3'b110})
        else $error("Invalid UpdateFC type");
    end

endmodule