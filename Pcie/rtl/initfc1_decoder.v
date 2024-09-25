module initfc1_decoder (
    input  logic [31:0] packet_data,
    output logic [2:0]  init_fc1_type,
    output logic        flow_control_type,
    output logic [2:0]  vc,
    output logic [1:0]  hdr_scale,
    output logic [1:0]  data_scale,
    output logic [7:0]  hdr_fc,
    output logic [15:0] data_fc
);

    // Decode InitFC1 type
    always_comb begin
        case (packet_data[31:29])
            3'b010: init_fc1_type = 3'b000; // InitFC1-P
            3'b011: init_fc1_type = 3'b001; // InitFC1-NP
            3'b011: init_fc1_type = 3'b010; // InitFC1-Cpl
            default: init_fc1_type = 3'b111; // Reserved
        endcase
    end

    // Decode Flow Control Type
    assign flow_control_type = packet_data[28];

    // Decode VC
    assign vc = packet_data[27:25];

    // Decode Hdr Scale
    always_comb begin
        case (packet_data[24:23])
            2'b00: hdr_scale = 2'b00; // Infinite Credits if HdrFC = 00h
            2'b01: hdr_scale = 2'b01; // Zero Credits when HdrFC = 00h
            2'b10: hdr_scale = 2'b10; // Merged Shared Credits if HdrFC = 00h
            default: hdr_scale = 2'b11; // Reserved
        endcase
    end

    // Decode Data Scale
    always_comb begin
        case (packet_data[22:21])
            2'b00: data_scale = 2'b00; // Infinite Credits when DataFC = 000h
            2'b01: data_scale = 2'b01; // Zero Credits when DataFC = 000h
            2'b10: data_scale = 2'b10; // Merged Shared Credits when DataFC = 000h
            default: data_scale = 2'b11; // Reserved
        endcase
    end

    // Decode HdrFC and DataFC
    assign hdr_fc = packet_data[20:13];
    assign data_fc = packet_data[15:0];

endmodule