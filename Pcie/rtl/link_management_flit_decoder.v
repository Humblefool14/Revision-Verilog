module link_management_flit_decoder (
    input  logic [31:0] packet_data,
    output logic        is_link_management_dllp,
    output logic        is_l0p_type,
    output logic [1:0]  reserved,
    output logic        l0p_priority,
    output logic [3:0]  l0p_cmd,
    output logic [2:0]  response_payload,
    output logic [2:0]  link_width
);

    // Decode Link Management DLLP
    assign is_link_management_dllp = (packet_data[31:24] == 8'h28);

    // Decode Link Mgmt Type (L0p)
    assign is_l0p_type = (packet_data[23:16] == 8'h00);

    // Decode Reserved bits
    assign reserved = packet_data[17:16];

    // Decode L0p Priority
    assign l0p_priority = packet_data[15];

    // Decode L0p Cmd
    assign l0p_cmd = packet_data[14:11];

    // Decode Response Payload
    assign response_payload = packet_data[10:8];

    // Decode Link Width
    assign link_width = packet_data[2:0];

    // Assertion to check if the packet is a valid Link Management DLLP
    always_ff @(posedge clk) begin
        assert(is_link_management_dllp && is_l0p_type)
        else $error("Invalid Link Management DLLP or L0p type");
    end

endmodule