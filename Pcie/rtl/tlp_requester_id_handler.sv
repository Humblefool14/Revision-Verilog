module tlp_requester_id_handler (
    input  wire        is_ari_enabled,     // Signal indicating if ARI is enabled
    input  wire [7:0]  bus_num,           // Bus number
    input  wire [4:0]  device_num,        // Device number (used in non-ARI mode)
    input  wire [2:0]  function_num,      // Function number (used in non-ARI mode)
    input  wire [7:0]  ari_function_num,  // ARI Function number (used in ARI mode)
    output wire [15:0] requester_id       // Output requester ID
);

    // In ARI mode:
    // - Bus number remains in [15:8]
    // - Device number field is repurposed along with Function number to create
    //   an 8-bit Function number field [7:0]
    
    // In non-ARI mode:
    // - Bus number in [15:8]
    // - Device number in [7:3]
    // - Function number in [2:0]

    reg [15:0] requester_id_internal;

    always @* begin
        if (is_ari_enabled) begin
            // ARI mode: 8-bit bus number + 8-bit function number
            requester_id_internal[15:8] = bus_num;
            requester_id_internal[7:0]  = ari_function_num;
        end else begin
            // Non-ARI mode: 8-bit bus number + 5-bit device number + 3-bit function number
            requester_id_internal[15:8] = bus_num;
            requester_id_internal[7:3]  = device_num;
            requester_id_internal[2:0]  = function_num;
        end
    end

    assign requester_id = requester_id_internal;

endmodule