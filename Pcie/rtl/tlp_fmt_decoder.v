module tlp_decoder(
    input wire [2:0] tlp_fmt,    // TLP Format field (3 bits)
    input wire [4:0] tlp_type,   // TLP Type field (5 bits)
    output reg is_memory_read,           // Memory read request
    output reg is_memory_read_locked,    // Memory read locked request
    output reg is_io_read,               // IO read request
    output reg is_io_write,              // IO write request
    output reg is_config_read_type0,     // Config read Type 0 request
    output reg is_config_write_type0,    // Config write Type 0 request
    output reg is_deprecated,            // Deprecated request
    output reg is_message_request,       // Message request
    output reg is_message_data_load,     // Message data load request
    output reg is_completion_request,    // Completion request
    output reg is_completion_data_request, // Completion data request
    output reg is_completion_locked_memory, // Completion for locked memory without data request
    output reg is_completion_locked_memory_data, // Completion for locked memory with data request
    output reg is_fetch_and_add_request, // Fetch and Add request
    output reg is_unconditional_swap_request, // Unconditional Swap request
    output reg is_compare_and_swap_request, // Compare and Swap request
    output reg is_local_tlp,             // Local TLP request
    output reg is_end_to_end_tlp         // End-to-End TLP request
);

    always @* begin
        // Memory read request
        is_memory_read = (tlp_fmt[2:1] == 2'b00) && (tlp_type == 5'b00000);
        
        // Memory read locked request
        is_memory_read_locked = (tlp_fmt[2:1] == 2'b00) && (tlp_type == 5'b00001);

        // IO read request
        is_io_read = (tlp_fmt[2:1] == 2'b000) && (tlp_type == 5'b00010);
        
        // IO write request
        is_io_write = (tlp_fmt[2:1] == 2'b010) && (tlp_type == 5'b00010);

        // Config read Type 0 request
        is_config_read_type0 = (tlp_fmt == 3'b000) && (tlp_type == 5'b00100);

        // Config write Type 0 request
        is_config_write_type0 = (tlp_fmt == 3'b010) && (tlp_type == 5'b00100);

        // Deprecated request
        is_deprecated = (tlp_fmt == 3'b000) && (tlp_type == 5'b11011);

        // Message request
        is_message_request = (tlp_fmt == 3'b001) && (tlp_type[4] == 1);

        // Message data load request
        is_message_data_load = (tlp_fmt == 3'b011) && (tlp_type[4] == 1);

        // Completion request
        is_completion_request = (tlp_fmt == 3'b000) && (tlp_type == 5'b01010);

        // Completion data request
        is_completion_data_request = (tlp_fmt == 3'b010) && (tlp_type == 5'b01010);

        // Completion for locked memory without data request
        is_completion_locked_memory = (tlp_fmt == 3'b000) && (tlp_type == 5'b01011);

        // Completion for locked memory with data request
        is_completion_locked_memory_data = (tlp_fmt == 3'b010) && (tlp_type == 5'b01011);

        // Fetch and Add request
        is_fetch_and_add_request = (tlp_fmt[2] == 1) && (tlp_type == 5'b01100);

        // Unconditional Swap request
        is_unconditional_swap_request = (tlp_fmt[2] == 1) && (tlp_type == 5'b01101);

        // Compare and Swap request
        is_compare_and_swap_request = (tlp_fmt[2] == 1) && (tlp_type == 5'b01110);

        // Local TLP request
        is_local_tlp = (tlp_fmt == 3'b100) && (tlp_type[3] == 0);

        // End-to-End TLP request
        is_end_to_end_tlp = (tlp_fmt == 3'b100) && (tlp_type[3] == 1);
    end

endmodule