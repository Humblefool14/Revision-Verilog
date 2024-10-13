module extended_message_data_register_msi (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        extended_message_data_capable,
    input  logic        extended_message_data_enable,
    input  logic        per_vector_masking,
    input  logic [15:0] write_data,
    input  logic        write_enable,
    output logic [15:0] read_data
);

    logic [15:0] extended_message_data;
    logic        register_implemented;

    // Determine if the register should be implemented
    always_comb begin
        if (!per_vector_masking) begin
            register_implemented = extended_message_data_capable;
        end else begin
            register_implemented = extended_message_data_capable;
        end
    end

    // Register logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            extended_message_data <= 16'h0000;
        end else if (write_enable && register_implemented) begin
            extended_message_data <= write_data;
        end
    end

    // Read logic
    always_comb begin
        if (register_implemented) begin
            if (extended_message_data_enable) begin
                read_data = extended_message_data;
            end else begin
                read_data = 16'h0000;
            end
        end else if (per_vector_masking) begin
            read_data = 16'h0000; // RsvdP behavior
        end else begin
            read_data = 16'hxxxx; // Undefined behavior
        end
    end

endmodule