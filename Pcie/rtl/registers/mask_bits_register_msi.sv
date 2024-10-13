module mask_bits_register_msi #(
    parameter int MAX_VECTORS = 32
) (
    input  logic                 clk,
    input  logic                 rst_n,
    input  logic                 per_vector_masking_capable,
    input  logic                 addr_64bit_capable,
    input  logic [4:0]           multiple_message_capable,
    input  logic [2:0]           multiple_message_enable,
    input  logic [MAX_VECTORS-1:0] write_data,
    input  logic                 write_enable,
    output logic [MAX_VECTORS-1:0] read_data,
    output logic [MAX_VECTORS-1:0] mask_bits
);

    logic [MAX_VECTORS-1:0] mask_bits_reg;
    logic [4:0] implemented_vectors;
    logic [4:0] allocated_vectors;

    // Determine the number of implemented vectors
    always_comb begin
        implemented_vectors = multiple_message_capable;
    end

    // Determine the number of allocated vectors
    always_comb begin
        allocated_vectors = (1 << multiple_message_enable) - 1;
    end

    // Register logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mask_bits_reg <= '0;  // Default is 0
        end else if (write_enable && per_vector_masking_capable) begin
            for (int i = 0; i < MAX_VECTORS; i++) begin
                if (i < implemented_vectors) begin
                    mask_bits_reg[i] <= write_data[i];
                end
            end
        end
    end

    // Read logic
    always_comb begin
        if (per_vector_masking_capable) begin
            for (int i = 0; i < MAX_VECTORS; i++) begin
                if (i < implemented_vectors) begin
                    read_data[i] = mask_bits_reg[i];
                end else begin
                    read_data[i] = 1'b0;  // Reserved bits read as 0
                end
            end
        end else begin
            read_data = '0;  // Register not present, read as 0
        end
    end

    // Output mask bits
    always_comb begin
        for (int i = 0; i < MAX_VECTORS; i++) begin
            if (i < allocated_vectors) begin
                mask_bits[i] = mask_bits_reg[i];
            end else begin
                mask_bits[i] = 1'b0;  // Unallocated vectors are ignored
            end
        end
    end

endmodule