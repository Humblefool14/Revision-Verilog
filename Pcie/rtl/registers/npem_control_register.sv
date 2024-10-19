module npem_control_register #(
    parameter int REGISTER_WIDTH = 32
) (
    input logic clk,
    input logic rst_n,
    input logic [REGISTER_WIDTH-1:0] write_data,
    input logic write_enable,
    input logic [REGISTER_WIDTH-1:0] capability_register,
    input logic enclosure_specific_write_enable,
    output logic [REGISTER_WIDTH-1:0] read_data,
    output logic npem_reset_initiated
);

    // Register bit fields
    logic npem_enable;
    logic npem_initiate_reset;
    logic [9:0] npem_controls;
    logic npem_disabled_control;
    logic [7:0] enclosure_specific_controls;

    // Temporary variable for read data
    logic [REGISTER_WIDTH-1:0] read_data_temp;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            npem_enable <= 1'b0;
            npem_initiate_reset <= 1'b0;
            npem_controls <= 10'b0;
            npem_disabled_control <= 1'b0;
            enclosure_specific_controls <= 8'h0;
            npem_reset_initiated <= 1'b0;
        end else if (write_enable) begin
            // NPEM Enable
            npem_enable <= write_data[0];

            // NPEM Initiate Reset
            if (capability_register[1] && write_data[1]) begin
                npem_initiate_reset <= 1'b1;
                npem_reset_initiated <= 1'b1;
            end else begin
                npem_initiate_reset <= 1'b0;
                npem_reset_initiated <= 1'b0;
            end

            // Other NPEM Controls
            for (int i = 0; i < 10; i++) begin
                if (capability_register[i+2]) begin
                    npem_controls[i] <= write_data[i+2];
                end
            end

            // NPEM Disabled Control
            if (capability_register[11]) begin
                npem_disabled_control <= write_data[11];
            end

            // Enclosure-specific Controls
            if (enclosure_specific_write_enable) begin
                enclosure_specific_controls <= write_data[31:24];
            end
        end else begin
            npem_initiate_reset <= 1'b0;
            npem_reset_initiated <= 1'b0;
        end
    end

    // Read logic
    always_comb begin
        read_data_temp = {enclosure_specific_controls, 12'b0, npem_disabled_control, npem_controls, 1'b0, npem_enable};

        // Apply read-only conditions based on capability register
        for (int i = 1; i < 12; i++) begin
            if (!capability_register[i]) begin
                read_data_temp[i] = 1'b0;
            end
        end

        // NPEM Initiate Reset always reads as 0
        read_data_temp[1] = 1'b0;
    end

    assign read_data = read_data_temp;

endmodule