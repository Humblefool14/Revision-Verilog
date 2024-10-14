module frs_queueing_control_register #(
    parameter int REGISTER_WIDTH = 16
) (
    input logic clk,
    input logic rst_n,
    input logic [REGISTER_WIDTH-1:0] write_data,
    input logic write_enable,
    output logic [REGISTER_WIDTH-1:0] read_data,
    output logic frs_interrupt_enable
);

    // Register bit fields
    logic frs_interrupt_enable_reg;
    logic [REGISTER_WIDTH-2:0] rsvdp;

    // RW logic for FRS Interrupt Enable
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            frs_interrupt_enable_reg <= 1'b0; // Default value is 0b
        end else if (write_enable) begin
            frs_interrupt_enable_reg <= write_data[0];
        end
    end

    // Reserved bits are always read as 0
    assign rsvdp = '0;

    // Combine all fields into read_data
    assign read_data = {rsvdp, frs_interrupt_enable_reg};

    // Output the FRS Interrupt Enable bit
    assign frs_interrupt_enable = frs_interrupt_enable_reg;

endmodule