module msi_x_message_control_register (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        write_enable,
    input  logic [15:0] write_data,
    output logic [15:0] read_data,
    input  logic        is_system_software,
    input  logic        msi_enable,
    output logic        msi_x_enable,
    output logic        function_mask,
    output logic [10:0] table_size
);

    logic [10:0] table_size_reg;
    logic        function_mask_reg;
    logic        msi_x_enable_reg;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            table_size_reg   <= 11'b0;
            function_mask_reg <= 1'b0;
            msi_x_enable_reg <= 1'b0;
        end else if (write_enable && is_system_software) begin
            function_mask_reg <= write_data[14];
            msi_x_enable_reg  <= write_data[15];
        end
    end

    always_comb begin
        read_data = {msi_x_enable_reg, function_mask_reg, 3'b000, table_size_reg};
        msi_x_enable = msi_x_enable_reg;
        function_mask = function_mask_reg;
        table_size = table_size_reg;
    end

    // Assertions for validation
    assert property (@(posedge clk) disable iff (!rst_n)
        write_enable && !is_system_software |-> $stable({function_mask_reg, msi_x_enable_reg}))
        else $error("Device driver attempted to modify read-write bits");

    assert property (@(posedge clk) disable iff (!rst_n)
        msi_x_enable_reg && !msi_enable |-> $stable(msi_x_enable_reg))
        else $error("MSI-X enabled while MSI is disabled");

    initial begin
        $display("MSI-X Message Control Register initialized.");
        $display("Default: MSI-X is disabled, Function Mask is clear.");
        $display("Table Size is read-only and encoded as N-1.");
    end

    // Coverage for important states
    covergroup cg_msi_x_states @(posedge clk);
        cp_msi_x_enable: coverpoint msi_x_enable_reg;
        cp_function_mask: coverpoint function_mask_reg;
        cp_msi_enable: coverpoint msi_enable;
        cp_table_size: coverpoint table_size_reg {
            bins small = {[0:15]};
            bins medium = {[16:127]};
            bins large = {[128:$]};
        }
    endgroup

    cg_msi_x_states cg_inst = new();

endmodule