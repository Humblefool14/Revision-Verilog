module npem_capability_register #(
    parameter int REGISTER_WIDTH = 32
) (
    input logic clk,
    input logic rst_n,
    input logic [REGISTER_WIDTH-1:0] hw_capabilities, // [FIXME] Need to pass a parameter or a constant value
    input logic [REGISTER_WIDTH-1:0] write_data,
    input logic write_enable,
    output logic [REGISTER_WIDTH-1:0] read_data
);

    // Register bit fields
    logic npem_capable;
    logic npem_reset_capable;
    logic npem_ok_capable;
    logic npem_locate_capable;
    logic npem_fail_capable;
    logic npem_rebuild_capable;
    logic npem_pfa_capable;
    logic npem_hot_spare_capable;
    logic npem_in_a_critical_array_capable;
    logic npem_in_a_failed_array_capable;
    logic npem_invalid_device_type_capable;
    logic npem_disabled_capable;
    logic [7:0] enclosure_specific_capabilities;

    // HwInit logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            {npem_capable, npem_reset_capable, npem_ok_capable, npem_locate_capable,
             npem_fail_capable, npem_rebuild_capable, npem_pfa_capable, npem_hot_spare_capable,
             npem_in_a_critical_array_capable, npem_in_a_failed_array_capable,
             npem_invalid_device_type_capable, npem_disabled_capable,
             enclosure_specific_capabilities} <= hw_capabilities;
        end else if (write_enable) begin
            // Software can modify HwInit fields
            {npem_capable, npem_reset_capable, npem_ok_capable, npem_locate_capable,
             npem_fail_capable, npem_rebuild_capable, npem_pfa_capable, npem_hot_spare_capable,
             npem_in_a_critical_array_capable, npem_in_a_failed_array_capable,
             npem_invalid_device_type_capable, npem_disabled_capable,
             enclosure_specific_capabilities} <= write_data;
        end
    end

    // Ensure dependent capabilities are set correctly
    always_comb begin
        if (npem_capable) begin
            npem_ok_capable = 1'b1;
            npem_locate_capable = 1'b1;
            npem_fail_capable = 1'b1;
            npem_rebuild_capable = 1'b1;
        end
    end

    // Combine all fields into read_data
    assign read_data = {
        enclosure_specific_capabilities,
        npem_disabled_capable,
        npem_invalid_device_type_capable,
        npem_in_a_failed_array_capable,
        npem_in_a_critical_array_capable,
        npem_hot_spare_capable,
        npem_pfa_capable,
        npem_rebuild_capable,
        npem_fail_capable,
        npem_locate_capable,
        npem_ok_capable,
        npem_reset_capable,
        npem_capable
    };

endmodule