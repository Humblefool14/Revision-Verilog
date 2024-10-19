module npem_extended_capability_header #(
    parameter int REGISTER_WIDTH = 32
) (
    input logic [11:0] next_capability_offset,
    output logic [REGISTER_WIDTH-1:0] read_data
);

    // Constants
    localparam logic [15:0] PCI_EXPRESS_EXTENDED_CAPABILITY_ID = 16'h0029;
    localparam logic [3:0] CAPABILITY_VERSION = 4'h1;

    // Register bit fields
    logic [11:0] next_cap_offset;
    logic [3:0] cap_version;
    logic [15:0] pci_express_extended_capability_id;

    // Assign values
    assign next_cap_offset = next_capability_offset;
    assign cap_version = CAPABILITY_VERSION;
    assign pci_express_extended_capability_id = PCI_EXPRESS_EXTENDED_CAPABILITY_ID;

    // Combine fields into read_data
    assign read_data = {next_cap_offset, cap_version, pci_express_extended_capability_id};

endmodule