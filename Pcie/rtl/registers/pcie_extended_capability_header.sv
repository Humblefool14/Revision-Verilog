module pcie_extended_capability_header (
    input  logic [31:0] header_in,
    output logic [15:0] pci_express_extended_capability_id,
    output logic [3:0]  capability_version,
    output logic [11:0] next_capability_offset
);

    // PCI Express Extended Capability ID (bits 15:0)
    assign pci_express_extended_capability_id = header_in[15:0];

    // Capability Version (bits 19:16)
    assign capability_version = header_in[19:16];

    // Next Capability Offset (bits 31:20)
    assign next_capability_offset = header_in[31:20];

    // Assertions for validation
    always_comb begin
        // Check if PCI Express Extended Capability ID is correct (0019h)
        assert (pci_express_extended_capability_id == 16'h0019) else
            $error("Invalid PCI Express Extended Capability ID");

        // Check if Capability Version is correct (1h)
        assert (capability_version == 4'h1) else
            $error("Invalid Capability Version");
    end

endmodule