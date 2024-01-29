
always @(posedge pcie_clk or negedge pcie_rst_n or negedge pci_per_rstn) begin
  if (!pcie_rst_n or !pci_per_rstn) begin
    dll_state        <= 1'b0;
  end
  else begin
    int_dst_pcie     <= int_dst_pcie_wire;
    int_dst_usb      <= int_dst_usb_wire ;
    int_dst_pcie_reg <= int_dst[INTPCIX] ;
  end
end
