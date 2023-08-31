module local_mgmt_if
(
    input  logic                lmi_rden;
    input  logic                lmi_wren;
    input  logic [LMIADDR-1: 0] lmi_addr;
    input  logic [LMIDATA-1: 0] lmi_din;
    input                        pld_clk; 
    input                        pld_rst; 
    output logic [LMIODAT-1: 0] lmi_dout; 
    output logic                lmi_ack; 
);



endmodule ; 