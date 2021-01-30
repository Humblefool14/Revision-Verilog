`include "uvm_macros.svh"
`default_nettype wire 

module lpi_testbench(); 
    
    import uvm_pkg ::*;

    reg lpi_dut_clk;

    reg dut_rst_n; 

    lpi_if lpi_dut_if (.lpi_clk(lpi_dut_clk));

        initial 

        begin 
             uvm_config_db #(virtual lpi_if):: set(null,"","lpi_vif",lpi_dut_if);
        end 
    lpi dut_lpi(
                .clk(lpi_dut_clk),
                .rst_n(dut_rst_n),
                .slp_req0(lpi_dut_if.slp_req0),
                .slp_req1(lpi_dut_if.slp_req1),
                .wakeup_req0(lpi_dut_if.wakeup_req0),
                .wakeup_req1(lpi_dut_if.wakeup_req1),
                .ss_wakeup(lpi_dut_if.ss_wakeup),
                .ss_sleep(lpi_dut_if.ss_sleep)
    );

        initial 
        begin 
                lpi_dut_clk =0; 

                dut_rst_n = 1; 
        end 

        always 
        begin 
              #10ns lpi_dut_clk = ~lpi_dut_clk; 
        end 

        initial 
        begin 
               #0; 
               run_test(); 
        end 

endmodule 
