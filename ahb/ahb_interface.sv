interface AHB_Interface #(parameter ADDR_WIDTH = 32,
                           parameter SIZE_WIDTH = 2,
                           parameter PROT_WIDTH = 2,
                           parameter HBURST_WIDTH = 2,
                           parameter HTRANS_WIDTH = 1, 
                           parameter STRB_WIDTH   = 4, 
                           parameter RESP_WIDTH   = 2, 
                           parameter DATA_WIDTH   = 32) ;

    // AHB Control Signals
    logic HCLK;                                     // AHB Clock
    logic HRESETn;                                  // Active low reset
    logic [HTRANS_WIDTH-1:0] HTRANS;                // Transfer type
    logic [HBURST_WIDTH-1:0] HBURST;                // Burst type
    logic HMASTLOCK;                                // Master lock
    logic [PROT_WIDTH-1:0] HPROT;                   // Protection type
    logic [ADDR_WIDTH-1:0] HADDR;                   // Address bus
    logic [SIZE_WIDTH-1:0] HSIZE;                   // Transfer size
    logic [DATA_WIDTH-1:0] HWDATA;                  // Write data bus
    logic [DATA_WIDTH-1:0] HRDATA;                  // Read data bus
    logic HWRITE;                                   // Write enable
    logic [STRB_WIDTH-1:0] HWSTB;                              // Write strobe
    logic HREADY;                                   // Transfer ready
    logic HREADYOUT;                                // Ready output
    logic [RESP_WIDTH-1:0] HRESP;                              // Response type

    modport mp (
        input HCLK,
        input HRESETn,
        output HTRANS,
        output HBURST,
        output HMASTLOCK,
        output HPROT,
        output HADDR,
        output HSIZE,
        output HWDATA,
        input HRDATA,
        output HWRITE,
        output HWSTB,
        input HREADY,
        output HREADYOUT,
        input HRESP
    );

    modport sp (
        input HCLK,
        input HRESETn,
        input HTRANS,
        input HBURST,
        input HMASTLOCK,
        input HPROT,
        input HADDR,
        input HSIZE,
        input HWDATA,
        output HRDATA,
        input HWRITE,
        input HWSTB,
        output HREADY,
        input HREADYOUT,
        output HRESP
    );

    task init_slave_signals();
        HTRANS <= TRANS_WD'b0;
        HBURST <= BURST_WD'b0;
        HMASTLOCK <= 1'b0;
        HPROT <= PROT_WD'b0;
        HADDR <= ADDR_WD'b0;
        HSIZE <= SIZE_WD'b0;
        HWDATA <= DATA_WIDTH'b0;
        HWRITE <= 1'b0;
        HWSTB <= WSTB_WD'b0;
        HREADY <= 1'b0;
        HREADYOUT <= 1'b0;
        HRESP <= RESP_WD'b0;
    endtask
    
    assert_check_hsize: assert property (@(posedge HCLK)  ($stable(HSIZE) && (8 * (1 << HSIZE) <= DATA_WIDTH)))
        else $error("Assertion failed: 8 * 2^HSIZE is greater than DATA_WIDTH");
    endproperty 

endinterface
