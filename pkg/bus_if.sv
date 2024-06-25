interface axi4_if #(
    parameter int ADDR_WIDTH = 32,  // Address width
    parameter int DATA_WIDTH = 32,  // Data width
    parameter int ID_WIDTH   = 4,   // ID width
    parameter int LEN_WIDTH  = 8    // Length width
) (
    input logic ACLK,   // Clock
    input logic ARESETn // Reset (active low)
);

    // Write address channel
    logic [ADDR_WIDTH-1:0] AWADDR;
    logic [LEN_WIDTH-1:0]  AWLEN;
    logic [2:0]            AWSIZE;
    logic [1:0]            AWBURST;
    logic                  AWLOCK;
    logic [3:0]            AWCACHE;
    logic [2:0]            AWPROT;
    logic [3:0]            AWQOS;
    logic [ID_WIDTH-1:0]   AWID;
    logic                  AWVALID;
    logic                  AWREADY;

    // Write data channel
    logic [DATA_WIDTH-1:0] WDATA;
    logic [(DATA_WIDTH/8)-1:0] WSTRB;
    logic                  WLAST;
    logic                  WVALID;
    logic                  WREADY;

    // Write response channel
    logic [1:0]            BRESP;
    logic [ID_WIDTH-1:0]   BID;
    logic                  BVALID;
    logic                  BREADY;

    // Read address channel
    logic [ADDR_WIDTH-1:0] ARADDR;
    logic [LEN_WIDTH-1:0]  ARLEN;
    logic [2:0]            ARSIZE;
    logic [1:0]            ARBURST;
    logic                  ARLOCK;
    logic [3:0]            ARCACHE;
    logic [2:0]            ARPROT;
    logic [3:0]            ARQOS;
    logic [ID_WIDTH-1:0]   ARID;
    logic                  ARVALID;
    logic                  ARREADY;

    // Read data channel
    logic [DATA_WIDTH-1:0] RDATA;
    logic [1:0]            RRESP;
    logic                  RLAST;
    logic [ID_WIDTH-1:0]   RID;
    logic                  RVALID;
    logic                  RREADY;

    // Master port (mp) modport
    modport mp (
        // Write address channel
        output AWADDR, 
        output AWLEN, 
        output AWSIZE, 
        output AWBURST, 
        output AWLOCK, 
        output AWCACHE, 
        output AWPROT, 
        output AWQOS, 
        output AWID, 
        output AWVALID,
        input  AWREADY,

        // Write data channel
        output WDATA, 
        output WSTRB, 
        output WLAST, 
        output WVALID,
        input  WREADY,

        // Write response channel
        input  BRESP, 
        input  BID, 
        input  BVALID,
        output BREADY,

        // Read address channel
        output ARADDR, 
        output ARLEN, 
        output ARSIZE, 
        output ARBURST, 
        output ARLOCK, 
        output ARCACHE, 
        output ARPROT, 
        output ARQOS, 
        output ARID, 
        output ARVALID,
        input  ARREADY,

        // Read data channel
        input  RDATA, RRESP, RLAST, RID, RVALID,
        output RREADY
    );

    // Slave port (sp) modport
    modport sp (
        // Write address channel
        input  AWADDR, AWLEN, AWSIZE, AWBURST, AWLOCK, AWCACHE, AWPROT, AWQOS, AWID, AWVALID,
        output AWREADY,

        // Write data channel
        input  WDATA, WSTRB, WLAST, WVALID,
        output WREADY,

        // Write response channel
        output BRESP, BID, BVALID,
        input  BREADY,

        // Read address channel
        input  ARADDR, ARLEN, ARSIZE, ARBURST, ARLOCK, ARCACHE, ARPROT, ARQOS, ARID, ARVALID,
        output ARREADY,

        // Read data channel
        output RDATA, RRESP, RLAST, RID, RVALID,
        input  RREADY
    );

endinterface

interface axi_r_if #(
    parameter int DATA_WIDTH = 32,
    parameter int ID_WIDTH   = 4
) (
    input logic ACLK,
    input logic ARESETn
);
    logic [DATA_WIDTH-1:0] RDATA;
    logic [1:0]            RRESP;
    logic                  RLAST;
    logic [ID_WIDTH-1:0]   RID;
    logic                  RVALID;
    logic                  RREADY;

    // Master port
    modport mp (
        input  RDATA, RRESP, RLAST, RID, RVALID,
        output RREADY
    );

    // Slave port
    modport sp (
        output RDATA, RRESP, RLAST, RID, RVALID,
        input  RREADY
    );

endinterface

interface axi_ar_if #(
    parameter int ADDR_WIDTH = 32,
    parameter int ID_WIDTH   = 4,
    parameter int LEN_WIDTH  = 8
) (
    input logic ACLK,
    input logic ARESETn
);
    logic [ADDR_WIDTH-1:0] ARADDR;
    logic [LEN_WIDTH-1:0]  ARLEN;
    logic [2:0]            ARSIZE;
    logic [1:0]            ARBURST;
    logic                  ARLOCK;
    logic [3:0]            ARCACHE;
    logic [2:0]            ARPROT;
    logic [3:0]            ARQOS;
    logic [ID_WIDTH-1:0]   ARID;
    logic                  ARVALID;
    logic                  ARREADY;

    // Master port
    modport mp (
        output ARADDR, ARLEN, ARSIZE, ARBURST, ARLOCK, ARCACHE, ARPROT, ARQOS, ARID, ARVALID,
        input  ARREADY
    );

    // Slave port
    modport sp (
        input  ARADDR, ARLEN, ARSIZE, ARBURST, ARLOCK, ARCACHE, ARPROT, ARQOS, ARID, ARVALID,
        output ARREADY
    );

endinterface

interface axi_w_if #(
    parameter int DATA_WIDTH = 32
) (
    input logic ACLK,
    input logic ARESETn
);
    logic [DATA_WIDTH-1:0] WDATA;
    logic [(DATA_WIDTH/8)-1:0] WSTRB;
    logic                  WLAST;
    logic                  WVALID;
    logic                  WREADY;

    // Master port
    modport mp (
        output WDATA, WSTRB, WLAST, WVALID,
        input  WREADY
    );

    // Slave port
    modport sp (
        input  WDATA, WSTRB, WLAST, WVALID,
        output WREADY
    );

endinterface


interface axi_aw_if #(
    parameter int ADDR_WIDTH = 32,
    parameter int ID_WIDTH   = 4,
    parameter int LEN_WIDTH  = 8
) (
    input logic ACLK,
    input logic ARESETn
);
    logic [ADDR_WIDTH-1:0] AWADDR;
    logic [LEN_WIDTH-1:0]  AWLEN;
    logic [2:0]            AWSIZE;
    logic [1:0]            AWBURST;
    logic                  AWLOCK;
    logic [3:0]            AWCACHE;
    logic [2:0]            AWPROT;
    logic [3:0]            AWQOS;
    logic [ID_WIDTH-1:0]   AWID;
    logic                  AWVALID;
    logic                  AWREADY;

    // Master port
    modport mp (
        output AWADDR, AWLEN, AWSIZE, AWBURST, AWLOCK, AWCACHE, AWPROT, AWQOS, AWID, AWVALID,
        input  AWREADY
    );

    // Slave port
    modport sp (
        input  AWADDR, AWLEN, AWSIZE, AWBURST, AWLOCK, AWCACHE, AWPROT, AWQOS, AWID, AWVALID,
        output AWREADY
    );

endinterface

interface apb_if #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    input logic PCLK,    // Clock
    input logic PRESETn  // Reset (active low)
);

    // Address phase
    logic [ADDR_WIDTH-1:0] PADDR;   // Address
    logic [DATA_WIDTH-1:0] PWDATA;  // Write data
    logic [DATA_WIDTH-1:0] PRDATA;  // Read data
    logic                  PWRITE;  // Write enable
    logic                  PSEL;    // Select
    logic                  PENABLE; // Enable
    logic                  PREADY;  // Ready
    logic                  PSLVERR; // Slave error

    // Master port (mp) modport
    modport mp (
        output PADDR, PWDATA, PWRITE, PSEL, PENABLE,
        input  PRDATA, PREADY, PSLVERR
    );

    // Slave port (sp) modport
    modport sp (
        input  PADDR, PWDATA, PWRITE, PSEL, PENABLE,
        output PRDATA, PREADY, PSLVERR
    );

endinterface

interface register_if #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    input logic CLK,     // Clock
    input logic RESETn   // Reset (active low)
);

    logic [ADDR_WIDTH-1:0] ADDR;   // Address
    logic [DATA_WIDTH-1:0] WDATA;  // Write data
    logic [DATA_WIDTH-1:0] RDATA;  // Read data
    logic                  VALID;  // Valid signal
    logic                  READ;   // Read enable
    logic                  WRITE;  // Write enable
    logic                  ACK;    // Acknowledge
    logic                  ERROR;  // Error signal

    // Master port (mp) modport
    modport mp (
        output ADDR, 
        output WDATA, 
        output VALID, 
        output READ, 
        output WRITE,
        input  RDATA, 
        input  ACK, 
        input  ERROR
    );

    // Slave port (sp) modport
    modport sp (
        input  ADDR, 
        input  WDATA, 
        input  VALID, 
        input  READ, 
        input  WRITE,
        output RDATA, ACK, ERROR
    );

endinterface