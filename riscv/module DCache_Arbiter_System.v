module DCache_Arbiter_System
#(
    parameter PORTS = 2
)
(
    input wire clk,
    input wire rst,
    
    // Read Port Signals
    input wire DCache_RdReq_Valid,
    input wire [55:0] DCache_RdReq_Paddr,
    input wire [`DATA_TYPE__LEN-1:0] DCache_RdReq_DataType,
    input wire DCache_RdReq_Abort,
    output wire DCache_RdResp_Done,
    output wire DCache_RdResp_Ready,
    output wire [63:0] DCache_RdResp_Data,
    
    // Write Port Signals
    input wire DCache_WrReq_Valid,
    input wire [`DATA_TYPE__LEN-1:0] DCache_WrReq_DataType,
    input wire [55:0] DCache_WrReq_Paddr,
    input wire [63:0] DCache_WrReq_Data,
    output wire DCache_WrResp_Done,
    output wire DCache_WrResp_Ready,
    
    // DCache Interface
    output wire DCache_Req_Valid,
    output wire DCache_Req_Type,
    output wire [`DATA_TYPE__LEN-1:0] DCache_Req_DataType,
    output wire [55:0] DCache_Req_Paddr,
    output wire [63:0] DCache_Req_Wrdata,
    output wire DCache_Req_Rdabort,
    input wire DCache_Resp_Done,
    input wire DCache_Resp_Ready,
    input wire [63:0] DCache_Resp_Rddata
);

    // Internal signals for connecting the arbiter and request handler
    wire internal_req_valid;
    wire internal_req_type;

    // Instantiate the Arbiter module
    DCache_Arbiter #(
        .PORTS(PORTS)
    ) arbiter (
        .clk(clk),
        .rst(rst),
        .DCache_RdReq_Valid(DCache_RdReq_Valid),
        .DCache_RdReq_Abort(DCache_RdReq_Abort),
        .DCache_WrReq_Valid(DCache_WrReq_Valid),
        .DCache_Req_Valid(internal_req_valid),
        .DCache_Req_Type(internal_req_type),
        .DCache_Resp_Done(DCache_Resp_Done),
        .DCache_Resp_Ready(DCache_Resp_Ready)
    );

    // Instantiate the Request Handler module
    DCache_Request_Handler #(
        .PORTS(PORTS)
    ) request_handler (
        .clk(clk),
        .rst(rst),
        .DCache_RdReq_Valid(DCache_RdReq_Valid),
        .DCache_RdReq_Paddr(DCache_RdReq_Paddr),
        .DCache_RdReq_DataType(DCache_RdReq_DataType),
        .DCache_RdReq_Abort(DCache_RdReq_Abort),
        .DCache_RdResp_Done(DCache_RdResp_Done),
        .DCache_RdResp_Ready(DCache_RdResp_Ready),
        .DCache_RdResp_Data(DCache_RdResp_Data),
        .DCache_WrReq_Valid(DCache_WrReq_Valid),
        .DCache_WrReq_DataType(DCache_WrReq_DataType),
        .DCache_WrReq_Paddr(DCache_WrReq_Paddr),
        .DCache_WrReq_Data(DCache_WrReq_Data),
        .DCache_WrResp_Done(DCache_WrResp_Done),
        .DCache_WrResp_Ready(DCache_WrResp_Ready),
        .DCache_Req_Valid(internal_req_valid),
        .DCache_Req_Type(internal_req_type),
        .DCache_Req_DataType(DCache_Req_DataType),
        .DCache_Req_Paddr(DCache_Req_Paddr),
        .DCache_Req_Wrdata(DCache_Req_Wrdata),
        .DCache_Req_Rdabort(DCache_Req_Rdabort),
        .DCache_Resp_Done(DCache_Resp_Done),
        .DCache_Resp_Ready(DCache_Resp_Ready),
        .DCache_Resp_Rddata(DCache_Resp_Rddata)
    );

    // Connect the internal signals to the top-level outputs
    assign DCache_Req_Valid = internal_req_valid;
    assign DCache_Req_Type = internal_req_type;

endmodule

// Arbiter Module
module DCache_Arbiter
#(
    parameter PORTS = 2
)
(
    input wire clk,
    input wire rst,
    
    // Read Port Signals
    input wire DCache_RdReq_Valid,
    input wire DCache_RdReq_Abort,
    
    // Write Port Signals
    input wire DCache_WrReq_Valid,
    
    // Arbiter Output Signals
    output wire DCache_Req_Valid,
    output reg DCache_Req_Type,
    input wire DCache_Resp_Done,
    input wire DCache_Resp_Ready
);

    reg [1:0] req_pending;
    reg Active_Req, Active_Req_d;
    reg arbiter_busy, arbiter_busy_d;
    reg last_valid, last_valid_d;

    always @(posedge clk) begin
        if (rst) begin
            req_pending <= 0;
        end else begin
            if (Active_Req == 1 && DCache_Resp_Done)
                req_pending[1] <= 1'b0;
            else if (DCache_WrReq_Valid)
                req_pending[1] <= 1'b1;
            
            if ((Active_Req == 0 && (DCache_Resp_Done || DCache_RdReq_Abort)) || DCache_RdReq_Abort)
                req_pending[0] <= 1'b0;
            else if (DCache_RdReq_Valid)
                req_pending[0] <= 1'b1;
        end
    end

    always @(*) begin
        last_valid_d = last_valid;
        if (arbiter_busy) begin
            if (DCache_Resp_Done || (Active_Req == 0 && DCache_RdReq_Abort)) begin
                arbiter_busy_d = 1'b0;
                Active_Req_d = Active_Req;
            end else begin
                arbiter_busy_d = arbiter_busy;
                Active_Req_d = Active_Req;
            end
        end else begin
            arbiter_busy_d = 1'b0;
            Active_Req_d = Active_Req;
            last_valid_d = last_valid;
            if (DCache_Resp_Ready) begin
                case (req_pending)
                    2'b00: begin
                        if (last_valid) begin
                            if (DCache_RdReq_Valid && !DCache_RdReq_Abort) begin
                                last_valid_d = 1'b0;
                                Active_Req_d = 1'b0;
                                arbiter_busy_d = 1'b1;
                            end else if (DCache_WrReq_Valid) begin
                                last_valid_d = 1'b1;
                                Active_Req_d = 1'b1;
                                arbiter_busy_d = 1'b1;
                            end
                        end else begin
                            if (DCache_WrReq_Valid) begin
                                last_valid_d = 1'b1;
                                Active_Req_d = 1'b1;
                                arbiter_busy_d = 1'b1;
                            end else if (DCache_RdReq_Valid && !DCache_RdReq_Abort) begin
                                last_valid_d = 1'b0;
                                Active_Req_d = 1'b0;
                                arbiter_busy_d = 1'b1;
                            end
                        end
                    end
                    2'b01: begin
                        if (!DCache_RdReq_Abort) begin
                            last_valid_d = 1'b0;
                            Active_Req_d = 1'b0;
                            arbiter_busy_d = 1'b1;
                        end
                    end
                    2'b10: begin
                        last_valid_d = 1'b1;
                        Active_Req_d = 1'b1;
                        arbiter_busy_d = 1'b1;
                    end
                    2'b11: begin
                        if (last_valid && !DCache_RdReq_Abort) begin
                            last_valid_d = 1'b0;
                            Active_Req_d = 1'b0;
                            arbiter_busy_d = 1'b1;
                        end else begin
                            last_valid_d = 1'b1;
                            Active_Req_d = 1'b1;
                            arbiter_busy_d = 1'b1;
                        end
                    end
                endcase
            end
        end
    end

    always @(posedge clk) begin
        if (rst) begin
            Active_Req <= 1'b0;
            last_valid <= 1'b0;
            arbiter_busy <= 1'b0;
        end else begin
            Active_Req <= Active_Req_d;
            last_valid <= last_valid_d;
            arbiter_busy <= arbiter_busy_d;
        end
    end

    assign DCache_Req_Valid = (!rst && arbiter_busy) ? 1'b1 : 1'b0;

    always @(*) begin
        DCache_Req_Type = Active_Req_d ? 1'b1 : 1'b0;
    end

endmodule

// Request Handler Module
module DCache_Request_Handler
#(
    parameter PORTS = 2
)
(
    input wire clk,
    input wire rst,
    
    // Read Port Signals
    input wire DCache_RdReq_Valid,
    input wire [55:0] DCache_RdReq_Paddr,
    input wire [`DATA_TYPE__LEN-1:0] DCache_RdReq_DataType,
    input wire DCache_RdReq_Abort,
    output wire DCache_RdResp_Done,
    output wire DCache_RdResp_Ready,
    output wire [63:0] DCache_RdResp_Data,
    
    // Write Port Signals
    input wire DCache_WrReq_Valid,
    input wire [`DATA_TYPE__LEN-1:0] DCache_WrReq_DataType,
    input wire [55:0] DCache_WrReq_Paddr,
    input wire [63:0] DCache_WrReq_Data,
    output wire DCache_WrResp_Done,
    output wire DCache_WrResp_Ready,
    
    // Arbiter Interface
    input wire DCache_Req_Valid,
    input wire DCache_Req_Type,
    
    // DCache Interface
    output wire [`DATA_TYPE__LEN-1:0] DCache_Req_DataType,
    output wire [55:0] DCache_Req_Paddr,
    output wire [63:0] DCache_Req_Wrdata,
    output wire DCache_Req_Rdabort,
    input wire DCache_Resp_Done,
    input wire DCache_Resp_Ready,
    input wire [63:0] DCache_Resp_Rddata
);

    wire is_write_req;
    assign is_write_req = DCache_Req_Type;

    // Routing signals based on request type
    assign DCache_Req_Paddr = is_write_req ? DCache_WrReq_Paddr : DCache_RdReq_Paddr;
    assign DCache_Req_DataType = is_write_req ? DCache_WrReq_DataType : DCache_RdReq_DataType;
    assign DCache_Req_Rdabort = (DCache_Req_Valid && !is_write_req) ? DCache_RdReq_Abort : 1'b0;
    assign DCache_Req_Wrdata = DCache_WrReq_Data;

    // Response handling
    assign DCache_RdResp_Ready = DCache_Resp_Ready;
    assign DCache_WrResp_Ready = DCache_Resp_Ready;
    assign DCache_RdResp_Data = DCache_Resp_Rddata;
    assign DCache_RdResp_Done = !is_write_req ? DCache_Resp_Done : 1'b0;
    assign DCache_WrResp_Done = is_write_req ? DCache_Resp_Done : 1'b0;

endmodule