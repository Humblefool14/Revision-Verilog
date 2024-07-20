package dllp_defines;

  typedef enum logic [31:0] {
    DLLP_ACK                    = 32'h00000001,
    DLLP_MRINIT                 = 32'h00000002,
    DLLP_DATA_LINK_FEATURE      = 32'h00000003,
    DLLP_NAK                    = 32'h00000004,
    DLLP_PM_ENTER_L1            = 32'h00000005,
    DLLP_PM_ENTER_L23           = 32'h00000006,
    DLLP_PM_ACTIVE_STATE_REQ_L1 = 32'h00000007,
    DLLP_PM_REQUEST_ACK         = 32'h00000008,
    DLLP_VENDOR_SPECIFIC        = 32'h00000009,
    DLLP_NOP                    = 32'h0000000A,
    DLLP_INITFC1_P              = 32'h0000000B,
    DLLP_INITFC1_NP             = 32'h0000000C,
    DLLP_INITFC1_CPL            = 32'h0000000D,
    DLLP_MRINITFC1              = 32'h0000000E,
    DLLP_INITFC2_P              = 32'h0000000F,
    DLLP_INITFC2_NP             = 32'h00000010,
    DLLP_INITFC2_CPL            = 32'h00000011,
    DLLP_MRINITFC2              = 32'h00000012,
    DLLP_UPDATEFC_P             = 32'h00000013,
    DLLP_UPDATEFC_NP            = 32'h00000014,
    DLLP_UPDATEFC_CPL           = 32'h00000015,
    DLLP_MRUPDATEFC             = 32'h00000016,
    DLLP_RESERVED               = 32'h00000000
  } dllp_type_t;

endpackage