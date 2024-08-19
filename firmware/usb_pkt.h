typedef enum TP_Subtype {
    TP_SUBTYPE_RESERVED_0 = 0,
    TP_SUBTYPE_ACK = 1,
    TP_SUBTYPE_NRDY = 2,
    TP_SUBTYPE_ERDY = 3,
    TP_SUBTYPE_STATUS = 4,
    TP_SUBTYPE_STALL = 5,
    TP_SUBTYPE_DEV_NOTIFICATION = 6,
    TP_SUBTYPE_PING = 7,
    TP_SUBTYPE_PING_RESPONSE = 8,
    // 9-15 are reserved
    TP_SUBTYPE_RESERVED_MAX = 15
}Tp_subtype_e;


typedef enum TransferType {
    TT_UNKNOWN = 0,         // 000b - Unknown for ACKs and deferred DPs from SuperSpeed
    TT_RESERVED_1 = 1,      // 001b - Reserved
    TT_RESERVED_2 = 2,      // 010b - Reserved
    TT_RESERVED_3 = 3,      // 011b - Reserved
    TT_CONTROL = 4,         // 100b - Control Transfer Type
    TT_ISOCHRONOUS = 5,     // 101b - Isochronous Transfer Type
    TT_BULK = 6,            // 110b - Bulk Transfer Type
    TT_INTERRUPT = 7        // 111b - Interrupt Transfer Type
}ttype_e;
