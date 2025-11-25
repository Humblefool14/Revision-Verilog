// PM Message Type enumeration
typedef enum logic [7:0] {
    PM_ACTIVE_STATE_NAK = 8'b0001_0100,  // Code: 0x14, Routing: 100 (Terminate at Receiver)
    PM_PME              = 8'b0001_1000,  // Code: 0x18, Routing: 000 (Propagate Upstream)
    PM_TURN_OFF         = 8'b0001_1001,  // Code: 0x19, Routing: 011 (Broadcast Downstream)
    PM_PME_TO_ACK       = 8'b0001_1011   // Code: 0x1B, Routing: 101 (Sent by Upstream Port)
} pm_msg_code_e;

// PM Message Routing enumeration
typedef enum logic [2:0] {
    ROUTE_TO_RC         = 3'b000,  // Route to Root Complex
    ROUTE_BY_ADDR       = 3'b001,  // Route by Address
    ROUTE_BY_ID         = 3'b010,  // Route by ID
    ROUTE_BROADCAST     = 3'b011,  // Broadcast from Root Complex
    ROUTE_LOCAL         = 3'b100,  // Local - Terminate at Receiver
    ROUTE_GATHER        = 3'b101   // Gather and route to Root Complex
} msg_routing_e;
