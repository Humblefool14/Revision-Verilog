typedef enum logic [2:0] {
    MSG_ROUTE_TO_RC      = 3'b000,  // Routed to Root Complex
    MSG_ROUTE_BY_ADDR    = 3'b001,  // Routed by Address
    MSG_ROUTE_BY_ID      = 3'b010,  // Routed by ID
    MSG_BROADCAST_FROM_RC = 3'b011, // Broadcast from Root Complex
    MSG_LOCAL_TO_RECV    = 3'b100,  // Local - Terminate at Receiver
    MSG_GATHER_TO_RC     = 3'b101   // Gathered and routed to Root Complex
} msg_routing_e;
