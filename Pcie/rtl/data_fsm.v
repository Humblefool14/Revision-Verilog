module dl_layer_fsm (
    input  logic        clk,
    input  logic        rst_n,          // Active low general reset
    input  logic        hot_reset,      // PCI Express Hot Reset
    input  logic        cold_reset,     // PCI Express Cold Reset
    input  logic        flr,            // Function Level Reset (does not affect DL states)
    input  logic        restart,        // Restart signal
    input  logic        feature_done,
    input  logic        init_done,
    input  logic        deactivate,
    output logic [2:0]  dl_state
);

    // State encoding
    typedef enum logic [2:0] {
        DL_INACTIVE = 3'b000,
        DL_FEATURE  = 3'b001,
        DL_INIT     = 3'b010,
        DL_ACTIVE   = 3'b011
    } dl_state_t;

    dl_state_t current_state, next_state;

    // Combined reset signal
    logic combined_reset;
    assign combined_reset = !rst_n || hot_reset || cold_reset;

    // State register with reset and restart logic
    always_ff @(posedge clk or posedge combined_reset) begin
        if (combined_reset)
            current_state <= DL_INACTIVE; // Initial state after any type of reset
        else if (restart)
            current_state <= DL_INACTIVE; // Restart to initial state
        else if (!flr)  // FLR does not affect DL states
            current_state <= next_state;
    end

    // Next state logic
    always_comb begin
        next_state = current_state; // Default is to stay in current state
        
        case (current_state)
            DL_INACTIVE: next_state = DL_FEATURE;
            
            DL_FEATURE: begin
                if (feature_done)
                    next_state = DL_INIT;
                else if (deactivate)
                    next_state = DL_INACTIVE;
            end
            
            DL_INIT: begin
                if (init_done)
                    next_state = DL_ACTIVE;
                else if (deactivate)
                    next_state = DL_INACTIVE;
            end
            
            DL_ACTIVE: begin
                if (deactivate)
                    next_state = DL_INACTIVE;
            end
            
            default: next_state = DL_INACTIVE;
        endcase
    end

    // Output logic
    assign dl_state = current_state;

    // Assertions
    property p_valid_state_transitions;
        @(posedge clk) disable iff (combined_reset || restart)
        (current_state != next_state) |-> 
            ((current_state == DL_INACTIVE && next_state == DL_FEATURE) ||
             (current_state == DL_FEATURE && (next_state == DL_INIT || next_state == DL_INACTIVE)) ||
             (current_state == DL_INIT && (next_state == DL_ACTIVE || next_state == DL_INACTIVE)) ||
             (current_state == DL_ACTIVE && next_state == DL_INACTIVE));
    endproperty
    assert property(p_valid_state_transitions) else $error("Invalid state transition detected");

    // Assert that FLR does not affect DL states
    property p_flr_no_effect;
        @(posedge clk) disable iff (combined_reset || restart)
        flr |-> ##1 (current_state == $past(current_state));
    endproperty
    assert property(p_flr_no_effect) else $error("FLR incorrectly affected DL state");

    // Assert that reset and restart set the state to DL_INACTIVE
    property p_reset_restart_to_inactive;
        @(posedge clk) ((combined_reset || restart) && !combined_reset) |-> ##1 (current_state == DL_INACTIVE);
    endproperty
    assert property(p_reset_restart_to_inactive) else $error("Reset or restart did not set state to DL_INACTIVE");

    // Assert that hot reset sets the state to DL_INACTIVE
    property p_hot_reset_to_inactive;
        @(posedge clk) $rose(hot_reset) |-> ##1 (current_state == DL_INACTIVE);
    endproperty
    assert property(p_hot_reset_to_inactive) else $error("Hot reset did not set state to DL_INACTIVE");

    // Assert that cold reset sets the state to DL_INACTIVE
    property p_cold_reset_to_inactive;
        @(posedge clk) $rose(cold_reset) |-> ##1 (current_state == DL_INACTIVE);
    endproperty
    assert property(p_cold_reset_to_inactive) else $error("Cold reset did not set state to DL_INACTIVE");

endmodule