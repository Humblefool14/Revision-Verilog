module link_status_2_register_decoder (
    input  logic        clk,
    input  logic        rst_n,
    
    // Input for the entire register
    input  logic [15:0] link_status_2,
    
    // Output signals decoded from the register
    output logic [3:0]  current_de_emphasis_level,
    output logic        equalization_8gt_complete,
    output logic        equalization_8gt_phase1_successful,
    output logic        equalization_8gt_phase2_successful,
    output logic        equalization_8gt_phase3_successful,
    output logic        link_equalization_request_8gt,
    output logic        retimer_presence_detected,
    output logic        two_retimers_presence_detected,
    output logic        crosslink_resolution,
    output logic        flit_mode_status,
    output logic        rsvdz,
    output logic        downstream_component_presence,
    output logic        drs_message_received
);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_de_emphasis_level      <= 4'b0000;
            equalization_8gt_complete      <= 1'b0;
            equalization_8gt_phase1_successful <= 1'b0;
            equalization_8gt_phase2_successful <= 1'b0;
            equalization_8gt_phase3_successful <= 1'b0;
            link_equalization_request_8gt  <= 1'b0;
            retimer_presence_detected      <= 1'b0;
            two_retimers_presence_detected <= 1'b0;
            crosslink_resolution           <= 1'b0;
            flit_mode_status               <= 1'b0;
            rsvdz                          <= 1'b0;
            downstream_component_presence  <= 1'b0;
            drs_message_received           <= 1'b0;
        end else begin
            current_de_emphasis_level      <= link_status_2[15:12];
            equalization_8gt_complete      <= link_status_2[11];
            equalization_8gt_phase1_successful <= link_status_2[10];
            equalization_8gt_phase2_successful <= link_status_2[9];
            equalization_8gt_phase3_successful <= link_status_2[8];
            link_equalization_request_8gt  <= link_status_2[7];
            retimer_presence_detected      <= link_status_2[6];
            two_retimers_presence_detected <= link_status_2[5];
            crosslink_resolution           <= link_status_2[4];
            flit_mode_status               <= link_status_2[3];
            rsvdz                          <= link_status_2[2];
            downstream_component_presence  <= link_status_2[1];
            drs_message_received           <= link_status_2[0];
        end
    end

endmodule