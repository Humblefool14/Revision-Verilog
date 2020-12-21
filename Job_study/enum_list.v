
module FSM(input logic clock,resetN,
            output logic [3:0] control);
    
    enum [2:0] logic { WAITE = 3'b001,
                       LOAD = 3'b010,
                       RELOAD = 3'b100} State,Next;
    always@(posedge clock and negedge resetN)
            if(!resetN) State <= WAITE;
            else State <= Next;
            
    always_comb begin 
        $display("\n Current State is %s (%b)",State.name(),State);
        case(State)
            WAITE  :   = Next;
            LOAD   :   = Next;
            RELOAD :   = Next;
        endcase 
        $display("\n Next State is %s (%b)",Next.name(),Next);
    end 
    assign control= State;
endmodule 
