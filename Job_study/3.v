module comb(output reg[15:0]  out,
            input [15:0] a,b,
            input [3:0] select);
    
    always@(*) begin 
        case(select)
        0: out = a+b;
        1: out = a-b;
        2: out = a*b;
        3: out = a;
        4: out = b;
        5: out = a&b;
        6: out = a|b;
        7: out = a^b;
        8: out = ~a;
        9: out = ~b;
        10: out = (a>>1);
        11: out = (a<<1);
        default: out = 16'hxxxx;
        endcase 
    end 
endmodule
