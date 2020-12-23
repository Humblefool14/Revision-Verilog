module SR_latch(input S,R,output Q, Qbar);
        nand n1(Q,S,Qbar);
        nand n2(Qbar,R,Q);
endmodule

module Top;
    wire q,qbar;
    reg set,reset;
    
    SR_latch m1(~set,~reset,q,qbar);

initial 
begin 
        $monitor($time, "set = %b,reset = %b,q = %b \n",set,reset,q);
        set =0;
        reset =0;
        #5 reset =1;
        #5 reset =0;
        #5 set =1;
end 
endmodule 
