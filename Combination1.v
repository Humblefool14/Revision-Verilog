module sequential(input a,b,c, output reg flag);
   always@(*)
       begin
          flag =c;
          if(a==1) flag = b&c;
       end
endmodule
