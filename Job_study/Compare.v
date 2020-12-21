module compare(output logic lt,et,gt, 
               input logic [31:0] a,b);
       
       always@(a,b)
            if( a < b )
                lt = 1'b1;
            else if(a==b)
                 lt = 1'b0;
          
          assign gt = (a>b);
        
 comparator(et,a,b);
 endmodule 
 
 module comparator (input logic[31:0] a,b,
                    output logic et);
         
   always@(a,b)
     et = (a==b);
 endmodule
 
            
            
