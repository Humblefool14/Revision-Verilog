// Code your testbench here or browse Examples
module top;
  
  bit clk ; bit siga_ = 1 ;
  
  always #5 clk = !clk;
  
  // By default ( data1 != data2 )
  int data1 =  0;
  int data2 = -1; 
  int pass, fail; 
  
  int unsigned d1 , d2 ; // Dynamic variables
  // Ben seuence from the package
  sequence dynamic_delay(count);
        int v;
      (count<=0) or ((1, v=count) ##0 (v>0, v=v-1) [*0:$] ##1 v<=0);
    endsequence // dynamic_delay
  sequence dynamic_delay_lohi_sq(d1, d2, sq);
        int v1, vdiff;
          ( (1, v1=d1, vdiff=d2-d1) ##0 dynamic_delay(v1)   ##0     
              (vdiff>0, vdiff=vdiff - 1)[*1:$] ##0 sq); 
    endsequence
  
/*  
  sequence dynamic_delay(count);
    int v;
    (count<=0) or ( ( count >0, v=count) ##0 (v>0, v=v-1) [*1:$] ##1 (v==0) );
  endsequence // dynamic_delay
  
  sequence dynamic_delay_lohi_sq(seq);
    int v1, vdiff;
    ( (1, v1=d1, vdiff=d2-d1) ##0 dynamic_delay(v1)  ##0 (vdiff>=0, vdiff=vdiff - 1)[*1:$] ##0 seq ); 
  endsequence
*/
  
/*  sequence dynamic_delay(count);
        int v;
      (count<=0) or ((1, v=count) ##0 (v>0, v=v-1) [*0:$] ##1 v<=0);
  endsequence // dynamic_delay
  
  sequence dynamic_delay_lohi_sq(sq);
        int v1, vdiff;
          ( (1, v1=d1, vdiff=d2-d1) ##0 dynamic_delay(v1)   ##0 (vdiff>=0, vdiff=vdiff - 1)[*1:$] ##0 sq); 
  endsequence */
  
  sequence seq_exp ;
    ( data1 == data2 );
  endsequence  
  
  property prop;
    $fell( siga_ ) |-> dynamic_delay_lohi_sq(d1, d2, seq_exp);
    //dynamic_delay_lohi_sq(seq_exp); // Fails at T:65 unlike intention
    //$fell( siga_ ) |-> ##[3:5] seq_exp; // Fails at T:55 as per expectation
  endproperty  
  
  assert property( @(posedge clk) prop ) begin 
    pass=pass+1; $display("T:%0t Pass",$time); end 
    else begin fail=fail+1; $display("T:%0t Fails",$time); end
    
  initial begin  
   $dumpfile("dump.vcd"); $dumpvars;
   d1 = 1 ; d2 = 2 ;    
   #4 ; siga_ = 0; 
    #82; $finish(); 
  end  
  
endmodule
