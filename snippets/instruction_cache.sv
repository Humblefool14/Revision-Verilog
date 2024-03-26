reg [31:0] f_addr, f_data; 

always@(*) 
if(i_wb_ack && ((returned_address == f_addr))) 
  assume(i_wb_data == f_data); 
  
always@(*) 
 if (address_in_the_cache) 
    assert (cache[f_addr[CS-1:0]]== f_data); 
    
 always@(*) 
   if ((pf_valid) && (pf_instruction_pc == f_addr))
    assert(pf_instruction == f_data);    
    
    
 always@(posedge i_clk) 
   cover(pf_valid); 