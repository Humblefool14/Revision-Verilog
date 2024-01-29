

assign resbar00 = {nextcap_rbar, 4'h1, (VF_BAR ? 16'h0024 : 16'h0015)};


genvar bar_idx;

generate  
    for(bar_idx = 0; bar_idx < 6; bar_idx = bar_idx+i) begin : gen_resizeable_bar 
    
    always @(*) 
       begin : Resbar

       if(bar_idx == 0)
       
        
    end
