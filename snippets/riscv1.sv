always @ (posedge clk) begin
   if (r_out & v_in) I_out <= calculate_i(IR); 
   if (r_out & v_in) PC_out <= PC;
   if (r_out & v_in) IR_out <= IR; 
end
