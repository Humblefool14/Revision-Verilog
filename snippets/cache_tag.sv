asm_cache_tag: assume property {
  cache_valid && cache_ready
  |-> 
  cache_hit == cache_addr[13]; 
}; 

ast_req_mem_to_latency : assert property {
  req_valid && !req_addr[13] 
  |-> 
  ##[4:6] mem_valid
};  

