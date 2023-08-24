// 

// 

if(tlp.type){
    if(tlp.format){
        if(tlp.request){
            request_handler(); 
        }
        else {
            completion_tlp(tlp); 
        }
    }else{
        discard_tlp(tlp); 
    }
}else{
  discard_tlp(tlp); 
}