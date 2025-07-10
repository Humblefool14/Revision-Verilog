class asc_desc; 
intA[9:0] 
constraint asc_desc{
  foreach(intA[i]){
    if(i>=1 && i < 5){
      intA[i] > intA[i-1]
    }else{
      intA[i] < intA[i-1]
    }
  }; 
}
endclass; 
