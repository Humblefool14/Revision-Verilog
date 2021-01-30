class BusTran; 
    bit [31:0] addr,crc,data[8];
    extern function void display();
endclass 

function void BusTran :: display(); 
    $display("%0d: Bustrain addr = %h,crc = %h",addr,crc);
    $write("\tdata[0-7]=");
    foreach(data[i]) 
            $write(data[i]);
    $display();
endfunction 

