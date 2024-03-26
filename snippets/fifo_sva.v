// Fifo conditions

property not_simultaneous_read_write; 
    (!(Read && Write));
endproperty 

assert property(not_simultaneous_read_write); 