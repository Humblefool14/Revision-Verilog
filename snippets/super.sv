class Packet ; // base class
integer value;
function integer delay();
    delay = value * value;
  endfunction
endclass

class LinkedPacket extends Packet; 
integer value; // derived class

function integer delay();
      delay = super.delay()+ value * super.value; endfunction
endclass