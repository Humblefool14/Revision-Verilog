class MemoryBlock; 
    bit [31:0] m_ram_start; 
    bit [31:0] m_ram_end; 

    rand bit [31:0] m_part_start[]; 
    rand int m_num_parts; 
    rand int m_size; 
    
    constraint c_parts { 
                         m_num_parts >4 && m_num_parts <10; 
    }

    constraint c_address{
                         m_part_start.size() == m_num_part; 
                         foreach(m_part_start[i]){
                            if(i)
                            m_part_start[i] == m_part_start[i-1]+m_size;
                            else 
                            m_part_start[i] == m_ram_start; 
                        }
    };

    constraint c_size{
        m_size == (m_ram_end-m_ram_start)/m_num_parts; 
    };

function void display(); 
    $display("MeMORY BLOCK");
    $display("RAM ADDRESS STARTing = 0x%0h",m_ram_start);
    $display("RAM END ADDR = 0x%0h",m_ram_end);
    $display("Block StartAddr = 0x%0h",m_part_start);
    $display("Block END Addr = 0x%0h",m_num_parts);
    $display("BLock size =     %0d",m_size); 
endfunction 
endclass 

module tb; 
initial begin 
    MemoryBlock mb = new(); 
    mb.m_ram_start = 64'h0; 
    mb.m_ram_end    = 64'h7FF; 
    mb.randomize(); 
    mb.display(); 
end 
endmodule 
