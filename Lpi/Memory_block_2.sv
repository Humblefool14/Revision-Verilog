class MemoryBlock; 
    bit [31:0] m_ram_start; 
    bit [31:0] m_ram_end; 

    rand bit [31:0] m_part_start[]; 
    rand int m_num_parts; 
    rand int m_size[]; 
    
    constraint c_parts { 
                         m_num_parts >4 && m_num_parts <10; 
    }
    constraint c_size{
        m_size.size() == m_num_parts;
        m_size.sum() == (m_ram_end-m_ram_start)/m_num_parts; 
        foreach(m_size[i])
            m_size[i] inside{16,32,64,128,512,1024};

    }

    constraint c_addr {
                        m.part_start.size() == m_num_part; 
                        foreach(m_part_start[i]){
                            if(i)
                            m_part_start[i] = m_part_start[i-1]+m_size[i-1];
                            else 
                            m_part_start[i] == m_ram_start; 
                        }
    }

function void display(); 
    $display("MeMORY BLOCK");
    $display("RAM ADDRESS STARTing = 0x%0h",m_ram_start);
    $display("RAM END ADDR = 0x%0h",m_ram_end);
    $display("BLock size =     %0d",m_num_parts); 
    foreach(m_part_start[i])
     $display(" Partition %0d start = 0x%0h,size = %0d bytes",i,m_part_start,m_size,m_);
endfunction 
endclass 