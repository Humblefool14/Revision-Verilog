class MemoryBlock; 
    bit [31:0] m_ram_start; 
    bit [31:0] m_ram_end; 

    rand bit [31:0] m_start_addr; 
    rand bit [31:0] m_end_addr; 
    rand int m_block_size; 

    constraint c_addr{
                        m_start_addr >= m_ram_start; 
                        m_end_addr <= m_ram_end; 
                        m_end_addr = m_start_addr+block_size-1; 
                        m_start_addr %4 ==0;
    }

    constraint c_blk_size{
                            m_block_size inside{64,128,256,512};
    };

    function void display(); 
        $display("MeMORY BLOCK");
        $display("RAM ADDRESS STARTing = 0x%0h",m_ram_start);
        $display("RAM END ADDR = 0x%0h",m_ram_end);
        $display("Block StartAddr = 0x%0h",m_start_addr);
        $display("Block END Addr = 0x%0h",m_end_addr);
        $display("BLock size =     %0d",m_block_size); 
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