class MemoryBlock;

  bit [31:0] 		m_ram_start; 			// Start address of RAM
  bit [31:0] 		m_ram_end; 				// End address of RAM

  rand int			m_num_part; 			// Number of partitions
  rand bit [31:0] 	m_part_start []; 		// Partition start array
  rand int 			m_part_size; 		 	// Size of each partition
  rand int			m_tmp;

  // Constrain number of partitions RAM has to be divided into
  constraint c_parts { m_num_part > 4; m_num_part < 10; }

  // Constraint size of each partition
  constraint c_size { m_part_size == (m_ram_end - m_ram_start)/m_num_part; }

  // Constrain start addr of each partition
  constraint c_part { m_part_start.size() == m_num_part;
                      foreach (m_part_start[i]) {
                        if (i)
                          m_part_start[i] == m_part_start[i-1] + m_part_size;
                        else
                          m_part_start[i] == m_ram_start;
                      }
                    }

  function void display();
    $display ("------ Memory Block --------");
    $display ("RAM StartAddr   = 0x%0h", m_ram_start);
    $display ("RAM EndAddr     = 0x%0h", m_ram_end);
    $display ("# Partitions = %0d", m_num_part);
    $display ("Partition Size = %0d bytes", m_part_size);
    $display ("------ Partitions --------");
    foreach (m_part_start[i])
      $display ("Partition %0d start = 0x%0h", i, m_part_start[i]);
  endfunction
endclass

module tb;
  initial begin
    MemoryBlock mb = new;
    mb.m_ram_start = 32'h0;
    mb.m_ram_end   = 32'h7FF; 		// 2KB RAM
    mb.randomize();
    mb.display();
  end
endmodule
