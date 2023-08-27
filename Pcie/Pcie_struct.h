#ifndef __PCIE_STRUCT_H__
#define __PCIE_STRUCT_H__

#include<stdio.h>
#include<stdlib.h>
#include<stdint.h>
#include<string.h>
typedef union pcie_typ1_cfg_header{
  struct __attribute__((packed)){
    uint32_t vendor_id                   : 16; //1+4+2+4+1+1+4+1+1+2+4+2+2+4+2+2
    uint32_t dev_id                      : 16;
    uint32_t command                     : 16;
    uint32_t status                      : 16;
    uint32_t revision_id                 : 8;
    uint32_t class_code                  : 24;
    uint32_t cache_line_size             : 8;
    uint32_t primary_laten_timer         : 8;
    uint32_t header_type                 : 8;
    uint32_t bist_type                   : 8;
    uint32_t bar_register_1              : 32;
    uint32_t bar_register_2              : 32;
    uint32_t primary_bus_num             : 8;
    uint32_t secnd_bus_num               : 8;
    uint32_t sub_bus_num                 : 8;
    uint32_t sec_laten_timer             : 8;
    uint32_t io_base                     : 8; 
    uint32_t io_limit                    : 8; 
    uint32_t secondary_status            : 16;
    uint32_t mem_base                    : 16; 
    uint32_t mem_limit                   : 16; 
    uint32_t prefetch_mem_base           : 16; 
    uint32_t prefetch_mem_limit          : 16; 
    uint32_t prefetch_mem_upper          : 32; 
    uint32_t prefetch_mem_lower          : 32; 
    uint32_t u_o_base_upper              : 16; 
    uint32_t i_o_base_limit              : 16; 
    uint32_t cap_ptr                     : 8; 
    uint32_t rsvd                        : 24; 
    uint32_t expansion_rom_base          : 32; 
    uint32_t int_line                    : 8; 
    uint32_t int_pin                     : 8; 
    uint32_t bridge_ctrl                 : 16;
  };
  uint8_t data[60];
}pcie_typ1_cfg_header_u;

typedef union pcie_dw_mem64_request_header{
  struct __attribute__((packed)){
    uint32_t fmt                         : 3; 
    uint32_t type                        : 5;
    uint32_t t9                          : 1;
    uint32_t tc                          : 3;
    uint32_t t8                          : 1;
    uint32_t attr                        : 1;
    uint32_t ln                          : 1;
    uint32_t th                          : 1;
    uint32_t td                          : 1;
    uint32_t ep                          : 1; 
    uint32_t attr                        : 2; 
    uint32_t at     : 2; 
    uint32_t length : 10; 
    uint32_t request_id : 16; 
    uint32_t tag : 8; 
    uint32_t last_dw_be: 4; 
    uint32_t first_dw_be: 4; 
    uint32_t addr_hi: 32; 
    uint32_t addr_lo : 30; 
    uint32_t ph: 2; 
  }
    uint8_t data[12];
}pcie_dw_req_u; 

typedef union pcie_dw_mem32_request_header{
  struct __attribute__((packed)){
    uint32_t fmt                         : 3; 
    uint32_t type                        : 5;
    uint32_t t9                          : 1;
    uint32_t tc                          : 3;
    uint32_t t8                          : 1;
    uint32_t attr                        : 1;
    uint32_t ln                          : 1;
    uint32_t th                          : 1;
    uint32_t td                          : 1;
    uint32_t ep                          : 1; 
    uint32_t attr                        : 2; 
    uint32_t at     : 2; 
    uint32_t length : 10; 
    uint32_t request_id : 16; 
    uint32_t tag : 8; 
    uint32_t last_dw_be: 4; 
    uint32_t first_dw_be: 4; 
    uint32_t addr_lo : 30; 
    uint32_t ph: 2; 
  }
    uint8_t data[8];
}pcie_dw_req_u; 

typedef union pcie_translation_64_request_header{
  struct __attribute__((packed)){
    uint32_t fmt                         : 3; //000
    uint32_t type                        : 5; // 00000
    uint32_t t9                          : 1;
    uint32_t tc                          : 3;
    uint32_t t8                          : 1;
    uint32_t attr                        : 1;
    uint32_t ln                          : 1; // LN read or write or compl 
    uint32_t th                          : 1;
    uint32_t td                          : 1;
    uint32_t ep                          : 1; 
    uint32_t attr                        : 2; 
    uint32_t at                          : 2; 
    uint32_t length                      : 10; 
    uint32_t request_id                  : 16; 
    uint32_t tag                         : 8; 
    uint32_t last_dw_be                  : 4;     /// 1111
    uint32_t first_dw_be                 : 4;     //// 1111
    uint32_t addr_hi                     : 32;
    uint32_t addr_lo                     : 20;
    uint32_t rsvd                        : 11; 
    uint32_t nw                          : 1;  
  }
    uint8_t data[8];
}pcie_trans64_req_u; 

typedef union pcie_translation_32_request_header{
  struct __attribute__((packed)){
    uint32_t fmt                         : 3; //001
    uint32_t type                        : 5; //00000
    uint32_t t9                          : 1;
    uint32_t tc                          : 3;
    uint32_t t8                          : 1;
    uint32_t attr                        : 1;
    uint32_t ln                          : 1;
    uint32_t th                          : 1;
    uint32_t td                          : 1;
    uint32_t ep                          : 1; 
    uint32_t attr                        : 2; 
    uint32_t at                          : 2; 
    uint32_t length                      : 10; 
    uint32_t request_id                  : 16; 
    uint32_t tag                         : 8; 
    uint32_t last_dw_be                  : 4;     /// 1111
    uint32_t first_dw_be                 : 4;     //// 1111
    uint32_t addr_lo                     : 20;
    uint32_t rsvd                        : 11; 
    uint32_t nw                          : 1;    // no write flag. if set ---> Read only access for translation
  }
    uint8_t data[8];
}pcie_trans32_req_u; 

typedef union pcie_mem_32_request_header{
  struct __attribute__((packed)){
    uint32_t fmt                         : 3; //0x0
    uint32_t type                        : 5; //00000
    uint32_t t9                          : 1;
    uint32_t tc                          : 3;
    uint32_t t8                          : 1;
    uint32_t attr                        : 1;
    uint32_t ln                          : 1;
    uint32_t th                          : 1;
    uint32_t td                          : 1;
    uint32_t ep                          : 1; 
    uint32_t attr                        : 2; 
    uint32_t at                          : 2; 
    uint32_t length                      : 10; 
    uint32_t request_id                  : 16; 
    uint32_t tag                         : 8; 
    uint32_t last_dw_be                  : 4;   
    uint32_t first_dw_be                 : 4;     
    uint32_t addr_lo                     : 30;
    uint32_t rsvd                        : 2;    
  }
    uint8_t data[8];
}pcie_mem32_req_u; 

typedef union pcie_mem_64_request_header{
  struct __attribute__((packed)){
    uint32_t fmt                         : 3; //0x1
    uint32_t type                        : 5; //00000
    uint32_t t9                          : 1;
    uint32_t tc                          : 3;
    uint32_t t8                          : 1;
    uint32_t attr                        : 1;
    uint32_t ln                          : 1;
    uint32_t th                          : 1;
    uint32_t td                          : 1;
    uint32_t ep                          : 1; 
    uint32_t attr                        : 2; 
    uint32_t at                          : 2; 
    uint32_t length                      : 10; 
    uint32_t request_id                  : 16; 
    uint32_t tag                         : 8; 
    uint32_t last_dw_be                  : 4;     
    uint32_t first_dw_be                 : 4;     
    uint32_t addr_hi                     : 32; 
    uint32_t addr_lo                     : 30;
    uint32_t rsvd                        : 2;    
  }
    uint8_t data[8];
}pcie_mem32_req_u; 

typedef union pcie_compl_request_header{
  struct __attribute__((packed)){
    uint32_t fmt                         : 3; //0x0
    uint32_t type                        : 5; 
    uint32_t t9                          : 1;
    uint32_t tc                          : 3;
    uint32_t t8                          : 1;
    uint32_t attr                        : 1;
    uint32_t ln                          : 1;
    uint32_t th                          : 1;
    uint32_t td                          : 1;
    uint32_t ep                          : 1; 
    uint32_t attr                        : 2; // 00 
    uint32_t at                          : 2; 
    uint32_t length                      : 10; 
    uint32_t compl_id                    : 16; 
    uint32_t compl_status                : 3; 
    uint32_t bcm                         : 1; 
    uint32_t byte_cnt                    : 12; 
    uint32_t request_id                  : 16; 
    uint32_t tag                         : 8;     
    uint32_t rsvd                        : 1;     
    uint32_t addr_lo                     : 7;
  }
    uint8_t data[8];
}pcie_compl_req_u; 

typedef union pcie_msg_request_header{
  struct __attribute__((packed)){
    uint32_t fmt                         : 3; //0x1
    uint32_t type                        : 5; //10 r2,r1,r0 ---> 001 routed by address ---> rsvd1,2 will have the address for others it will be reserved 
    uint32_t t9                          : 1;
    uint32_t tc                          : 3;
    uint32_t t8                          : 1;
    uint32_t attr                        : 1;
    uint32_t ln                          : 1;
    uint32_t th                          : 1;
    uint32_t td                          : 1;
    uint32_t ep                          : 1; 
    uint32_t attr                        : 2; // 00 
    uint32_t at                          : 2; 
    uint32_t length                      : 10; 
    uint32_t request_id                  : 16; 
    uint32_t tag                         : 8;   
    uint32_t message_code                : 8;       
    uint32_t rsvd                        : 32;     
    uint32_t rsvd2                       : 32;
  }
    uint8_t data[8];
}pcie_msg_req_u; 

typedef union pcie_memread_request_header{
  struct __attribute__((packed)){
    uint32_t fmt                         : 3; //0x1
    uint32_t type                        : 5; 
    uint32_t t9                          : 1;
    uint32_t tc                          : 3;
    uint32_t t8                          : 1;
    uint32_t attr                        : 1;
    uint32_t ln                          : 1;
    uint32_t th                          : 1;
    uint32_t td                          : 1;
    uint32_t ep                          : 1; 
    uint32_t attr                        : 2; // 00 
    uint32_t at                          : 2; 
    uint32_t length                      : 10; 
    uint32_t request_id                  : 16; 
    uint32_t tag                         : 8;   
    uint32_t st                          : 8;       
  }
    uint8_t data[8];
}pcie_memread_req_u; 

typedef union pcie_memwrite_request_header{
  struct __attribute__((packed)){
    uint32_t fmt                         : 3; //0x1
    uint32_t type                        : 5; 
    uint32_t t9                          : 1;
    uint32_t tc                          : 3;
    uint32_t t8                          : 1;
    uint32_t attr                        : 1;
    uint32_t ln                          : 1;
    uint32_t th                          : 1;
    uint32_t td                          : 1;
    uint32_t ep                          : 1; 
    uint32_t attr                        : 2; // 00 
    uint32_t at                          : 2; 
    uint32_t length                      : 10; 
    uint32_t request_id                  : 16; 
    uint32_t st                          : 8; 
    uint32_t last_dw_be                  : 4;     
    uint32_t first_dw_be                 : 4;        
  }
    uint8_t data[8];
}pcie_memwrite_req_u; 
