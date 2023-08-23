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
