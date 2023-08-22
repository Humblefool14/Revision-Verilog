#ifndef _PCIE_CPP__
#define _PCIE_CPP__
#include "Pcie.h"
int32_t pcie_chk_capability(void * dev){
   unsigned int addr=0, wdata=0,pcie_cap_addr;
   get_register_address(addr,  PCIE, EXPR_CAP);
   wdata = regRead(dev,addr);
   if((wdata >> 8)!=0x10){
    printf("[ERROR] CTEST PCIE CAPABILITY REGISTER DOESN'T WORK  \n"); 
   }
   wdata = wdata >> 8; // 8 bits shifted out. 
   pcie_cap_addr = wdata; 
  return pcie_cap_addr; 
}
