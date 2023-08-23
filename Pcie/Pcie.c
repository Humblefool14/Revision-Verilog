#ifndef _PCIE_CPP__
#define _PCIE_CPP__
#include "Pcie.h"
int32_t pcie_chk_capability_id(void * dev, uint32_t *status){
   unsigned int addr=0, wdata=0,pcie_cap_addr;
   get_register_address(addr,  PCIE, EXPR_CAP);
   wdata = regRead(dev,addr);
   *status =1; 
   if((wdata >> 8)!=0x10){
    printf("[ERROR] CTEST PCIE CAPABILITY REGISTER DOESN'T WORK  \n"); 
    *status = 0; 
   }
  return API_OK; 
}
int32_t pcie_ret_cap_ptr(void * dev, uint32_t *pcie_cap_addr){
   unsigned int addr=0, wdata=0;
   get_register_address(addr,  PCIE, EXPR_CAP);
   wdata = regRead(dev,addr);
   wdata = (wdata >> 8)&(0xFF); // 8 bits shifted out. 
   *pcie_cap_addr = wdata; 
  return API_OK; 
}

int32_t pcie_chk_capability_version(void * dev, uint32_t *status){
   unsigned int addr=0, wdata=0,pcie_cap_addr;
   get_register_address(addr,  PCIE, EXPR_CAP);
   wdata = regRead(dev,addr);
   wdata = wdata >> 16; 
   wdata = (wdata >> 4)&(0xF); // 4 bits shifted out. 
   *status =1; 
   if((wdata)!=0x02){
    printf("[ERROR] CTEST PCIE CAPABILITY REGISTER DOESN'T WORK  \n"); 
    *status = 0; 
   }
  return API_OK; 
}

int32_t pcie_chck_port(void *dev){
   unsigned int addr=0, wdata=0,pcie_cap_addr;
   get_register_address(addr,  PCIE, EXPR_CAP);
   wdata = regRead(dev,addr);
   wdata = wdata >> 24; 
   wdata = (wdata)&(0x1); // 4 bits shifted out. 
   if((wdata)!=0x01){
    printf("[ERROR] CTEST PCIE SLOT UNDEFINED.UPSTREAM PORT  \n"); 
   }
   else printf("SLOT DEFINED. DOWNSTREAM PORT \n"); 
  return API_OK; 
}
