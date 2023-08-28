#ifndef _PCIE_RCRB_CPP__
#define _PCIE_RCRB_CPP__
#include "Pcie.h"
int32_t pcie_chk_rcrb_capability_id(void * dev){
   unsigned int addr=0, wdata=0,rcrb_cap_id;
   get_register_address(addr,  PCIE, RCRB_EXPR_CAP);
   wdata = regRead(dev,addr);
   rcrb_cap_id = wdata && (0xFFFF);
   return rcrb_cap_id; 
}

int32_t pcie_chk_rcrb_cap_ver(void * dev){
   unsigned int addr=0, wdata=0,rcrb_cap_ver_id;
   get_register_address(addr,  PCIE, RCRB_EXPR_CAP);
   wdata = regRead(dev,addr);
   rcrb_cap_ver_id = wdata && (0x000F0000);
   return rcrb_cap_ver_id; 
}

int32_t pcie_rcrb_nxt_cap_ptr(void * dev){
   unsigned int addr=0, wdata=0,rcrb_cap_ptr;
   get_register_address(addr,  PCIE, RCRB_EXPR_CAP);
   wdata = regRead(dev,addr);
   rcrb_cap_ptr = wdata && (0xFFF00000);
   return rcrb_cap_ptr; 
}

int32_t pcie_rcrb_vendor_id(void * dev){
   unsigned int addr=0, wdata=0,rcrb_vendor_id;
   get_register_address(addr,  PCIE, RCRB_ID);
   wdata = regRead(dev,addr);
   rcrb_vendor_id = wdata && (0xFFFF);
   return rcrb_vendor_id; 
}

int32_t pcie_rcrb_dev_id(void * dev){
   unsigned int addr=0, wdata=0,rcrb_dev_id;
   get_register_address(addr,  PCIE, RCRB_ID);
   wdata = regRead(dev,addr);
   rcrb_dev_id = wdata && (0xFFFF0000);
   return rcrb_dev_id; 
}

int32_t pcie_rcrb_ro_rrs(void * dev){
   unsigned int addr=0, wdata=0,rcrb_rrs;
   get_register_address(addr,  PCIE, RCRB_CAP);
   wdata = regRead(dev,addr);
   wdata = wdata & (0x1);
   return wdata; 
}/// request retry status completion. 

int32_t pcie_chk_rrs(void *dev){
    uint32_t rrs = pcie_rcrb_ro_rrs(dev);
    if(rrs==1){
        printf("[RCRB REGISTER] ROOT COMPLEX RETURNS RRS \n");
    }
    else{
        printf("[RCRB REGISTER] ROOT COMPLEX FAILS IN RETURNING RRS \n");
    }
   return API_OK; 
}

int32_t pcie_rcrb_set_rrs(void * dev){
   unsigned int addr=0, wdata=0,rcrb_rrs;
   get_register_address(addr,  PCIE, RCRB_CTRL);
   wdata = regRead(dev,addr);
   wdata = wdata | (0x1);
   regWrite(dev,addr,wdata);
   return API_OK; 
}/// request retry status completion will be given by root complex. 