#include "Pcie.h"
#include "Pcie_defines.h"
int32_t pcie_set_all_vc(void * dev){
   unsigned int addr=0, wdata=0;
   get_register_address(addr,  PCIE, VC_CTRL);
   wdata = regRead(dev,addr);
   wdata = wdata | (1 << ALL_VC_ENABLE); 
   regWrite(dev,addr,wdata); 
   return API_OK; 
}

int32_t pcie_get_arbitration_cap(void *dev){
    uint32_t addr,wdata; 
    get_register_address(addr,  PCIE, VC_CAP);
    wdata = regRead(dev,addr_reg); 
    return (wdata & (0xFF)); 
}
int32_t pcie_set_arbitration_sel(void *dev){
    uint32_t addr =0,wdata =0,addr_reg; 
    get_register_address(addr,  PCIE, VC_CTRL);
    wdata = pcie_get_arbitration_cap(dev); 
    //FIXME 
    return value; 
}

int32_t pcie_get_vc_arbitration(void *dev){
    uint32_t addr,wdata; 
    get_register_address(addr,  PCIE, VC_CAP);
    wdata = regRead(dev,addr_reg); 
    return (wdata & (0xFF000000)); 
}

int32_t pcie_vc_chk(void *dev){
    uint32_t rdata = pcie_get_vc_arbitration(dev); 
    uint32_t addr = get_register_address(addr, PCIE, DQWORDS_TBL); 
    if(rdata ==0){
        printf("No table present \n"); 
    }
    else {
        printf("Table location : 0x%x",addr+rdata);
    }
    return API_OK; 
}