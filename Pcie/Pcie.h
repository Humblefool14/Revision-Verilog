#ifndef __Pcie_H__
#define __Pcie_H__

#include<stdio.h>
#include<stdlib.h>
#include<stdint.h>
#include<string.h>
#define API_OK 1
typedef enum pcie_device_port_typ{
    PCI_EXPRESS_ENDPT                  = 0, 
    LEGACY_PCI_EXPRESS_ENDPT           = 1,
    ROOT_PORT_PCI_EXPRESS_CMPLX        = 4,
    UPSTREAM_PORT_PCI_EXPRESS_SWITCH   = 5,
    DOWNSTREAM_PORT_PCI_EXPRESS_SWITCH = 6,
    PCI_EXPRESS_TO_PCI_BRIDGE          = 7,
    PCI_TO_PCI_EXPRESS_BRIDGE          = 8,
    RCIEP                              = 9,
    ROOT_CMPLX_EVNT_COLLECTOR         = 10, 
}pcie_dev_port_e; 
typedef enum pcie_aspm_support{
    NO_ASPM = 0, 
    ASPM_L0 = 1, 
    ASPM_L1 = 2,
    ASPM_L01 = 3
}aspm_e; 

typedef enum pcie_L0_exit_latency{
    LESS_THAN_64      = 0, 
    FROM_64_TO_128    = 1,
    FROM_128_TO_256   = 2,
    FROM_256_TO_512   = 3, 
    FROM_512_TO_1024  = 4, 
    FROM_1_TO_2       = 5, 
    FROM_2_TO_4       = 6,
    BEYOND_4          = 7
}L0_exit_lat_e; 
typedef enum pcie_L1_exit_latency{
    LESS_THAN_1     = 0, 
    FROM_1_TO_2   = 1,
    FROM_2_TO_4   = 2,
    FROM_4_TO_8   = 3, 
    FROM_8_TO_16  = 4, 
    FROM_16_TO_32       = 5, 
    FROM_32_TO_64       = 6,
    BEYOND_64          = 7
}L1_exit_lat_e; 

typedef enum pcie_negotiated_link_wid{
    LANE0 = 1,
    LANE1 = 2,
    LANE2 = 4,
    LANE8 = 8,
    LANE12 = 12,
    LANE16 = 16,
    LANE32 = 32
}lane_e; 
typedef enum pcie_mrl_state{
 MRL_CLOSED = 0, 
 MRL_OPEN   = 1
}mrl_state_e; 
typedef enum pcie_power_indicator_ctrl{
    PWR_RSVD  = 0,
    PWR_ON    = 1,
    PWR_BLINK = 2,
    PWR_OFF   = 3
}pwr_ind_e; 
typedef enum pcie_ctrler_ctrl{
    PWR_ON    = 0,
    PWR_OFF   = 1
}pwr_ctrl_e;
 
typedef enum pcie_attn_indicator_ctrl{
    ATTN_RSVD  = 0,
    ATTN_ON    = 1,
    ATTN_BLINK = 2,
    ATTN_OFF   = 3
}attn_ind_e; 

typedef enum pcie_at_encoding{
    UN_TRANS    = 0,
    TRANS_REQ   = 1,
    TRANS_LATED  = 2,
    UNTRANSLATED = 3
}pcie_at_e;

typedef enum cmpl_field_status{
    SUCCESS_COMPL   = 0,
    UNSUPPORTED_REQ = 1,
    CFG_REQ_RETRY   = 2,
    CMPL_ABORT      = 4
   // REST            = RSVD
}cmpl_e; 

typedef enum pcie_ordering{
    DEFAULT_ORDERING = 0,
    RELAX_ORDERING   =1, 
    ID_ORDERING      = 2,
    RELAXED_ID_ORDERING = 3
}tlp_pcie_order_e; 

typedef enum pcie_cache_mgmt{
    DEFAULT_CACHE =0,
    SWOOP_CACHE   = 1
}pcie_cache_mgmt_e; 

typedef enum pcie_traffic_class{
    TC0 = 0, 
    TC1 = 1 // FIXME. 
}tc_e; 

typedef enum pcie_vc_arb_cap{
    ROUND_ROBIN =0, 
    WRR_32      =1,
    WRR_64      =2,
    WRR_128     =3
    // Rest are reserved
}pcie_vc_arb_cap_e; 
//WRR --> weighted round robin 

typedef enum pcie_pm_state{
    D0 =0, 
    D1 =1,
    D2 =2, 
    D3 =3
}pm_st_e; 

#endif 