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
#define API_OK 1
int32_t pcie_chk_capability(void * dev); 
