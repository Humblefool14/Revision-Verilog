#define MAX_PAYLOAD_SIZE 4096 
`define ASSERT_INTA     0x20 
`define ASSERT_INTB     0x21 
`define ASSERT_INTC     0x22 
`define ASSERT_INTD     0x23 
`define DEASSERT_INTA   0x24 
`define DEASSERT_INTB   0x25
`define DEASSERT_INTC   0x26 
`define DEASSERT_INTD   0x27 
//root code for above messages are same. that is 0x100. 


typedef enum PH [2-1:0] {
BIDIRECTIONAL                 = 2'b00,
REQUESTER                     = 2'b01,
TARGET                        = 2'b10,
TARGET_WITH_PRIORITY          = 2'b11
} hph_type;

// ERROR tlp's are message type. 
// Error tlp should tc0 
// Else it is a malformed tlp. 
// routing's code is 000 for all these tlp's. 
typedef enum erro_mgt[9-1:0]{
    ERROR_FATAL     = 8'b00110011;  // Malformed tlp. 
    ERROR_NONFATAL  = 8'b00110001; 
    ERROR_COR       = 8'b00110000; 
}erro_mgt_e; 

// type 4 i.e 5 th bit has to be 0 
typedef enum lcl_tlp_prefix [4-1:0]{
    MR_IOV          = 4'b0000; 
    FLIT_MODE_PFX   = 4'b1101; 
    VEND_PFX_L0     = 4'b1110; 
    VEND_PFX_L1     = 4'b1111; 
}lcl_tlp_prefix_e; 

`define MAX_READ_REQUEST_SIZE_000 128 
`define MAX_READ_REQUEST_SIZE_001 256 
`define MAX_READ_REQUEST_SIZE_010 512 
`define MAX_READ_REQUEST_SIZE_011 1024  
`define MAX_READ_REQUEST_SIZE_100 2048 
`define MAX_READ_REQUEST_SIZE_101 4096  

`define NO_OHC 5'b00000 
`define OHC_A  5'bxxxx1 
`define OHC_B  5'bxxx1x 
`define OHC_C  5'bxx1xx 

variables:
// shared_crdts_consumed  
// shared_crdts_consumed_currently 
// crdts_consumed
