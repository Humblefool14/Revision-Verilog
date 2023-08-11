#define TRANFER_SIZE 1000 

typedef enum msg_type{
 IQ_DATA = 0; 
 BIT_SEQ =1; 
 REAL_CTRL_DATA =2; 
 DATA_TRANSFR   = 3; 
 REMOTE_MEM_ACC  = 4; 
 DLY_MSMT = 5; 
 RMT_RST  = 6; 
 EVNT_IND  = 7; 
 RSVD      = 255; 
}eCPRI_msg_typ_u; 

typedef union ecpri_layer_attributes{
    uint32_t pc_id; 
    uint32_t rtc_id; 
    uint32_t seq_id; 
    uint32_t data[TRANFER_SIZE]; 
}ecpri_layer_u; 

typedef struct eCPRI_msg{
    struct __attribute__(packed) eCPRI_H{
        uint8_t ecpri_protocol_version : 4; 
        uint8_t rsvd_typ: 3;
        uint8_t  msg_chain: 1; 
        uint8_t  ecpri_msg_typ : 8; 
        uint16_t payload_size : 16; 
    }
    payload[TRANSFER_SIZE];
}
