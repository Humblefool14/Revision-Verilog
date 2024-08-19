typedef enum usb_3_2_capability_type {
    USB_CAP_TYPE_WIRELESS_USB           = 0x01,
    USB_CAP_TYPE_USB_2_0_EXTENSION      = 0x02,
    USB_CAP_TYPE_SUPERSPEED_USB         = 0x03,
    USB_CAP_TYPE_CONTAINER_ID           = 0x04,
    USB_CAP_TYPE_PLATFORM               = 0x05,
    USB_CAP_TYPE_POWER_DELIVERY         = 0x06,
    USB_CAP_TYPE_BATTERY_INFO           = 0x07,
    USB_CAP_TYPE_PD_CONSUMER_PORT       = 0x08,
    USB_CAP_TYPE_PD_PROVIDER_PORT       = 0x09,
    USB_CAP_TYPE_SUPERSPEED_PLUS        = 0x0A,
    USB_CAP_TYPE_PRECISION_TIME_MEASUREMENT = 0x0B,
    USB_CAP_TYPE_WIRELESS_USB_EXT       = 0x0C,
    USB_CAP_TYPE_BILLBOARD              = 0x0D,
    USB_CAP_TYPE_AUTHENTICATION         = 0x0E,
    USB_CAP_TYPE_BILLBOARD_EX           = 0x0F,
    USB_CAP_TYPE_CONFIGURATION_SUMMARY  = 0x10
}ucap_t;


typedef enum request_codes{
    USB_REQ_GET_STA             = 0x0, 
    USB_REQ_CLEAR_FEATURE       = 0x1, 
    USB_REQ_RSVD                = 0x2, 
    USB_REQ_SET_FEATURE         = 0x3, 
    USB_REQ_STA_RSVD2           = 0x4,
    USB_REQ_SET_ADDRESS         = 0x5,
    USB_REQ_GET_DESCRIPTOR      = 0x6,
    USB_REQ_SET_DESCRIPTOR      = 0x7,
    USB_REQ_GET_CONFIGURATION   = 0x8, 
    USB_REQ_SET_CONFIGURATION   = 0x9,
    USB_REQ_GET_INTERFACE
    USB_REQ_SET_INTERFACE
    USB_REQ_SYNCH_FRAME
    USB_REQ_SET_ENCRYPTION
    USB_REQ_GET_ENCRYPTION
    USB_REQ_SET_HANDSHAKE
    USB_REQ_GET_HANDSHAKE 
    USB_REQ_SET_CONNECTION
    USB_REQ_SET_SECURITY_DATA
    USB_REQ_GET_SECURITY_DATA
    USB_REQ_SET_WUSB_DATA
    USB_REQ_LOOPBACK_DATA_WRITE
    USB_REQ_LOOPBACK_DATA_READ
    USB_REQ_SET_INTERFACE_DS
    USB_REQ_SET_SEL
    USB_REQ_SET_ISOCH_DELAY
}req_code_e; 

#define SS_ISO_EP  3*16*1024 
#define SSP_ISO_EP 6*16*1024 


// Endpoint Feature Selectors
#define ENDPOINT_HALT 0

// Interface Feature Selectors
#define FUNCTION_SUSPEND 0

// Device Feature Selectors
#define DEVICE_REMOTE_WAKEUP 1
#define TEST_MODE 2
#define b_hnp_enable 3
#define a_hnp_support 4
#define a_alt_hnp_support 5
#define WUSB_DEVICE 6
#define U1_ENABLE 48
#define U2_ENABLE 49
#define LTM_ENABLE 50
#define B3_NTF_HOST_REL 51
#define B3_RSP_ENABLE 52
#define LDM_ENABLE 53