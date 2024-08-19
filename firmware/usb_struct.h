#include "usb_defines.h"
struct usb_configuration_request {
    uint8_t bmRequestType;   // Characteristics of the request
    uint8_t bRequest;        // Specific request (usually SET_CONFIGURATION)
    uint16_t wValue;         // Value to be set (usually the configuration value)
    uint16_t wIndex;         // Index or offset (often 0 for configuration requests)
    uint16_t wLength;        // Number of bytes to transfer (typically 0 for configuration requests)
};


struct usb_device_capability_descriptor {
    uint8_t  bLength;
    uint8_t  bDescriptorType;
    uint8_t  bDevCapabilityType;
    uint8_t  bmAttributes[4];
};

struct usb_bos_descriptor {
    uint8_t  bLength;
    uint8_t  bDescriptorType;
    uint16_t wTotalLength;
    uint8_t  bNumDeviceCaps;
};

struct usb_bos_descriptor bos = {
    .bLength = sizeof(struct usb_bos_descriptor),
    .bDescriptorType = USB_DT_BOS,
    .wTotalLength = sizeof(struct usb_bos_descriptor) + sizeof(struct usb_device_capability_descriptor),
    .bNumDeviceCaps = 1
};

struct usb_device_capability_descriptor cap = {
    .bLength = sizeof(struct usb_device_capability_descriptor),
    .bDescriptorType = USB_DT_DEVICE_CAPABILITY,
    .bDevCapabilityType = /* specific type */,
    .bmAttributes = {/* capability-specific attributes */}
};

struct usb_device_descriptor {
    uint8_t  bLength;
    uint8_t  bDescriptorType;
    uint16_t bcdUSB;
    uint8_t  bDeviceClass;
    uint8_t  bDeviceSubClass;
    uint8_t  bDeviceProtocol;
    uint8_t  bMaxPacketSize0;
    uint16_t idVendor;
    uint16_t idProduct;
    uint16_t bcdDevice;
    uint8_t  iManufacturer;
    uint8_t  iProduct;
    uint8_t  iSerialNumber;
    uint8_t  bNumConfigurations;
};

struct usb_configuration_request set_address_request = {
    .bmRequestType = USB_DIR_OUT | USB_TYPE_STANDARD | USB_RECIP_DEVICE,
    .bRequest = USB_REQ_SET_ADDRESS,
    .wValue = address,  // The new address to set
    .wIndex = 0,
    .wLength = 0
};

struct usb_configuration_request get_interface_request = {
    .bmRequestType = 0x81,  // Device-to-host, standard, interface
    .bRequest = USB_REQ_GET_INTERFACE,
    .wValue = 0,
    .wIndex = interface_number,
    .wLength = 1  // We expect 1 byte in response
};

struct usb_get_status_request std_status_request ={
    .bmRequestType = 0x82; // Device to host, standard request, endpoint recipient
    .bRequest = 0x00;      // GET_STATUS request
    .wValue = 0x0000;      // Must be zero
    .wIndex = 0x01;        // Endpoint 1
    .wLength = 0x0002;     // Status length returns is 2 bytes
}
// Response: 
// Bit 0: Halted (1 if the endpoint is halted/stalled).
// Bits 1-15: Reserved (should be 0).

struct usb_get_status_request ptm_status_request ={
    .bmRequestType = 0x82; // Device to host, standard request, endpoint recipient
    .bRequest = 0x00;      // GET_STATUS request
    .wValue = 0x0000;      // Must be zero
    .wIndex = 0x01;        // Endpoint 1
    .wLength = 0x0004;     // Status length returns is 4 bytes
}

struct ptm_status_response {
    uint8_t status_code;     // Status code indicating the result of the request
    uint8_t ptm_capabilities;// PTM capabilities supported by the device
    uint16_t reserved;       // Reserved, typically set to 0
    uint32_t ptm_timestamp;  // PTM timestamp or relevant status data
};