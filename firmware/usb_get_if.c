#include "usb_defines.h"
#include "usb_struct.h"

int get_interface(int interface_number, uint8_t *alternate_setting) {
    struct usb_configuration_request get_interface_request = {
        .bmRequestType = 0x81,
        .bRequest = USB_REQ_GET_INTERFACE,
        .wValue = 0,
        .wIndex = interface_number,
        .wLength = 1
    };

    int result = usb_control_transfer(&get_interface_request, alternate_setting, 1);
    
    if (result < 0) {
        // Handle error
        return result;
    }

    if (result != 1) {
        // Didn't get the expected amount of data
        return -1;
    }

    return 0;  // Success
}