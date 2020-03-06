/*
 *
 * Copyright 2019 The wookey project team <wookey@ssi.gouv.fr>
 *   - Ryad     Benadjila
 *   - Arnauld  Michelizza
 *   - Mathieu  Renard
 *   - Philippe Thierry
 *   - Philippe Trebuchet
 *
 * This package is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published
 * the Free Software Foundation; either version 3 of the License, or (at
 * ur option) any later version.
 *
 * This package is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this package; if not, write to the Free Software Foundation, Inc., 51
 * Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
 *
 */
#include "libusbctrl.h"
#include "libc/types.h"
#include "libc/stdio.h"
#include "usbhid.h"
#include "autoconf.h"

/* USBHID class specific request (i.e. bRequestType is Type (bit 5..6 = 1, bits 0..4 target current iface
 * These values are set in bRequest field */
#define USB_CLASS_RQST_GET_REPORT           0x01
#define USB_CLASS_RQST_GET_IDLE             0x02
#define USB_CLASS_RQST_GET_PROTOCOL         0x03
#define USB_CLASS_RQST_SET_REPORT           0x09
#define USB_CLASS_RQST_SET_IDLE             0x0A
#define USB_CLASS_RQST_SET_PROTOCOL         0x0B

#define USB_STD_RQST_ACTION_GET_DESCRIPTOR 0x06
#define USB_STD_RQST_ACTION_SET_DESCRIPTOR 0x07

/* USBHID Get_Descriptor standard request targetting current interface.
 * These values are set in wValue high byte, when request is *not* class specific */
#define DESCRIPTOR_TYPE_HID             0x21
#define DESCRIPTOR_TYPE_REPORT          0x22
#define DESCRIPTOR_TYPE_PHYSICAL        0x23

static mbed_error_t usbhid_handle_std_request(usbctrl_setup_pkt_t *pkt)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* get the high byte */
    uint8_t action = pkt->bRequest;
    uint8_t descriptor_type = pkt->wValue >> 0x8;
    uint8_t descriptor_index = pkt->wValue & 0xff;
    switch (action) {
        case USB_STD_RQST_ACTION_GET_DESCRIPTOR:
            switch (descriptor_type) {
                case DESCRIPTOR_TYPE_HID:
                    log_printf("[USBHID] get_descriptor: HID DESC w/index: %d\n", descriptor_index);
#if 0
                    /*1. configure descriptor */
                    /*2. send data */
                    usb_backend_drv_send_data(&desc, sizeof(max_lun), EP0);
                    usb_backend_drv_endpoint_clear_nak(0, USBOTG_HS_EP_DIR_OUT);
#endif
                    break;
                case DESCRIPTOR_TYPE_REPORT:
                    log_printf("[USBHID] get_descriptor: REPORT DESC w/index: %d\n", descriptor_index);
                    break;
                case DESCRIPTOR_TYPE_PHYSICAL:
                    log_printf("[USBHID] get_descriptor: PHYSICAL DESC w/index: %d\n", descriptor_index);
                    break;
                default:
                    errcode = MBED_ERROR_INVPARAM;
                    log_printf("[USBHID] Ubnupported requested desc %d\n", descriptor_type);
                    goto err;
            }
            break;
        case USB_STD_RQST_ACTION_SET_DESCRIPTOR:
            switch (descriptor_type) {
                case DESCRIPTOR_TYPE_HID:
                    log_printf("[USBHID] set_descriptor: HID DESC w/index: %d\n", descriptor_index);
                    break;
                case DESCRIPTOR_TYPE_REPORT:
                    log_printf("[USBHID] set_descriptor: REPORT DESC w/index: %d\n", descriptor_index);
                    break;
                case DESCRIPTOR_TYPE_PHYSICAL:
                    log_printf("[USBHID] set_descriptor: PHYSICAL DESC w/index: %d\n", descriptor_index);
                    break;
                default:
                    errcode = MBED_ERROR_INVPARAM;
                    log_printf("[USBHID] Unsupported set_desc %d\n", descriptor_type);
                    goto err;
            }
            break;
        default:
            log_printf("[USBHID] Unsupported class request action %x", action);
    }
err:
    return errcode;
}

static mbed_error_t usbhid_handle_class_request(usbctrl_setup_pkt_t *pkt)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t action = pkt->bRequest;
    switch (action) {
        case USB_CLASS_RQST_GET_REPORT:
            break;
        case USB_CLASS_RQST_GET_IDLE:
            break;
        case USB_CLASS_RQST_GET_PROTOCOL:
            break;
        case USB_CLASS_RQST_SET_REPORT:
            break;
        case USB_CLASS_RQST_SET_IDLE:
            break;
        case USB_CLASS_RQST_SET_PROTOCOL:
            break;
        default:
            log_printf("[USBHID] Ubsupported class request action %x", action);
    }

    return errcode;
}


/**
 * \brief Class request handling for bulk mode.
 *
 * @param packet Setup packet
 */
mbed_error_t usbhid_class_rqst_handler(uint32_t usbxdci_handler __attribute__((unused)),
                                       usbctrl_setup_pkt_t *packet)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    log_printf("[classRqst] handling HID class rqst\n");
    if (((packet->bmRequestType >> 5) & 0x3) == 1) {
        /* class request */
        errcode = usbhid_handle_class_request(packet);
    } else {
        /* standard request targetting current iface */
        errcode = usbhid_handle_std_request(packet);
    }
    return errcode;
}


