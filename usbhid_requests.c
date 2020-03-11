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
#include "api/libusbhid.h"
#include "libusbctrl.h"
#include "libc/types.h"
#include "libc/stdio.h"
#include "usbhid.h"
#include "usbhid_descriptor.h"
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


#define USBHID_STD_ITEM_LEN             4

uint8_t usbhid_get_report_len(uint8_t index)
{
    usbhid_report_infos_t *report = usbhid_get_report(index);
    if (report == NULL) {
        return 0;
    }
    uint32_t offset = 0;

    for (uint32_t iterator = 0; iterator < report->num_items; ++iterator) {
        /* first byte is handling type, tag and size of the item */
        /* there can be one to three more bytes, depending on the item */
        if (report->items[iterator].size == 0) {
            offset += 1;
        } else if (report->items[iterator].size == 1) {
            offset += 2;
        } else if (report->items[iterator].size == 2) {
            offset += 3;
        } else {
            log_printf("[USBHID] invalid item size %d!\n", report->items[iterator].size);
            goto err;
        }
    }
err:
    return offset;
}

static mbed_error_t usbhid_forge_report(uint8_t *buf, uint32_t *bufsize, uint8_t index)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* define a buffer of num_items x max item size
     * these informations should be rodata content, defining the number of
     * item of collections and reports, specific to each upper stack profile
     * (FIDO, keyboard, etc.), they should not be dynamic content */

    if (buf == NULL || bufsize == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    uint32_t offset = 0;
    uint32_t iterator = 0;
    usbhid_report_infos_t *report = usbhid_get_report(index);
    if (report == NULL) {
        log_printf("[USBHID] report for index %d not found!\n", index);
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (*bufsize < (report->num_items * USBHID_STD_ITEM_LEN)) {
        log_printf("[USBHID] potential report size %d too big for buffer (%d bytes)\n",
                (report->num_items * USBHID_STD_ITEM_LEN), *bufsize);
    }

    /* let's forge the report */
    log_printf("[USBHID] collection size is %d\n", report->num_items);
    for (iterator = 0; iterator < report->num_items; ++iterator) {
        usbhid_short_item_t *item = (usbhid_short_item_t*)&(buf[offset]);
        item->bSize =  report->items[iterator].size;
        item->bType =  report->items[iterator].type;
        item->bTag =  report->items[iterator].tag;
        if (report->items[iterator].size == 0) {
            offset += 1;
        } else if (report->items[iterator].size == 1) {
            item->data1 =  report->items[iterator].data1;
            offset += 2;
        } else if (report->items[iterator].size == 2) {
            item->data1 =  report->items[iterator].data1;
            item->data2 =  report->items[iterator].data2;
            offset += 3;
        } else {
            log_printf("[USBHID] invalid item size %d!\n", report->items[iterator].size);
            goto err;
        }
    }
    usbhid_report_sent(index);
    /* and update the size with the report one */
    *bufsize = offset;
err:
    return errcode;
}

static mbed_error_t usbhid_handle_std_request(usbctrl_setup_pkt_t *pkt)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* get the high byte */
    uint8_t maxlen = pkt->wLength;
    uint8_t action = pkt->bRequest;
    uint8_t descriptor_type = pkt->wValue >> 0x8;
    uint8_t descriptor_index = pkt->wValue & 0xff;
    switch (action) {
        case USB_STD_RQST_ACTION_GET_DESCRIPTOR:
            switch (descriptor_type) {
                case DESCRIPTOR_TYPE_HID: {
                    log_printf("[USBHID] get_descriptor: HID DESC w/index: %d\n", descriptor_index);
                    break;
                }
                case DESCRIPTOR_TYPE_REPORT: {
                    log_printf("[USBHID] get_descriptor: REPORT DESC w/index: %d\n", descriptor_index);
                    /* getting back the collection size */

                    /* FIXME: to be replaced by calculated*/
                    uint8_t desc[256];
                    uint32_t size = 256;
                    usbhid_forge_report(&desc[0], &size, descriptor_index);
                    log_printf("[USBHID] written %d byte in descriptor\n", size);
                    /* now, offset define the collection size, desc handle it, we can send it */
                    /*1. configure descriptor */
                    /*2. send data */
                    usb_backend_drv_send_data(&(desc[0]), maxlen >= size ? size : maxlen, EP0);
//                    usb_backend_drv_ack(1, USB_BACKEND_DRV_EP_DIR_OUT);
                    usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
                    break;
                }
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
            /*TODO*/
            break;
        case USB_CLASS_RQST_GET_IDLE:
            /*TODO*/
            break;
        case USB_CLASS_RQST_GET_PROTOCOL:
            /*TODO*/
            break;
        case USB_CLASS_RQST_SET_REPORT:
            /* acknowledge current report (TODO) */
            usb_backend_drv_send_zlp(0);
            break;
        case USB_CLASS_RQST_SET_IDLE:
            /* acknowledge SET IDLE */
            usb_backend_drv_send_zlp(0);
            break;
        case USB_CLASS_RQST_SET_PROTOCOL:
            /*TODO*/
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


