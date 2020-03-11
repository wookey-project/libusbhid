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
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * ur option) any later version.
 *
 * This package is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this package; if not, write to the Free Software Foundation, Inc., 51
 * Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
 *
 */


#include "api/libusbhid.h"
#include "libusbctrl.h"
#include "usbhid.h"
#include "usbhid_requests.h"
#include "usbhid_descriptor.h"


#define MAX_HID_DESCRIPTORS 8

static volatile usbhid_context_t usbhid_ctx = { 0 };

static mbed_error_t usbhid_control_received(uint32_t dev_id, uint32_t size, uint8_t ep_id)
{
    dev_id = dev_id;
    size = size;
    ep_id = ep_id;
    return MBED_ERROR_NONE;
}

static mbed_error_t usbhid_data_sent(uint32_t dev_id, uint32_t size, uint8_t ep_id)
{
    dev_id = dev_id;
    size = size;
    ep_id = ep_id;
    return MBED_ERROR_NONE;
}

usbhid_context_t *usbhid_get_context(void)
{
    return (usbhid_context_t*)&usbhid_ctx;
}


mbed_error_t usbhid_declare(uint32_t usbxdci_handler,
                            usbhid_subclass_t hid_subclass,
                            usbhid_protocol_t hid_protocol,
                            uint8_t           num_descriptor)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* sanitize */
    if (num_descriptor == 0) {
        log_printf("[USBHID] error ! at least one descriptor for report is required!\n");
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (num_descriptor > MAX_HID_DESCRIPTORS) {
        log_printf("[USBHID] error ! too many class level descriptors!\n");
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    usbhid_ctx.num_reports = 0;
    usbhid_ctx.iface.usb_class = USB_CLASS_HID;
    usbhid_ctx.iface.usb_subclass = hid_subclass; /* SCSI transparent cmd set (i.e. use INQUIRY) */
    usbhid_ctx.iface.usb_protocol = hid_protocol; /* Protocol BBB (Bulk only) */
    usbhid_ctx.iface.dedicated = false;
    usbhid_ctx.iface.rqst_handler = usbhid_class_rqst_handler;
    usbhid_ctx.iface.class_desc_handler = usbhid_get_descriptor;
    usbhid_ctx.iface.usb_ep_number = 2;

    /*
     * Hid handle 2 endpoints:
     * EP0, for dedicated class-level request and synchronous (on host demand) data
     * transfer
     * another interrupt-based pipe, for aynchronous device-initiated data transfers
     * and low latency data transfer two the host (EP in IN direction)
     */

    /*
     * We request EP0 as control pipe in OUT mode (receiving) in order to receive data
     * from the host. Here, we inform the libusbctrl that we are the target of input
     * DATA content on EP0.
     *
     * Input class-level requests (and corresponding responses on EP0) will be handled
     * naturally by the usbhid_class_rqst_handler.
     */
    usbhid_ctx.iface.eps[0].type        = USB_EP_TYPE_CONTROL;
    usbhid_ctx.iface.eps[0].dir         = USB_EP_DIR_OUT;
    usbhid_ctx.iface.eps[0].attr        = USB_EP_ATTR_NO_SYNC;
    usbhid_ctx.iface.eps[0].usage       = USB_EP_USAGE_DATA;
    usbhid_ctx.iface.eps[0].pkt_maxsize = 64; /* mpsize on EP0, not considered by libusbctrl */
    usbhid_ctx.iface.eps[0].ep_num      = 0; /* not considered by libusbctrl for CONTROL EP */
    usbhid_ctx.iface.eps[0].handler     = usbhid_control_received;

    /*
     * Other EP for low latency data transmission with the host
     */
    usbhid_ctx.iface.eps[1].type        = USB_EP_TYPE_INTERRUPT;
    usbhid_ctx.iface.eps[1].dir         = USB_EP_DIR_IN;
    usbhid_ctx.iface.eps[1].attr        = USB_EP_ATTR_NO_SYNC;
    usbhid_ctx.iface.eps[1].usage       = USB_EP_USAGE_DATA;
    usbhid_ctx.iface.eps[1].pkt_maxsize = 512; /* mpsize on EP2 */
    usbhid_ctx.iface.eps[1].ep_num      = 2; /* this may be updated by libctrl */
    usbhid_ctx.iface.eps[1].handler     = usbhid_data_sent;


    usbctrl_declare_interface(usbxdci_handler, (usbctrl_interface_t*)&(usbhid_ctx.iface));

err:
    return errcode;
}

/*
 * report descriptor
 */
mbed_error_t usbhid_configure(uint8_t num_reports)
{
    /* TODO: physical descriptors can be added to report descriptors */
    usbhid_ctx.num_reports = num_reports;
    return MBED_ERROR_NONE;
}

mbed_error_t usbhid_send_report(usbhid_report_t* report,
                                uint32_t report_len)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    usb_backend_drv_send_data((uint8_t*)report, report_len, usbhid_ctx.iface.eps[1].ep_num);
    usb_backend_drv_ack(usbhid_ctx.iface.eps[1].ep_num, USB_BACKEND_DRV_EP_DIR_IN);
    return errcode;
}
