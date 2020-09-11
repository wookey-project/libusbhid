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
#include "libc/string.h"
#include "libusbctrl.h"
#include "usbhid.h"
#include "usbhid_requests.h"
#include "usbhid_reports.h"
#include "usbhid_descriptor.h"
#include "usbhid_default_handlers.h"
#include "libc/sanhandlers.h"


#define MAX_HID_DESCRIPTORS 8

volatile bool data_being_sent = false;

static volatile usbhid_context_t usbhid_ctx = { 0 };


/*
 * Only if trigger not defined in the above stack.
 */
__attribute__((weak)) mbed_error_t usbhid_report_received_trigger(uint8_t hid_handler __attribute__((unused)),
                                                                  uint16_t size __attribute__((unused)))
{
    return MBED_ERROR_NONE;
}

static inline uint8_t get_in_epid(volatile usbctrl_interface_t *iface)
{
    /* sanitize */
    if (iface == NULL) {
        return 0;
    }
    for (uint8_t i = 0; i < iface->usb_ep_number; ++i) {
        if (iface->eps[i].dir == USB_EP_DIR_IN) {
            log_printf("[USBHID] IN EP is %d\n", iface->eps[i].ep_num);
            return iface->eps[i].ep_num;
        }
    }
    return 0;
}

static inline uint8_t get_out_epid(volatile usbctrl_interface_t *iface)
{
    /* sanitize */
    if (iface == NULL) {
        return 0;
    }
    for (uint8_t i = 0; i < iface->usb_ep_number; ++i) {
        if (iface->eps[i].dir == USB_EP_DIR_OUT) {
            log_printf("[USBHID] OUT EP is %d\n", iface->eps[i].ep_num);
            return iface->eps[i].ep_num;
        }
    }
    return 0;
}

/*
 * A HID packet has been received on a dedicated (or not) OUTPUT Endpoint.
 * This HID packet is considered as a RAW HID packet. The HID layer is treated here and
 * if there is an upper layer registered against the HID stack, the decapsulated HID
 * packet is transmitted to the upper layer.
 * HID report should respect the declared report size for the corresponding report id.
 * for e.g. FIDO reports are typically upto 64 bytes length.
 */
static mbed_error_t usbhid_received(uint32_t dev_id, uint32_t size, uint8_t ep_id)
{
    log_printf("[USBHID] HID packet (%d B) received on ep %d\n", size, ep_id);
    for (uint8_t iface = 0; iface < usbhid_ctx.num_iface; ++iface)
    {
        for (uint8_t ep = 0; ep < usbhid_ctx.hid_ifaces[iface].iface.usb_ep_number; ++ep)
        {

            if (usbhid_ctx.hid_ifaces[iface].iface.eps[ep].ep_num == ep_id)
            {
                usbhid_report_received_trigger(iface, size);
            }
        }
    }
    dev_id = dev_id;
    return MBED_ERROR_NONE;
}

/*
 * TODO HID state must be handled by report send/sent pair to handle properly busy state
 * Moreover, set_idle require a state automaton at usbhid level to lock IN Endpoint transmission
 * for time given in SET_IDLE requests
 */
static mbed_error_t usbhid_data_sent(uint32_t dev_id, uint32_t size, uint8_t ep_id)
{
    log_printf("[USBHID] data (%d B) sent on EP %d\n", size, ep_id);
    ep_id = ep_id;
    dev_id = dev_id;
    size = size;
    data_being_sent = false;

    //usb_backend_drv_ack(usbhid_ctx.iface.eps[1].ep_num, USB_BACKEND_DRV_EP_DIR_IN);
    return MBED_ERROR_NONE;
}

usbhid_context_t *usbhid_get_context(void)
{
    return (usbhid_context_t*)&usbhid_ctx;
}

bool usbhid_interface_exists(uint8_t hid_handler)
{
    usbhid_context_t *ctx = usbhid_get_context();
    if (hid_handler < ctx->num_iface) {
        return true;
    }
    return false;
}



mbed_error_t usbhid_declare(uint32_t usbxdci_handler,
                            usbhid_subclass_t hid_subclass,
                            usbhid_protocol_t hid_protocol,
                            uint8_t           num_descriptor,
                            uint8_t           poll_time,
                            bool              dedicated_out_ep,
                            uint16_t          ep_mpsize,
                            uint8_t          *hid_handler,
                            uint8_t          *in_buff,
                            uint32_t          in_buff_len)
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
    if (hid_handler == NULL) {
        log_printf("[USBHID] error ! hid_handler is null!\n");
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    uint8_t i = usbhid_ctx.num_iface;
    memset((void*)&usbhid_ctx.hid_ifaces[i], 0x0, sizeof(usbctrl_interface_t));

    ADD_LOC_HANDLER(usbhid_class_rqst_handler);
    ADD_LOC_HANDLER(usbhid_get_descriptor);
    ADD_LOC_HANDLER(usbhid_data_sent);
    ADD_LOC_HANDLER(usbhid_received);

    usbhid_ctx.hid_ifaces[i].iface.usb_class = USB_CLASS_HID;
    usbhid_ctx.hid_ifaces[i].iface.usb_subclass = hid_subclass; /* SCSI transparent cmd set (i.e. use INQUIRY) */
    usbhid_ctx.hid_ifaces[i].iface.usb_protocol = hid_protocol; /* Protocol BBB (Bulk only) */
    usbhid_ctx.hid_ifaces[i].iface.dedicated = false;
    usbhid_ctx.hid_ifaces[i].iface.rqst_handler = usbhid_class_rqst_handler;
    usbhid_ctx.hid_ifaces[i].iface.class_desc_handler = usbhid_get_descriptor;

    /*
     * Hid handle 2 endpoints:
     * EP0, for dedicated class-level request and synchronous (on host demand) data
     * transfer
     * another interrupt-based pipe, for aynchronous device-initiated data transfers
     * and low latency data transfer two the host (EP in IN direction)
     */

    uint8_t curr_ep = 0;
    /*
     * IN EP for low latency data transmission with the host
     */
    usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].type        = USB_EP_TYPE_INTERRUPT;
    usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].dir         = USB_EP_DIR_IN;
    usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].attr        = USB_EP_ATTR_NO_SYNC;
    usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].usage       = USB_EP_USAGE_DATA;
    usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].pkt_maxsize = ep_mpsize; /* mpsize on EP1 */
    usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].ep_num      = 1; /* this may be updated by libctrl */
    usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].handler     = usbhid_data_sent;
    usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].poll_interval = poll_time;
    curr_ep++;


    if (dedicated_out_ep == false) {
        /* using control EP out as OUT EP instead of dedicated. This EP should be
         * declared once when declaring multiple interfaces */
        if (i == 0) {
            /*
             * This is the first HID interface we declare, we request an access to EP0
             * if this is a second (or a third...) we already have a EP0 handler, and this
             * EP is not requested :-)
             *
             * We request EP0 as control pipe in OUT mode (receiving) in order to receive data
             * from the host. Here, we inform the libusbctrl that we are the target of input
             * DATA content on EP0.
             *
             * Input class-level requests (and corresponding responses on EP0) will be handled
             * naturally by the usbhid_class_rqst_handler.
             */
            usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].type        = USB_EP_TYPE_CONTROL;
            usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].dir         = USB_EP_DIR_OUT;
            usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].attr        = USB_EP_ATTR_NO_SYNC;
            usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].usage       = USB_EP_USAGE_DATA;
            usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].pkt_maxsize = ep_mpsize; /* mpsize on EP0, not considered by libusbctrl */
            usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].ep_num      = 0; /* not considered by libusbctrl for CONTROL EP */
            usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].handler     = usbhid_received;
            curr_ep++;
        }
    } else {
        /*
         * OUT EP for low latency data transmission with the host
         */
        usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].type        = USB_EP_TYPE_INTERRUPT;
        usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].dir         = USB_EP_DIR_OUT;
        usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].attr        = USB_EP_ATTR_NO_SYNC;
        usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].usage       = USB_EP_USAGE_DATA;
        usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].pkt_maxsize = ep_mpsize; /* mpsize on EP1 */
        usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].ep_num      = 2; /* this may be updated by libctrl */
        usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].handler     = usbhid_received;
        usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].poll_interval = poll_time;
        curr_ep++;

    }

    usbhid_ctx.hid_ifaces[i].iface.usb_ep_number = curr_ep;


    errcode = usbctrl_declare_interface(usbxdci_handler, (usbctrl_interface_t*)&(usbhid_ctx.hid_ifaces[i].iface));
    if (errcode != MBED_ERROR_NONE) {
        log_printf("[USBHID] Error while declaring interface: err=%d !\n", errcode);
        goto err;
    }

    /* set IN EP real identifier */
    uint8_t epid = get_in_epid(&usbhid_ctx.hid_ifaces[i].iface);
    usbhid_ctx.hid_ifaces[i].inep.id = epid;
    for (uint8_t j = 0; j < MAX_HID_REPORTS; ++j) {
        usbhid_ctx.hid_ifaces[i].inep.idle_ms[j] = 0;
        usbhid_ctx.hid_ifaces[i].inep.silence[j] = true; /* silent while no event associated to this EP is received */
    }
    /* set current interface effective identifier */
    usbhid_ctx.hid_ifaces[i].id   = usbhid_ctx.hid_ifaces[i].iface.id;
    usbhid_ctx.hid_ifaces[i].num_descriptors = num_descriptor;
    usbhid_ctx.hid_ifaces[i].dedicated_out_ep = dedicated_out_ep;
    usbhid_ctx.hid_ifaces[i].in_buff = in_buff;
    usbhid_ctx.hid_ifaces[i].in_buff_len = in_buff_len;

    /* the configuration step not yet passed */
    usbhid_ctx.hid_ifaces[i].configured = false;

    *hid_handler = usbhid_ctx.num_iface;
    usbhid_ctx.num_iface++;

err:
    return errcode;
}

mbed_error_t usbhid_configure(uint8_t               hid_handler,
                              usbhid_get_report_t   get_report_cb,
                              usbhid_set_report_t   set_report_cb,
                              usbhid_set_protocol_t set_proto_cb,
                              usbhid_set_idle_t     set_idle_cb)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbhid_context_t *ctx = usbhid_get_context();
    /* sanitize */
    if (!usbhid_interface_exists(hid_handler)) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (get_report_cb == NULL) {
        /* At least this one must be set! */
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    /* set each of the interface callbacks */
    ctx->hid_ifaces[hid_handler].get_report_cb = get_report_cb;

    if (set_report_cb != NULL) {
        ctx->hid_ifaces[hid_handler].set_report_cb = set_report_cb;
    } else {
        ctx->hid_ifaces[hid_handler].set_report_cb = usbhid_dflt_set_report;
    }

    if (set_proto_cb != NULL) {
        ctx->hid_ifaces[hid_handler].set_proto_cb = set_proto_cb;
    } else {
        ctx->hid_ifaces[hid_handler].set_proto_cb = usbhid_dflt_set_protocol;
    }

    if (set_idle_cb != NULL) {
        ctx->hid_ifaces[hid_handler].set_idle_cb = set_idle_cb;
    } else {
        ctx->hid_ifaces[hid_handler].set_idle_cb = usbhid_dflt_set_idle;
    }

    /* set interface as configured */
    ctx->hid_ifaces[hid_handler].configured = true;
err:
    return errcode;
}


mbed_error_t usbhid_send_response(uint8_t              hid_handler,
                                  uint8_t*             response,
                                  uint8_t              response_len)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (response == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (!usbhid_interface_exists(hid_handler)) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /* first field is the report index */
    /* wait for previous data to be fully transmitted */
    while (data_being_sent == true) {
        ;
    }
    data_being_sent = true;
    /* total size is report + report id (one byte) */
    uint8_t epid = get_in_epid(&usbhid_ctx.hid_ifaces[hid_handler].iface);
    log_printf("[USBHID] sending response on EP %d (len %d)\n", epid, response_len);

    usb_backend_drv_send_data(response, response_len, epid);
    /* wait for end of transmission */
    while (data_being_sent == true) {
        ;
    }
    /* ZLP should not be automatically sent, as the fragmentation is handled also in upper stack */
    /* XXX: needed ? */
    data_being_sent = false;
err:
    return errcode;
}



mbed_error_t usbhid_send_report(uint8_t              hid_handler,
                                uint8_t*             report,
                                usbhid_report_type_t type,
                                uint8_t              report_index)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint32_t len = 0;
    if (report == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (!usbhid_interface_exists(hid_handler)) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /* first field is the report index */
    uint8_t buf[256] = { 0 };
    len = usbhid_get_report_len(hid_handler, type, report_index);
    if (len == 0) {
        log_printf("[USBHID] unable to get back report len for iface %d/idx %d\n", hid_handler, report_index);
    }
    /* wait for previous data to be fully transmitted */
    while (data_being_sent == true) {
        ;
    }
    data_being_sent = true;
    /* is a report id needed ? if a REPORT_ID is defined in the report descriptor, it is added,
     * otherwise, items are sent directly */
    if (usbhid_report_needs_id(hid_handler, report_index)) {
        buf[0] = usbhid_report_get_id(hid_handler, report_index);
        log_printf("[USBHID] this report requires its ID (0x%x) to be sent\n", buf[0]);
        memcpy((void*)&buf[1], (void*)report, len);
        len++;
    } else {
        log_printf("[USBHID] sending report without ID\n");
        memcpy((void*)&buf[0], (void*)report, len);
    }

    /* total size is report + report id (one byte) */
    uint8_t epid = get_in_epid(&usbhid_ctx.hid_ifaces[hid_handler].iface);
    log_printf("[USBHID] sending report on EP %d (len %d)\n", epid, len);

    data_being_sent = true;
    usb_backend_drv_send_data(buf, len, epid);
    /* wait for end of transmission */
    while (data_being_sent == true) {
        ;
    }
    /* finishing with ZLP */
    usb_backend_drv_send_zlp(epid);
    /* XXX: needed ? */
    data_being_sent = false;
err:
    return errcode;
}

bool usbhid_is_silence_requested(uint8_t hid_handler, uint8_t index)
{
    if (index >= MAX_HID_REPORTS) {
        return true;
    }
    /* when setting idle_ms to 0, silence is requested while no event arrise on the
     * corresponding report index */
    return usbhid_ctx.hid_ifaces[hid_handler].inep.silence[index];
}

uint16_t usbhid_get_requested_idle(uint8_t hid_handler, uint8_t index)
{
    if (index >= MAX_HID_REPORTS) {
        return 0;
    }
    return usbhid_ctx.hid_ifaces[hid_handler].inep.idle_ms[index];
}


/*
 * HID DATA OUT endpoint may be:
 * 1. EP0, updated to handle data content
 * 2. EPx dedicated EP
 *
 * In the first case, the recv FIFO must be updated each time the device actively wait for
 * an effective DATA content. This is done at the end of a setup stage when a non-zero data stage is
 * configued
 * In the second case, the recv FIFO is dedicated in the corresponding EP. Though it should be
 * configured each time the device application is ready to receive data from host
 */
mbed_error_t usbhid_recv_report(uint8_t hid_handler __attribute__((unused)), uint8_t *report, uint16_t size)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t ep_id = 0;
    /* get back EP identifier from HID handler */
    for (uint8_t iface = 0; iface < usbhid_ctx.num_iface; ++iface)
    {
        for (uint8_t ep = 0; ep < usbhid_ctx.hid_ifaces[iface].iface.usb_ep_number; ++ep)
        {

            if (usbhid_ctx.hid_ifaces[iface].iface.eps[ep].dir == USB_EP_DIR_OUT)
            {
                ep_id = usbhid_ctx.hid_ifaces[iface].iface.eps[ep].ep_num;
                goto set_fifo;
            }
        }
    }

    /* OUT EP not found */
    log_printf("[USBHID] OUT EP not found for HID handler %d\n", hid_handler);
    errcode = MBED_ERROR_UNKNOWN;
    goto err;

set_fifo:
    /* set recv FIFO */
    errcode = usb_backend_drv_set_recv_fifo(report, size, ep_id);
    /* activate Endpoint (Ack sent, ready to recv) */
    /*XXX: is this is required for EP0 ? Compare with DFU implementation to check */
    usb_backend_drv_activate_endpoint(ep_id, USB_BACKEND_DRV_EP_DIR_OUT);
    /* no automaton at HID state. This is handled by upper class if needed */
    log_printf("[USBHID] OUT EP %d set and ready to receive at most %d bytes\n", ep_id, size);

err:
    return errcode;
}
