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
#include "libc/sync.h"
#include "libusbctrl.h"
#include "usbhid.h"
#include "usbhid_requests.h"
#include "usbhid_reports.h"
#include "usbhid_descriptor.h"
#include "usbhid_default_handlers.h"
#include "libc/sanhandlers.h"

/*@
  assigns \nothing;
  */
void usbctrl_configuration_set(void)
{
    return;
}



#ifndef __FRAMAC__
static bool data_being_sent = false;

#define MAX_HID_DESCRIPTORS 8

static usbhid_context_t usbhid_ctx = { 0 };

/*
 * Only if trigger not defined in the above stack.
 */
__attribute__((weak)) mbed_error_t usbhid_report_received_trigger(uint8_t hid_handler __attribute__((unused)),
                                                                  uint16_t size __attribute__((unused)))
{
    return MBED_ERROR_NONE;
}
#endif


/*@
  @ assigns \nothing ;
  @ ensures usbhid_ctx.num_iface <= MAX_USBHID_IFACES;

  @ behavior gie_invalid_iface:
  @   assumes iface == NULL ;
  @   ensures \result == 0;

  @ behavior gie_invalid_maxep:
  @   assumes iface != NULL ;
  @   assumes iface->usb_ep_number >= MAX_EP_PER_INTERFACE ;
  @   ensures \result == 0;

  @ behavior gie_ep_found:
  @   assumes iface != NULL ;
  @   assumes iface->usb_ep_number < MAX_EP_PER_INTERFACE ;
  @   assumes \exists integer i ; 0 <= i < iface->usb_ep_number && (iface->eps[i].dir == USB_EP_DIR_IN || iface->eps[i].dir == USB_EP_DIR_BOTH) ;
  @   ensures \result >= 0 && \result <= 255 ; // no upper limit at HID level, upper limit is handled at driver level

  // seems that this behavior is dead code (impossible to reach through normal call graph)
  @ behavior gie_ep_not_found:
  @   assumes iface != NULL ;
  @   assumes iface->usb_ep_number < MAX_EP_PER_INTERFACE ;
  @   assumes \forall integer i ; 0 <= i < iface->usb_ep_number ==> (iface->eps[i].dir != USB_EP_DIR_IN && iface->eps[i].dir != USB_EP_DIR_BOTH) ;
  @   ensures \result == 0;

  @ complete behaviors;
  @ disjoint behaviors;

 */
#ifndef __FRAMAC__
static inline
#endif
uint8_t get_in_epid(usbctrl_interface_t const * const iface)
{
    uint8_t epin = 0;
    uint8_t iface_ep_num = 0;
    /* sanitize */
    if (iface == NULL) {
        goto err;
    }
    if (iface->usb_ep_number >= MAX_EP_PER_INTERFACE) {
        goto err;
    }
    iface_ep_num = iface->usb_ep_number;
    /*@ assert iface_ep_num < MAX_EP_PER_INTERFACE ; */

    uint8_t i = 0;
    /*@
      @ loop invariant 0 <= i <= iface_ep_num ;
      @ loop assigns i ;
      @ loop variant (iface_ep_num - i);
      */
    for (i = 0; i < iface_ep_num; ++i) {
        if (iface->eps[i].dir == USB_EP_DIR_IN || iface->eps[i].dir == USB_EP_DIR_BOTH) {
            log_printf("[USBHID] IN EP is %d\n", iface->eps[i].ep_num);
            epin = iface->eps[i].ep_num;
            goto err;
        }
    }
err:
    return epin;
}


/*
 * A HID packet has been received on a dedicated (or not) OUTPUT Endpoint.
 * This HID packet is considered as a RAW HID packet. The HID layer is treated here and
 * if there is an upper layer registered against the HID stack, the decapsulated HID
 * packet is transmitted to the upper layer.
 * HID report should respect the declared report size for the corresponding report id.
 * for e.g. FIDO reports are typically upto 64 bytes length.
 */
#ifndef __FRAMAC__
static
#endif
/*@ requires \separated(&usbhid_ctx,&GHOST_opaque_drv_privates);
  @ assigns \nothing; */
mbed_error_t usbhid_received(uint32_t dev_id __attribute__((unused)), uint32_t size, uint8_t ep_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t iface = 0;
    log_printf("[USBHID] Huint8_t ID packet (%d B) received on ep %d\n", size, ep_id);


    /*@ assert \valid(usbhid_ctx.hid_ifaces + (0 .. usbhid_ctx.num_iface)) ;*/
    /*@
      @ loop invariant 0 <= iface <= usbhid_ctx.num_iface ;
      @ loop assigns iface ;
      @ loop variant (usbhid_ctx.num_iface - iface) ;
      */
    for (iface = 0; iface < usbhid_ctx.num_iface; ++iface)
    {
        if (usbhid_ctx.hid_ifaces[iface].iface.usb_ep_number >= MAX_EP_PER_INTERFACE) {
            errcode = MBED_ERROR_INVPARAM;
            goto err;
        }

        uint8_t ep = 0;
        const uint8_t max_ep_number = usbhid_ctx.hid_ifaces[iface].iface.usb_ep_number;
        /*@ assert 0 <= max_ep_number < MAX_EP_PER_INTERFACE; */
        /*@ assert \valid(usbhid_ctx.hid_ifaces[iface].iface.eps + (0 .. max_ep_number - 1)) ; */
        /*@
          @ loop invariant 0 <= ep <= max_ep_number ;
          @ loop assigns ep ;
          @ loop variant (max_ep_number - ep) ;
          */
        for (ep = 0; ep < max_ep_number; ++ep)
        {
            if (usbhid_ctx.hid_ifaces[iface].iface.eps[ep].ep_num == ep_id)
            {
                log_printf("[USBHID] executing trigger for EP %d\n", ep_id);
                usbhid_report_received_trigger(iface, size);
                goto err;
            }
        }
    }
err:
    return errcode;
}

/*
 * TODO HID state must be handled by report send/sent pair to handle properly busy state
 * Moreover, set_idle require a state automaton at usbhid level to lock IN Endpoint transmission
 * for time given in SET_IDLE requests
 */
#ifndef __FRAMAC__
static
#endif
mbed_error_t usbhid_data_sent(uint32_t dev_id __attribute__((unused)), uint32_t size __attribute__((unused)), uint8_t ep_id __attribute((unused)))
{
    log_printf("[USBHID] data (%d B) sent on EP %d\n", size, ep_id);
    set_bool_with_membarrier(&data_being_sent, false);
    return MBED_ERROR_NONE;
}


/*@
  @ assigns \nothing ;
  @ ensures \result == &usbhid_ctx;
  */
usbhid_context_t *usbhid_get_context(void)
{
    return (usbhid_context_t*)&usbhid_ctx;
}

/*@
  @ assigns \nothing ;
  @ ensures usbhid_ctx.num_iface <= MAX_USBHID_IFACES;

  @ behavior uie_invalid_handler:
  @   assumes hid_handler >= usbhid_ctx.num_iface ||hid_handler >=MAX_USBHID_IFACES;
  @   ensures \result == \false;

  @ behavior uie_undeclared_iface:
  @   assumes hid_handler < usbhid_ctx.num_iface && hid_handler < MAX_USBHID_IFACES ;
  @   assumes usbhid_ctx.hid_ifaces[hid_handler].declared == \false;
  @   ensures \result == \false;

  @ behavior uie_ok:
  @   assumes hid_handler < usbhid_ctx.num_iface&& hid_handler < MAX_USBHID_IFACES ;
  @   assumes usbhid_ctx.hid_ifaces[hid_handler].declared == \true;
  @   ensures \result == \true;

  @ complete behaviors;
  @ disjoint behaviors;

 */
bool usbhid_interface_exists(uint8_t hid_handler)
{
    usbhid_context_t *ctx = usbhid_get_context();
    bool result = false;
    if (hid_handler < ctx->num_iface && hid_handler < MAX_USBHID_IFACES) {
        /* INFO: boolean normalization based on false (lonely checked value.
         * Thus, this is not fault-resilient as any non-zero value generates a
         * TRUE result */
        result = !(ctx->hid_ifaces[hid_handler].declared == false);
    }
    return result;
}

#ifndef __FRAMAC__
/* INFO: must be exported in order to be triggered by EVA */
static
#endif
mbed_error_t usbhid_ep_trigger(uint32_t dev_id, uint32_t size, uint8_t ep_id)
{
    /* full duplex trigger, detect if the event on the EP is a IN event or an OUT event,
     * and call the corresponding function */

    usb_ep_dir_t dir;
    usb_backend_drv_ep_state_t state;
    mbed_error_t errcode;

    log_printf("[USBHID] triggered on IN or OUT event\n");
    /* are we currently receiving content (DATA_OUT state ? */
    state = usb_backend_drv_get_ep_state(ep_id, USB_BACKEND_DRV_EP_DIR_OUT);
    if (state == USB_BACKEND_DRV_EP_STATE_DATA_OUT) {
        dir = USB_EP_DIR_OUT;
    } else {
        dir = USB_EP_DIR_IN;
    }
    /* otherwhise, we have been triggering on data sent */

    switch (dir) {
        case USB_EP_DIR_IN:
            log_printf("[USBHID] triggered on IN event\n");
            errcode = usbhid_data_sent(dev_id, size, ep_id);
            break;
        case USB_EP_DIR_OUT:
            log_printf("[USBHID] triggered on OUT event\n");
            errcode = usbhid_received(dev_id, size, ep_id);
            break;
        default:
            /* should never happend (dead block) */
            break;
    }
    return errcode;
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
    if (num_descriptor >= MAX_HID_DESCRIPTORS) {
        log_printf("[USBHID] error ! too many class level descriptors!\n");
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (hid_handler == NULL) {
        log_printf("[USBHID] error ! hid_handler is null!\n");
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (usbhid_ctx.num_iface >= MAX_USBHID_IFACES) {
        log_printf("[USBHID] error ! no more iface storage !\n");
        errcode = MBED_ERROR_NOSTORAGE;
        goto err;
    }
    if (in_buff == NULL) {
        log_printf("[USBHID] error ! buffer given is null !\n");
        errcode = MBED_ERROR_NOSTORAGE;
        goto err;
    }
    if (in_buff_len == 0) {
        log_printf("[USBHID] error ! buffer given is null-sized !\n");
        errcode = MBED_ERROR_NOSTORAGE;
        goto err;
    }


    uint8_t i = usbhid_ctx.num_iface;
#ifndef __FRAMAC__
    /* INFO: memset, as it uses void* types, is incompatible with assigns constraint.
     * Wait for the -instanciate mode to be compatible with -nostd use case to allow memset instanciation
     * by framaC.
     */
    memset((void*)&usbhid_ctx.hid_ifaces[i], 0x0, sizeof(usbctrl_interface_t));
#else
    usbhid_ctx.hid_ifaces[i].inep.id = 0;
    /*@
      @ loop invariant 0 <= k <= MAX_HID_REPORTS;
      @ loop assigns k, usbhid_ctx.hid_ifaces[i].inep.idle_ms[0 .. MAX_HID_REPORTS-1];
      @ loop variant MAX_HID_REPORTS - k;
      */
    for (uint8_t k = 0; k < MAX_HID_REPORTS; ++k) {
        usbhid_ctx.hid_ifaces[i].inep.idle_ms[k] = 0;
    }
    /*@
      @ loop invariant 0 <= k <= MAX_HID_REPORTS;
      @ loop assigns k, usbhid_ctx.hid_ifaces[i].inep.silence[0 .. MAX_HID_REPORTS-1];
      @ loop variant MAX_HID_REPORTS - k;
      */
    for (uint8_t k = 0; k < MAX_HID_REPORTS; ++k) {
        usbhid_ctx.hid_ifaces[i].inep.silence[k] = false;
    }
    /* no need to set iface as it is fully set just below */
    usbhid_ctx.hid_ifaces[i].num_descriptors = 0;
    usbhid_ctx.hid_ifaces[i].dedicated_out_ep = 0;
    usbhid_ctx.hid_ifaces[i].in_buff = NULL;
    usbhid_ctx.hid_ifaces[i].in_buff_len = 0;
    usbhid_ctx.hid_ifaces[i].get_report_cb = NULL;
    usbhid_ctx.hid_ifaces[i].set_report_cb = NULL;
    usbhid_ctx.hid_ifaces[i].set_proto_cb = NULL;
    usbhid_ctx.hid_ifaces[i].set_idle_cb = NULL;
    usbhid_ctx.hid_ifaces[i].configured = false;
    usbhid_ctx.hid_ifaces[i].declared = false;
#endif

#ifndef __FRAMAC__
    ADD_LOC_HANDLER(usbhid_class_rqst_handler);
    ADD_LOC_HANDLER(usbhid_get_descriptor);
    if (dedicated_out_ep == false) {
        ADD_LOC_HANDLER(usbhid_data_sent);
        ADD_LOC_HANDLER(usbhid_received);
    } else {
        ADD_LOC_HANDLER(usbhid_ep_trigger);
    }
#endif

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

    if (dedicated_out_ep == false) {
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
         * IN & OUT dedicated EP for low latency data transmission with the host
         */
        usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].type        = USB_EP_TYPE_INTERRUPT;
        usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].dir         = USB_EP_DIR_BOTH;
        usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].attr        = USB_EP_ATTR_NO_SYNC;
        usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].usage       = USB_EP_USAGE_DATA;
        usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].pkt_maxsize = ep_mpsize; /* mpsize on EP1 */
        usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].ep_num      = 1; /* this may be updated by libctrl */
        usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].handler     = usbhid_ep_trigger;
        usbhid_ctx.hid_ifaces[i].iface.eps[curr_ep].poll_interval = poll_time;
        curr_ep++;

    }

    /* @ assert curr_ep <= 2 ; */
    usbhid_ctx.hid_ifaces[i].iface.usb_ep_number = curr_ep;


    errcode = usbctrl_declare_interface(usbxdci_handler, (usbctrl_interface_t*)&(usbhid_ctx.hid_ifaces[i].iface));
    if (errcode != MBED_ERROR_NONE) {
        log_printf("[USBHID] Error while declaring interface: err=%d !\n", errcode);
        goto err;
    }

    /* set IN EP real identifier */
    uint8_t epid = get_in_epid(&usbhid_ctx.hid_ifaces[i].iface);
    usbhid_ctx.hid_ifaces[i].inep.id = epid;

    uint8_t j = 0;
    /*@
        @ loop invariant 0 <= j <= MAX_HID_REPORTS;
        @ loop invariant \valid(usbhid_ctx.hid_ifaces[i].inep.idle_ms + (0..(MAX_HID_REPORTS-1))) ;
        @ loop invariant \valid(usbhid_ctx.hid_ifaces[i].inep.silence + (0..(MAX_HID_REPORTS-1))) ;
        @ loop assigns j;
        @ loop assigns usbhid_ctx.hid_ifaces[i].inep.idle_ms[0..(MAX_HID_REPORTS-1)] ;
        @ loop assigns usbhid_ctx.hid_ifaces[i].inep.silence[0..(MAX_HID_REPORTS-1)] ;
        @ loop variant (MAX_HID_REPORTS - j);
    */
    for (j = 0; j < MAX_HID_REPORTS; ++j) {
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
    usbhid_ctx.hid_ifaces[i].declared = true;

    *hid_handler = usbhid_ctx.num_iface;
    usbhid_ctx.num_iface++;
    request_data_membarrier();

err:
    return errcode;
}

mbed_error_t usbhid_configure(uint8_t               hid_handler,
                              usbhid_get_report_t   get_report,
                              usbhid_set_report_t   set_report,
                              usbhid_set_protocol_t set_proto,
                              usbhid_set_idle_t     set_idle)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbhid_context_t *ctx = usbhid_get_context();
    /* sanitize */
    if (!usbhid_interface_exists(hid_handler)) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (get_report == NULL) {
        /* At least this one must be set! */
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /*@ assert errcode==MBED_ERROR_NONE; */
    /* set each of the interface callbacks */
    ctx->hid_ifaces[hid_handler].get_report_cb = get_report;
    /* @ assert ctx->hid_ifaces[hid_handler].get_report_cb ∈ {oneidx_get_report_cb,  twoidx_get_report_cb} ;)*/

    if (set_report != NULL) {
        ctx->hid_ifaces[hid_handler].set_report_cb = set_report;
        /* @ assert ctx->hid_ifaces[hid_handler].set_report_cb ∈ {set_report_cb} ;)*/
    } else {
        ctx->hid_ifaces[hid_handler].set_report_cb = usbhid_dflt_set_report;
        /* @ assert ctx->hid_ifaces[hid_handler].set_report_cb ∈ {usbhid_dflt_set_report} ;)*/
    }

    if (set_proto != NULL) {
        ctx->hid_ifaces[hid_handler].set_proto_cb = set_proto;
        /* @ assert ctx->hid_ifaces[hid_handler].set_proto_cb ∈ {set_proto} ;)*/
    } else {
        ctx->hid_ifaces[hid_handler].set_proto_cb = usbhid_dflt_set_protocol;
        /* @ assert ctx->hid_ifaces[hid_handler].set_proto_cb ∈ {usbhid_dflt_set_protocol} ;)*/
    }

    if (set_idle != NULL) {
        ctx->hid_ifaces[hid_handler].set_idle_cb = set_idle;
        /* @ assert ctx->hid_ifaces[hid_handler].set_idle_cb ∈ {set_idle} ;)*/
    } else {
        ctx->hid_ifaces[hid_handler].set_idle_cb = usbhid_dflt_set_idle;
        /* @ assert ctx->hid_ifaces[hid_handler].set_idle_cb ∈ {usbhid_dflt_set_idle} ;)*/
    }

    /* set interface as configured */
    ctx->hid_ifaces[hid_handler].configured = true;
    /*@ assert errcode==MBED_ERROR_NONE; */
    /*@ assert  errcode==MBED_ERROR_NONE ==> (hid_handler < usbhid_ctx.num_iface && get_report != NULL) ;*/

err:
    return errcode;
}
/*@ requires true;
  @
  @ behavior not_exist_invhandler:
  @    assumes !(hid_handler < usbhid_ctx.num_iface);
  @    assigns \nothing;
  @    ensures \result == MBED_ERROR_INVPARAM;

  @ behavior not_exist:
  @    assumes (hid_handler < usbhid_ctx.num_iface);
  @    assumes (usbhid_ctx.hid_ifaces[hid_handler].declared ≢ 0) != \true ;
  @    assigns \nothing;
  @    ensures \result == MBED_ERROR_INVPARAM;

  @ behavior exists:
  @    assumes (hid_handler < usbhid_ctx.num_iface);
  @    assumes (usbhid_ctx.hid_ifaces[hid_handler].declared ≢ 0) == \true ;
  @    assigns GHOST_opaque_drv_privates;
  @    ensures \result==MBED_ERROR_NONE;
  @
  @ complete behaviors;
  @ disjoint behaviors;
*/

mbed_error_t usbhid_response_done(uint8_t hid_handler)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!usbhid_interface_exists(hid_handler)) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    uint8_t epid = get_in_epid(&usbhid_ctx.hid_ifaces[hid_handler].iface);
    usb_backend_drv_send_zlp(epid);
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
    if (response_len == 0) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (!usbhid_interface_exists(hid_handler)) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /* first field is the report index */
    /* wait for previous data to be fully transmitted */
    /*@
      @ loop assigns data_being_sent ;
      */
    while (data_being_sent == true) {
        request_data_membarrier();
#ifdef __FRAMAC__
        /* asynchronous triggering must be simulate in Frama-C. Here we trigger
         * the flag syncrhonously */
        data_being_sent = false;
#endif
    }

    set_bool_with_membarrier(&data_being_sent, true);
    /* total size is report + report id (one byte) */
    uint8_t epid = get_in_epid(&usbhid_ctx.hid_ifaces[hid_handler].iface);
    log_printf("[USBHID] sending response on EP %d (len %d)\n", epid, response_len);

    errcode = usb_backend_drv_send_data(response, response_len, epid);
    if (errcode != MBED_ERROR_NONE) {
        goto err_send;
    }
    /* wait for end of transmission */
    /*@
      @ loop assigns data_being_sent ;
      */
    while (data_being_sent == true) {
        request_data_membarrier();
#ifdef __FRAMAC__
        /* asynchronous triggering must be simulate in Frama-C. Here we trigger
         * the flag syncrhonously */
        data_being_sent = false;
#endif
    }
err_send:
    /* TODO: is this line useful ? the trigger should have done the job */
    set_bool_with_membarrier(&data_being_sent, false);
err:
    return errcode;
}


mbed_error_t usbhid_send_report(uint8_t               hid_handler,
                                uint8_t const * const report,
                                usbhid_report_type_t  type,
                                uint8_t               report_index)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint16_t len = 0;
    if (report == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (!usbhid_interface_exists(hid_handler)) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /* first field is the report index */
    uint8_t buf[MAX_HID_REPORT_SIZE + 1] = { 0 };
    /* report, as report length, is transmit by the upper layer and as a consequence, is under the responsability
     * of it.
     * We assume that if report is a valid_read pointer, given report length is correct (i.e. smaller or equal to the
     * effective report buffer.
     */
    len = usbhid_get_report_len(hid_handler, type, report_index);
    if (len == 0 || len > MAX_HID_REPORT_SIZE) {
        log_printf("[USBHID] unable to get back report len for iface %d/idx %d\n", hid_handler, report_index);
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /*@ assert 0 < len <= MAX_HID_REPORT_SIZE ; */
    /* wait for previous data to be fully transmitted */
    /*@
      @ loop assigns data_being_sent ;
      */
    while (data_being_sent == true) {
        request_data_membarrier();
#ifdef __FRAMAC__
        /* asynchronous triggering must be simulate in Frama-C. Here we trigger
         * the flag syncrhonously */
        data_being_sent = false;
#endif
    }
    set_bool_with_membarrier(&data_being_sent, true);
    /* is a report id needed ? if a REPORT_ID is defined in the report descriptor, it is added,
     * otherwise, items are sent directly */
    uint8_t * dest_buf = NULL;
    bool requires_id = false;
    errcode = usbhid_report_needs_id(hid_handler, report_index, &requires_id);
    if (errcode != MBED_ERROR_NONE) {
        goto err;
    }

    if (requires_id) {
        buf[0] = usbhid_report_get_id(hid_handler, report_index);
        log_printf("[USBHID] this report requires its ID (0x%x) to be sent\n", buf[0]);
        dest_buf = &buf[1];
    } else {
        log_printf("[USBHID] sending report without ID\n");
        dest_buf = &buf[0];
    }
#ifndef __FRAMAC__
    memcpy(&dest_buf[0], report, len);
#else
    /*@
      @ loop invariant \separated(dest_buf + (0 .. len-1), report + (0 .. len-1));
      @ loop invariant 0 <= offset <= len;
      @ loop assigns offset, dest_buf[0 .. len-1];
      @ loop variant len - offset;
     */
    for (uint16_t offset = 0; offset < len; ++offset) {
        dest_buf[offset] = report[offset];
    }
#endif

    if (requires_id) {
        len += 1;
    }

    /* total size is report + report id (one byte) */
    uint8_t epid = get_in_epid(&usbhid_ctx.hid_ifaces[hid_handler].iface);
    log_printf("[USBHID] sending report on EP %d (len %d)\n", epid, len);

    usb_backend_drv_send_data(buf, len, epid);
    /* wait for end of transmission. This is a triggered loop. Frama-C can't guarantee
     * that this loop is finished using this vary implementation */
    /*@
      @ loop assigns data_being_sent ;
      */
    while (data_being_sent == true) {
        request_data_membarrier();
#ifdef __FRAMAC__
        /* asynchronous triggering must be simulate in Frama-C. Here we trigger
         * the flag syncrhonously */
        data_being_sent = false;
#endif
    }
    /* finishing with ZLP */
    usb_backend_drv_send_zlp(epid);
    /* TODO: is this line useful ? the trigger should have done the job */
    set_bool_with_membarrier(&data_being_sent, false);
err:
    return errcode;
}



bool usbhid_is_silence_requested(uint8_t hid_handler, uint8_t index)
{
    if (index >= MAX_HID_REPORTS) {
        return true;
    }
    if (hid_handler >= MAX_USBHID_IFACES) {
        return true;
    }
    if (usbhid_ctx.hid_ifaces[hid_handler].configured == false) {
        return true;
    }
    /*@ assert index < MAX_HID_REPORTS && hid_handler < MAX_USBHID_IFACES && usbhid_ctx.hid_ifaces[hid_handler].configured != \false ;*/
    /* when setting idle_ms to 0, silence is requested while no event arrise on the
     * corresponding report index */
    return usbhid_ctx.hid_ifaces[hid_handler].inep.silence[index];
}

/*@
  @ assigns \nothing ;

  @ behavior ugri_invalid_idx:
  @   assumes index >= MAX_HID_REPORTS;
  @   ensures \result == 0;

  @ behavior ugri_invalid_handler:
  @   assumes index < MAX_HID_REPORTS;
  @   assumes hid_handler >= MAX_USBHID_IFACES;
  @   ensures \result == 0;

  @ behavior ugri_unconfigured_iface:
  @   assumes index < MAX_HID_REPORTS;
  @   assumes hid_handler < MAX_USBHID_IFACES;
  @   assumes usbhid_ctx.hid_ifaces[hid_handler].configured == \false;
  @   ensures \result == 0;

  @ behavior ugri_ok:
  @   assumes index < MAX_HID_REPORTS;
  @   assumes hid_handler < MAX_USBHID_IFACES;
  @   assumes usbhid_ctx.hid_ifaces[hid_handler].configured == \true;
  @   ensures \result == usbhid_ctx.hid_ifaces[hid_handler].inep.idle_ms[index];

  @ complete behaviors;
  @ disjoint behaviors;

 */
uint16_t usbhid_get_requested_idle(uint8_t hid_handler, uint8_t index)
{
    if (index >= MAX_HID_REPORTS) {
        return 0;
    }

    if (hid_handler >= MAX_USBHID_IFACES) {
        return 0;
    }
    if (usbhid_ctx.hid_ifaces[hid_handler].configured == false) {
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

/* basics ACSL for now */

mbed_error_t usbhid_recv_report(uint8_t hid_handler __attribute__((unused)),
                                uint8_t *report,
                                uint16_t size)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t ep_id = 0;
    uint8_t ep;
    uint8_t iface = 0;
    /* get back EP identifier from HID handler */

    /*@ assert \valid(usbhid_ctx.hid_ifaces + (0 .. usbhid_ctx.num_iface - 1)) ; */
    /*@
      @ loop invariant 0 <= iface <= usbhid_ctx.num_iface ;
      @ loop assigns iface,ep;
      @ loop variant (usbhid_ctx.num_iface - iface) ;
      */
    for (iface = 0; iface < usbhid_ctx.num_iface; ++iface)
    {
        if (usbhid_ctx.hid_ifaces[iface].iface.usb_ep_number >= MAX_EP_PER_INTERFACE) {
            errcode = MBED_ERROR_INVPARAM;
            goto err;
        }
        /*@ assert \valid(usbhid_ctx.hid_ifaces[iface].iface.eps + (0 .. usbhid_ctx.hid_ifaces[iface].iface.usb_ep_number - 1)) ; */
        /*@
          @ loop invariant 0 <= ep <= usbhid_ctx.hid_ifaces[iface].iface.usb_ep_number ;
          @ loop assigns  ep;
          @ loop variant (usbhid_ctx.hid_ifaces[iface].iface.usb_ep_number - ep) ;
          */
        for (ep = 0; ep < usbhid_ctx.hid_ifaces[iface].iface.usb_ep_number; ++ep)
        {
            if (usbhid_ctx.hid_ifaces[iface].iface.eps[ep].dir == USB_EP_DIR_OUT || usbhid_ctx.hid_ifaces[iface].iface.eps[ep].dir == USB_EP_DIR_BOTH)
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
