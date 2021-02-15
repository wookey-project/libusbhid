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
#include "usbhid_reports.h"
#include "autoconf.h"

/* USBHID class specific request (i.e. bRequestType is Type (bit 5..6 = 1, bits 0..4 target current iface
 * These values are set in bRequest field */
#define USB_STD_RQST_ACTION_GET_DESCRIPTOR 0x06
#define USB_STD_RQST_ACTION_SET_DESCRIPTOR 0x07

/* USBHID Get_Descriptor standard request targetting current interface.
 * These values are set in wValue high byte, when request is *not* class specific */
#define DESCRIPTOR_TYPE_HID             0x21
#define DESCRIPTOR_TYPE_REPORT          0x22
#define DESCRIPTOR_TYPE_PHYSICAL        0x23

#ifndef __FRAMAC__
/*
 * weak trigger, to be replaced by upper stack trigger implementation at link time
 */
__attribute__((weak)) mbed_error_t usbhid_request_trigger(uint8_t hid_handler __attribute__((unused)),
                                                          uint8_t hid_req __attribute__((unused)))
{
    return MBED_ERROR_NONE;
}
#endif

/*
 * TODO: behaviors
 */
/*@
  @ requires \valid(it_does);
  @ assigns *it_does;

  // full functional
  @ behavior invhandler:
  @    assumes hid_handler >= MAX_USBHID_IFACES;
  @    ensures \result == MBED_ERROR_INVPARAM;

  @ behavior inv_handler_state:
  @    assumes hid_handler < MAX_USBHID_IFACES;
  @    assumes usbhid_ctx.hid_ifaces[hid_handler].configured == \false;
  @    ensures \result == MBED_ERROR_INVSTATE;

  @ behavior inv_handler_content:
  @    assumes hid_handler < MAX_USBHID_IFACES;
  @    assumes usbhid_ctx.hid_ifaces[hid_handler].configured == \true;
  @    assumes usbhid_ctx.hid_ifaces[hid_handler].iface.usb_ep_number >= MAX_EP_PER_INTERFACE;
  @    ensures \result == MBED_ERROR_UNKNOWN;

  @ behavior ok:
  @    assumes hid_handler < MAX_USBHID_IFACES;
  @    assumes usbhid_ctx.hid_ifaces[hid_handler].configured == \true;
  @    assumes usbhid_ctx.hid_ifaces[hid_handler].iface.usb_ep_number < MAX_EP_PER_INTERFACE;
  @    ensures *it_does == \true ==> \exists integer i; 0 <= i < usbhid_ctx.hid_ifaces[hid_handler].iface.usb_ep_number && usbhid_ctx.hid_ifaces[hid_handler].iface.eps[i].dir == USB_EP_DIR_OUT;
  @    ensures *it_does == \false ==> (\forall integer j; 0 <= j < usbhid_ctx.hid_ifaces[hid_handler].iface.usb_ep_number ==> usbhid_ctx.hid_ifaces[hid_handler].iface.eps[j].dir != USB_EP_DIR_OUT);
  @    ensures \result == MBED_ERROR_NONE;

 */
#ifndef __FRAMAC__
static inline
#endif
mbed_error_t is_iface_using_out_ep(uint8_t hid_handler, bool *it_does)
{
    /* ctx checked by parent function */
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbhid_context_t *ctx = usbhid_get_context();
    bool result = false;

    if (hid_handler >= MAX_USBHID_IFACES) {
        /* in the current call context, never reached, thus fault injection
         * protection. */
        /*@ assert \false; */
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (usbhid_interface_configured(hid_handler) == false) {
        /* interface not configured (hould not happen, but can be emulated. This
         * is a fault injection case too) */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    if (ctx->hid_ifaces[hid_handler].iface.usb_ep_number >= MAX_EP_PER_INTERFACE) {
        /* current iface config is invalid, this should not happen
         * (fault injection?) */
        errcode = MBED_ERROR_UNKNOWN;
        goto err;
    }
    /*@
      @ loop invariant 0 <= j <= ctx->hid_ifaces[hid_handler].iface.usb_ep_number ;
      @ loop assigns j, result;
      @ loop variant (ctx->hid_ifaces[hid_handler].iface.usb_ep_number - j);
      */
    for (uint8_t j = 0; j < ctx->hid_ifaces[hid_handler].iface.usb_ep_number; ++j) {
        if (ctx->hid_ifaces[hid_handler].iface.eps[j].dir == USB_EP_DIR_OUT) {
            result = true;
            /* helping wp with eva */
            /*@  assert \exists integer i; 0 <= i < usbhid_ctx.hid_ifaces[hid_handler].iface.usb_ep_number && usbhid_ctx.hid_ifaces[hid_handler].iface.eps[i].dir == USB_EP_DIR_OUT; */
            goto err;
        }
    }
    result = false;
    /*@ assert \forall integer j; 0 <= j < usbhid_ctx.hid_ifaces[hid_handler].iface.usb_ep_number ==> usbhid_ctx.hid_ifaces[hid_handler].iface.eps[j].dir != USB_EP_DIR_OUT; */

err:
    *it_does = result;
    return errcode;
}


/*@
  @ requires \valid(hid_handler);
  @   assigns *hid_handler;

  @ behavior inviface:
  @   assumes !(\exists integer i; 0 <= i < usbhid_ctx.num_iface && usbhid_ctx.hid_ifaces[i].iface.id == iface) ;
  @   ensures \result == MBED_ERROR_INVPARAM;

  // we can't consider this as two behavior as usbhid_ctx.hid_ifaces[] is not a program input data but a global
  // separating into two behaviors would fail the disjoint property
  @ behavior ok:
  @   assumes (\exists integer i; 0 <= i < usbhid_ctx.num_iface && usbhid_ctx.hid_ifaces[i].iface.id == iface) ;
  @   ensures \result == MBED_ERROR_INVSTATE ==> \exists integer i; 0 <= i < usbhid_ctx.num_iface && usbhid_ctx.hid_ifaces[i].iface.id == iface && usbhid_ctx.hid_ifaces[i].configured == \false;
  @   ensures \result == MBED_ERROR_NONE ==> \exists integer i; 0 <= i < usbhid_ctx.num_iface && usbhid_ctx.hid_ifaces[i].iface.id == iface && usbhid_ctx.hid_ifaces[i].configured == \true;

  @ disjoint behaviors;
  @ complete behaviors;
 */
/*
 * This function is used in HID requests. We assumes that request should be executed
 * only if the associated interface is declared and configured.
 */
#ifndef __FRAMAC__
static inline
#endif
mbed_error_t get_hid_handler_from_iface(uint8_t iface, uint8_t *hid_handler)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* ctx checked by parent function */
    usbhid_context_t *ctx = usbhid_get_context();

    uint8_t handler = 0;
    uint8_t num_iface = ctx->num_iface;
    bool handler_found = false;
    /*@
      @ loop invariant 0 <= i <= num_iface ;
      @ loop assigns i, handler, handler_found ;
      @ loop variant num_iface - i;
      */
    for (uint8_t i = 0; i < num_iface; ++i) {
        if (ctx->hid_ifaces[i].iface.id == iface) {
            handler = i;
            handler_found = true;
            /*@ assert (\exists integer j; 0 <= i < usbhid_ctx.num_iface && usbhid_ctx.hid_ifaces[j].iface.id == iface && j == i); */
            break;
        }
    }
    if (handler_found == false) {
        /* iface not found */
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (!usbhid_interface_configured(handler)) {
        /* iface found, but not configured */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    *hid_handler = handler;
err:
    return errcode;
}


/*@
  @ requires \valid_read(pkt);
  @ requires \separated(pkt,&usbhid_ctx);
  @ assigns usbhid_ctx.hid_ifaces[0 .. MAX_USBHID_IFACES-1].protocol;

 // let's handle functional proof (usbhid conformity)
 // Set_Proto, usb_hid 1.11, chap 7.2.6
 // Info: bmRequestType & bRequest has been checked by caller

 // value should be 0 (Boot Protocol) or 1 (Report Protocol)
 @ behavior bad_wValue:
 @   assumes pkt->wValue != 0 && pkt->wValue != 1;
 @   ensures \result == MBED_ERROR_UNSUPORTED_CMD;

 // wLength (data size) should be 0)
 @ behavior bad_wLength:
 @   assumes pkt->wValue == 0 || pkt->wValue == 1;
 @   assumes pkt->wLength != 0;
 @   ensures \result == MBED_ERROR_UNSUPORTED_CMD;

 // wIndex: interface identifier
 @ behavior bad_wIndex_hbyte:
 @   assumes pkt->wValue == 0 || pkt->wValue == 1;
 @   assumes pkt->wLength == 0;
 @   assumes ((pkt->wIndex >> 8) & 0xff) != 0;
 @   ensures \result == MBED_ERROR_UNSUPORTED_CMD;

 // input (setup pkt) ok. Let's check current context
 @ behavior input_ok:
 @   assumes pkt->wValue == 0 || pkt->wValue == 1;
 @   assumes pkt->wLength == 0;
 @   assumes ((pkt->wIndex >> 8) & 0xff) == 0;
 @   ensures !(\exists integer j; 0 <= j < usbhid_ctx.num_iface &&
         usbhid_ctx.hid_ifaces[j].iface.id == (pkt->wIndex & 0xff) && usbhid_ctx.hid_ifaces[j].configured == \true) ==> \result != MBED_ERROR_NONE;
 @   ensures (\forall integer j; 0 <= j < usbhid_ctx.num_iface ==>
         !(usbhid_ctx.hid_ifaces[j].iface.id != (pkt->wIndex & 0xff) && usbhid_ctx.hid_ifaces[j].configured == \true &&
           usbhid_ctx.hid_ifaces[j].iface.usb_subclass == USBHID_SUBCLASS_BOOT_IFACE)) ==> \result != MBED_ERROR_NONE;
 @   ensures !(\forall integer j; 0 <= j < usbhid_ctx.num_iface ==>
         !(usbhid_ctx.hid_ifaces[j].iface.id == (pkt->wIndex & 0xff) && usbhid_ctx.hid_ifaces[j].configured == \true &&
           usbhid_ctx.hid_ifaces[j].iface.usb_subclass == USBHID_SUBCLASS_BOOT_IFACE)) ==> \result == MBED_ERROR_NONE;

 @ complete behaviors;
 @ disjoint behaviors;
 */
#ifndef __FRAMAC__
/* export needed to be triggered in EVA entrypoint */
static
#endif
mbed_error_t usbhid_handle_set_protocol(usbctrl_setup_pkt_t *pkt)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbhid_context_t *ctx = usbhid_get_context();
    if (ctx == NULL) {
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    uint16_t proto = pkt->wValue;
    if (proto != 0 && proto != 1) {
        errcode = MBED_ERROR_UNSUPORTED_CMD;
        goto err;
    }
    if (pkt->wLength != 0) {
        /* should be zero, as defined in the standard */
        errcode = MBED_ERROR_UNSUPORTED_CMD;
        goto err;
    }
    uint8_t wIndex_hbyte = (pkt->wIndex >> 8) & 0xff;
    if (wIndex_hbyte != 0x0) {
        log_printf("[USBHID] wIndex should handle iface id only (hid 1.11, 7.2.6)\n");
        errcode = MBED_ERROR_UNSUPORTED_CMD;
        goto err;
    }
    uint8_t iface = pkt->wIndex & 0xff;
    uint8_t hid_handler;
    errcode = get_hid_handler_from_iface(iface, &hid_handler);
    if (errcode != MBED_ERROR_NONE) {
         /*  assert !(\exists integer j; 0 <= j < usbhid_ctx.num_iface &&
            (usbhid_ctx.hid_ifaces[j].iface.id == iface && usbhid_ctx.hid_ifaces[j].configured == \true)); */
        goto err;
    }
    /*@ assert \exists integer j; 0 <= j < usbhid_ctx.num_iface &&
         (usbhid_ctx.hid_ifaces[j].iface.id == iface && usbhid_ctx.hid_ifaces[j].configured == \true); */
    /*@ assert hid_handler < usbhid_ctx.num_iface; */
    /*@ assert usbhid_ctx.hid_ifaces[hid_handler].iface.id == iface; */
    /*@ assert usbhid_ctx.hid_ifaces[hid_handler].configured == \true; */

    /* iface **must** be declared in the boot subclass */
    if (ctx->hid_ifaces[hid_handler].iface.usb_subclass != USBHID_SUBCLASS_BOOT_IFACE) {
        /* SetProtocol is only for boot interfaces (typically keyboards) */
        errcode = MBED_ERROR_UNSUPORTED_CMD;
        goto err;
    }
    /*@ assert usbhid_ctx.hid_ifaces[hid_handler].iface.usb_subclass == USBHID_SUBCLASS_BOOT_IFACE; */
    switch (proto) {
        case 0:
            log_printf("[USBHID] requesting boot protocol on iface %d\n", iface);
            ctx->hid_ifaces[hid_handler].protocol = USBHID_PROTO_BOOT;
            break;
        case 1:
            log_printf("[USBHID] requesting report protocol on iface %d\n", iface);
            ctx->hid_ifaces[hid_handler].protocol = USBHID_PROTO_REPORT;
            break;
        default:
            /* dead code, fault resilient, required as default fallback for compiler */
            /*@ assert \false; */
            errcode = MBED_ERROR_UNSUPORTED_CMD;
            goto err;
    }
    /* trigger upper layer that SetProtocol has been received */
    usbhid_request_trigger(hid_handler, USB_CLASS_RQST_SET_PROTOCOL);
    /*@ assert errcode == MBED_ERROR_NONE; */
err:
    return errcode;
}

#ifndef __FRAMAC__
static
#endif
mbed_error_t usbhid_handle_set_idle(usbctrl_setup_pkt_t *pkt)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbhid_context_t *ctx = usbhid_get_context();
    if (ctx == NULL) {
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    uint16_t idle_ms = 0;
    uint16_t wvalue = pkt->wValue;
    uint8_t hbyte = ((wvalue >> 4) & 0xff);
    /* lbyte: HID descriptor identifier */
    uint8_t lbyte = wvalue & 0xff;

    uint8_t iface = pkt->wIndex & 0xff;
    uint8_t hid_handler;

    errcode = get_hid_handler_from_iface(iface, &hid_handler);
    if (errcode != MBED_ERROR_NONE) {
        goto err;
    }

    if (hbyte == 0) {
        /* duration_ms to 0, no limit to IDLE time, do not send */
        idle_ms = 0;
    } else {
        /* duration in ms */
        idle_ms = hbyte * 4;
    }
    if (lbyte == 0) {
        /* applicable to all reports */
        for (uint8_t i = 0; i < MAX_HID_REPORTS; ++i) {
            ctx->hid_ifaces[hid_handler].inep.idle_ms[i] = idle_ms;
            if (idle_ms == 0) {
                ctx->hid_ifaces[hid_handler].inep.silence[i] = true;
            }
        }
    } else if (lbyte >= MAX_HID_REPORTS) {
        /* invalid report targeted! */
        log_printf("[USBHID] invalid report %d targetted by setup packet!\n", lbyte);
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    } else {
        /* applicable to report given by lbyte only */
        ctx->hid_ifaces[hid_handler].inep.idle_ms[lbyte] = idle_ms;
        if (idle_ms == 0) {
            ctx->hid_ifaces[hid_handler].inep.silence[lbyte] = true;
        }
    }
    usbhid_request_trigger(hid_handler, USB_CLASS_RQST_SET_IDLE);
err:
    return errcode;
}


#ifndef __FRAMAC__
static
#endif
mbed_error_t usbhid_handle_std_request(usbctrl_setup_pkt_t *pkt)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* get the high byte */
    uint8_t maxlen = pkt->wLength & 0xff;
    uint8_t action = pkt->bRequest;
    uint8_t descriptor_type = pkt->wValue >> 0x8;
    uint8_t descriptor_index = pkt->wValue & 0xff;
    usbhid_context_t *ctx = usbhid_get_context();
    if (ctx == NULL) {
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    if (descriptor_index >= MAX_HID_REPORTS) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
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

                    /* get back hid iface handler from targetted iface */
                    uint8_t iface = pkt->wIndex & 0xff;
                    uint8_t hid_handler;

                    errcode = get_hid_handler_from_iface(iface, &hid_handler);
                    if (errcode != MBED_ERROR_NONE) {
                        goto err;
                    }
                    /* forge the descriptor */
                    usbhid_forge_report_descriptor(hid_handler, &desc[0], &size, descriptor_index);
                    log_printf("[USBHID] written %d byte in descriptor\n", size);
                    /* now, offset define the collection size, desc handle it, we can send it */
                    /*1. configure descriptor */
                    /*2. send data */
                    usb_backend_drv_send_data(&(desc[0]), maxlen >= size ? size : maxlen, EP0);
//                    usb_backend_drv_ack(1, USB_BACKEND_DRV_EP_DIR_OUT);
                    usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
                    /* this is a new event on descriptor_index, cleaning silence request */
                    ctx->hid_ifaces[hid_handler].inep.silence[descriptor_index] = false;

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

#ifndef __FRAMAC__
static
#endif
mbed_error_t usbhid_handle_class_request(usbctrl_setup_pkt_t *pkt)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbhid_context_t *ctx = usbhid_get_context();
    if (ctx == NULL) {
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    uint8_t iface = pkt->wIndex & 0xff;

    uint8_t action = pkt->bRequest;
    switch (action) {
        case USB_CLASS_RQST_GET_REPORT:
            log_printf("[USBHID] Get_Report class request (TODO)\n");
            /*TODO*/
            break;
        case USB_CLASS_RQST_GET_IDLE:
            log_printf("[USBHID] Get_Idle class request (TODO)\n");
            /*TODO*/
            break;
        case USB_CLASS_RQST_GET_PROTOCOL:
            log_printf("[USBHID] Get_Protocol class request (TODO)\n");
            /*TODO*/
            break;
        case USB_CLASS_RQST_SET_REPORT:
            log_printf("[USBHID] Set_Report class request (TODO)\n");
            /* receiving report on EP0 (when no EP OUT declared) */

            uint8_t hid_handler;
            if ((errcode = get_hid_handler_from_iface(iface, &hid_handler)) != MBED_ERROR_NONE) {
                goto err;
            }
            bool iface_using_outep = false;

            if ((errcode = is_iface_using_out_ep(hid_handler, &iface_using_outep)) != MBED_ERROR_NONE) {
                goto err;
            }
            if (iface_using_outep == true) {
                log_printf("[USBHID] iface %d is using OUT EP, Set_Report class request should not be received!\n", iface);
                /* Set_Report is replaced by sending report directly to OUT EP */
                usb_backend_drv_stall(0, USB_BACKEND_DRV_EP_DIR_OUT);
            } else {
                /* TODO: pass received report to upper stack */
                /* 1. get back report content */
                /* 2. push it to the upper stack */
                /* 3. and acknowledge */
                usb_backend_drv_send_zlp(0);
            }
            break;
        case USB_CLASS_RQST_SET_IDLE:
            usbhid_handle_set_idle(pkt);
            /* acknowledge SET IDLE */
            usb_backend_drv_send_zlp(0);
            break;
        case USB_CLASS_RQST_SET_PROTOCOL:
            log_printf("[USBHID] Set_Protocol class request (TODO)\n");
            /*TODO*/
            break;
        default:
            log_printf("[USBHID] Ubsupported class request action %x", action);
    }
err:
    return errcode;
}


/**
 * \brief Class request handling
 *
 * There is two ways requests can be received at this level:
 * through a class level request:
 *  - the bmRequestType class bit is set to 1, indicating that the request is targetting
 *    the current class. In this first case, all the HID requests are possible.
 * through a standard request, targeting one of our (HID) interfaces.
 *  - in that case, the setup packet respect the USB standard, and two USB requests
 *    can target the HID level: Get_Descriptor() and Set_Descriptor().
 *
 * The below function discriminate the way request is passed to HID level, and calls the
 * appropriate handler.
 *
 * @param packet Setup packet
 */
mbed_error_t usbhid_class_rqst_handler(uint32_t usbxdci_handler __attribute__((unused)),
                                       usbctrl_setup_pkt_t *packet)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    log_printf("[classRqst] handling HID rqst\n");
    if (((packet->bmRequestType >> 5) & 0x3) == 1) {
        /* class request */
        log_printf("[classRqst] handling HID class rqst\n");
        errcode = usbhid_handle_class_request(packet);
    } else {
        /* standard request targetting current iface */
        log_printf("[classRqst] handling HID std rqst\n");
        errcode = usbhid_handle_std_request(packet);
    }
    return errcode;
}


