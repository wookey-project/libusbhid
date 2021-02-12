/*
 *
 * Copyright 2018 The wookey project team <wookey@ssi.gouv.fr>
 *   - Ryad     Benadjila
 *   - Arnauld  Michelizza
 *   - Mathieu  Renard
 *   - Philippe Thierry
 *   - Philippe Trebuchet
 *
 * This package is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * ur option) any later version.
 *
 * This package is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this package; if not, write to the Free Software Foundation, Inc., 51
 * Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
 *
 */

#include "libc/types.h"
#include "autoconf.h"
#include "usbhid.h"
#include "usbhid_descriptor.h"
#include "usbhid_reports.h"
#include "usbhid_requests.h"


/* This is the HID class descriptor content. This descriptor is returned at GetConfiguration time.
 * Each other class-level descriptor (report descriptor and others) are returned to
 * GetDescriptor class level requests, handled by the class-level handler */
/*@
  @ requires \separated(buf + (0 .. sizeof(usbhid_descriptor_t)-1),desc_size) ;
  @ assigns buf[0 .. sizeof(usbhid_descriptor_t)-1] ;
  @ assigns *desc_size ;

  @behavior invparam:
  @   assumes (buf == NULL || desc_size == NULL) ;
  @   ensures \result == MBED_ERROR_INVPARAM ;

  @behavior invstate:
  @   assumes !(buf == NULL || desc_size == NULL) ;
  @   assumes usbhid_ctx.num_iface >= MAX_USBHID_IFACES || usbhid_ctx.num_iface == 0;
  @   requires \separated((uint8_t*)(buf +( 0 .. *desc_size)),desc_size) ;
  @   ensures \result == MBED_ERROR_INVSTATE ;

  @behavior noiface:
  @   assumes !(buf == NULL || desc_size == NULL) ;
  @   assumes !(usbhid_ctx.num_iface >= MAX_USBHID_IFACES || usbhid_ctx.num_iface == 0);
  @   assumes \forall integer i ; 0 <= i < usbhid_ctx.num_iface ==> usbhid_ctx.hid_ifaces[i].id != iface_id ;
  @   requires \separated((uint8_t*)(buf +( 0 .. *desc_size)),desc_size) ;
  @   ensures \result == MBED_ERROR_INVPARAM ;

  @behavior ok:
  @   assumes !(buf == NULL || desc_size == NULL) ;
  @   assumes !(usbhid_ctx.num_iface >= MAX_USBHID_IFACES || usbhid_ctx.num_iface == 0);
  @   assumes \exists integer i ; 0 <= i < usbhid_ctx.num_iface && usbhid_ctx.hid_ifaces[i].id == iface_id;
  @   requires \separated((uint8_t*)(buf +( 0 .. *desc_size)),desc_size) ;
  @   ensures \result == MBED_ERROR_NOMEM || \result == MBED_ERROR_NONE || \result == MBED_ERROR_INVPARAM || \result == MBED_ERROR_NOSTORAGE || \result == MBED_ERROR_INVSTATE;

  @ complete behaviors ;
  @ disjoint behaviors ;

 */
mbed_error_t      usbhid_get_descriptor(uint8_t             iface_id,
                                        uint8_t            *buf,
                                        uint8_t            *desc_size,
                                        uint32_t            usbdci_handler __attribute__((unused)))
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbhid_context_t *ctx = usbhid_get_context();
    /* sanitation */
    if (buf == NULL || desc_size == NULL) {
        log_printf("[USBHID] invalid param buffers\n");
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
     if (ctx->num_iface >= MAX_USBHID_IFACES || ctx->num_iface == 0) {
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /*@ assert ctx->num_iface < MAX_USBHID_IFACES; */

    /* desc size is usbhid_descriptor_t size plus usbhid_content_descriptor_t size
     * for each additional optional content descriptor (report descriptor is requested) */
    uint32_t size = 0;
    uint8_t i;
    /* descriptor number is a per-interface information. We get back the iface based on the
     * identifier passed by libxDCI */

    /*@ assert \valid(ctx->hid_ifaces + (0 .. ctx->num_iface - 1)) ; */
    /* @ assert \valid_read(*desc_size) ; */
    /*@
      @ loop invariant 0 <= i <= ctx->num_iface ;
      @ loop assigns i ;
      @ loop variant (ctx->num_iface - i) ;
      */
    for (i = 0; i < ctx->num_iface; ++i) {
        if (ctx->hid_ifaces[i].id == iface_id) {
            size = sizeof(usbhid_descriptor_t) + (ctx->hid_ifaces[i].num_descriptors * sizeof (usbhid_content_descriptor_t));
            if (*desc_size < size) {
                log_printf("[USBHID] invalid param buffers\n");
                errcode = MBED_ERROR_NOMEM;
                goto err;
            }
            break;
        }
    }
    if (i >= ctx->num_iface) {
        log_printf("[USBHID] iface not found\n");
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /* @ assert i < ctx->num_iface ; */
    /* @ assert i < MAX_USBHID_IFACES ; */

    /* @ assert ctx->hid_ifaces[i].num_descriptors < MAX_HID_DESCRIPTORS; */
    const uint8_t num_desc = ctx->hid_ifaces[i].num_descriptors;

    usbhid_descriptor_t * const desc =
        (usbhid_descriptor_t *)(&buf[0]);
    desc->bLength = size; /* HID descriptor size */
    desc->bDescriptorType = HID_DESCRIPTOR_TYPE; /* HID descriptor type, set by USB consortium */
    desc->bcdHID = 0x111; /* HID class specification release 1.11 */
    desc->bCountryCode = 0;  /* contry code : 0x0 = not supported */
    desc->bNumDescriptors = num_desc; /* number of class descriptor, including report descriptor (at least one) */

    uint8_t descid = 0;
    /*@
      @ loop invariant 0 <= descid <= num_desc ;
      @ loop assigns descid, buf[0 .. sizeof(usbhid_descriptor_t)-1], errcode;
      @ loop assigns desc->descriptors[0..(num_desc-1)].bDescriptorType ;
      @ loop assigns desc->descriptors[0..(num_desc-1)].wDescriptorLength ;
      @ loop variant (num_desc - descid) ;
      */
    for (descid = 0; descid < num_desc; ++descid) {
        desc->descriptors[descid].bDescriptorType = REPORT_DESCRIPTOR_TYPE;
        uint8_t len = 0;
        errcode = usbhid_get_report_desc_len(i, descid, &len);
        if (errcode != MBED_ERROR_NONE) {
            goto err;
        }
        desc->descriptors[descid].wDescriptorLength = len;
    }
    *desc_size = size;
err:
    return errcode;
}
