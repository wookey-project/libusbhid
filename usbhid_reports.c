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
#include "libc/types.h"
#include "libc/stdio.h"
#include "usbhid.h"
#include "usbhid_descriptor.h"
#include "autoconf.h"
#ifdef __FRAMAC__
#include "framac/entrypoint.h"
#endif

#define USBHID_STD_ITEM_LEN             4

mbed_error_t usbhid_report_needs_id(uint8_t hid_handler, uint8_t index, bool *id_needed)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbhid_context_t *ctx = usbhid_get_context();
    /*@ assert ctx != \null; */
    /* sanitize */
    if (!usbhid_interface_exists(hid_handler)) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (ctx->hid_ifaces[hid_handler].configured == false) {
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /*@ assert ctx->hid_ifaces[hid_handler].get_report_cb  ; */
    usbhid_report_infos_t *report;

    /*@ assert ctx->hid_ifaces[hid_handler].get_report_cb \in {&oneidx_get_report_cb,  &twoidx_get_report_cb} ;*/
    /*@ calls oneidx_get_report_cb, twoidx_get_report_cb ; */
    report = ctx->hid_ifaces[hid_handler].get_report_cb(hid_handler, index);
    if (report == NULL) {
        errcode = MBED_ERROR_NOBACKEND;
        goto err;
    }
    /* INFO: for the needs of the proof, two HID descriptors have been defined in the entrypoint.
     * These descriptors have different reports number & size that can be sent back by the device and
     * are associated two HID descriptor index 0 & 1.
     */
    /*@ assert (report == &report_oneindex || report ==  &report_twoindex); */
    /*@
      @ loop invariant 0 <= iterator <= report->num_items ;
      @ loop invariant \forall integer prei; 0<= prei<iterator ==> !(report->items[prei].type == USBHID_ITEM_TYPE_GLOBAL && report->items[prei].tag == USBHID_ITEM_GLOBAL_TAG_REPORT_ID);
      @ loop assigns iterator;
      @ loop variant report->num_items - iterator ;
      */
    for (uint32_t iterator = 0; iterator < report->num_items; ++iterator) {
        if (report->items[iterator].type == USBHID_ITEM_TYPE_GLOBAL &&
            report->items[iterator].tag == USBHID_ITEM_GLOBAL_TAG_REPORT_ID) {
            /*  assert (index == 0 ==> (\exists integer i; 0 <= i < ONEINDEX_ITEMS_NUM && (report_oneindex.items[i].type == USBHID_ITEM_TYPE_GLOBAL && report_oneindex.items[i].tag == USBHID_ITEM_GLOBAL_TAG_REPORT_ID))); */
            /*  assert (index == 1 ==> (\exists integer i; 0 <= i < TWOINDEX_ITEMS_NUM && (report_twoindex.items[i].type == USBHID_ITEM_TYPE_GLOBAL && report_twoindex.items[i].tag == USBHID_ITEM_GLOBAL_TAG_REPORT_ID))); */
            *id_needed = true;
            goto err;
        }
    }
    /* tag not found */
    *id_needed = false;
err:
    return errcode;
}


mbed_error_t usbhid_report_get_id(uint8_t hid_handler, uint8_t index, uint8_t *id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbhid_context_t *ctx = usbhid_get_context();

    /* sanitize */
    if (!usbhid_interface_exists(hid_handler)) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (ctx->hid_ifaces[hid_handler].configured == false) {
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }

    usbhid_report_infos_t *report;
    /*@ assert ctx->hid_ifaces[hid_handler].get_report_cb \in {&twoidx_get_report_cb} ;*/
    /*@ calls twoidx_get_report_cb ; */
    report  = ctx->hid_ifaces[hid_handler].get_report_cb(hid_handler, index);
    if (report == NULL) {
        errcode = MBED_ERROR_NOBACKEND;
        goto err;
    }
    /*@ assert \valid_read(report); */

    uint8_t found_id = 0;
    /*@
      @ loop invariant 0 <= iterator <= report->num_items ;
      @ loop assigns iterator, found_id ;
      @ loop variant report->num_items - iterator ;
      */
    for (uint32_t iterator = 0; iterator < report->num_items; ++iterator) {
        if (report->items[iterator].type == USBHID_ITEM_TYPE_GLOBAL &&
            report->items[iterator].tag == USBHID_ITEM_GLOBAL_TAG_REPORT_ID) {
            found_id = report->items[iterator].data1;
            goto err;
        }
    }
    /* tag not found, falling back to id 0 */
    *id = found_id;
err:
    return errcode;
}


uint16_t usbhid_get_report_len(uint8_t hid_handler, usbhid_report_type_t type, uint8_t index)
{

    mbed_error_t errcode = MBED_ERROR_NONE;
    usbhid_context_t *ctx = usbhid_get_context();
    uint32_t report_len = 0;

    /* sanitize */
    if (!usbhid_interface_exists(hid_handler)) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (hid_handler >= MAX_USBHID_IFACES) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (!ctx->hid_ifaces[hid_handler].get_report_cb) {
        goto err;
    }
    /*@ assert ctx->hid_ifaces[hid_handler].get_report_cb != \null ;*/


    usbhid_report_infos_t *report;
    /*@ assert ctx->hid_ifaces[hid_handler].get_report_cb \in {&oneidx_get_report_cb,  &twoidx_get_report_cb} ;*/
    /*@ calls oneidx_get_report_cb, twoidx_get_report_cb ; */
    report = ctx->hid_ifaces[hid_handler].get_report_cb(hid_handler, index);

    if (report == NULL) {
        goto err;
    }
    uint8_t report_size = 0;
    uint8_t report_count = 0;
    log_printf("[USBHID] get report length for HID report type %x\n", type);
    /* The report len defines the length (in bits in USB HID 1.11) of
     * the data sent after the report identifier.
     * This length is based of the number of data, multiplied by the size
     * of each of them.
     *
     * for a given descriptor identifier, even if there is multiple
     * input/output/features with multiple REPORT_SIZE and REPORT_COUNT, these field
     * are handled by (count/size) pairs. If multiple collections handle
     * different REPORT_SIZE/REPORT_COUNT pairs, they are separated by
     * a global INPUT/OUTPUT or FEATURE main item.
     * Here, we use these three items as separator for each SIZE/COUNT report
     * pairs, to calculate the global report size, which is the
     * addition of earch local report size/count.
     * if main item doesn't update one of the report count or size, we consider
     * the previous one as valid, as it is a global item.
     * TODO: there is a constraint here: MAIN items (INPUT, OUTPUT, FEATURE) must
     * be declared *after* their specifications (report size, count, logical values
     * and so on)
     */
    uint32_t local_report_len = 0;
    uint32_t iterator = 0;
    /*@
      @ loop invariant 0 <= iterator <= report->num_items ;
      @ loop invariant \valid(report->items + (0 .. (report->num_items -1)));
      @ loop assigns iterator,report_count, report_size, local_report_len, report_len ;
      @ loop variant (report->num_items - iterator);
      */
    for (iterator = 0; iterator < report->num_items; ++iterator) {
        if (report->items[iterator].type == USBHID_ITEM_TYPE_GLOBAL &&
            report->items[iterator].tag == USBHID_ITEM_GLOBAL_TAG_REPORT_SIZE) {
            report_size = report->items[iterator].data1;
            log_printf("[USBHID] found report size %d\n", report_size);
        }
        if (report->items[iterator].type == USBHID_ITEM_TYPE_GLOBAL &&
            report->items[iterator].tag == USBHID_ITEM_GLOBAL_TAG_REPORT_COUNT) {
            report_count = report->items[iterator].data1;
            log_printf("[USBHID] found report count %d\n", report_count);
        }
        /* add current report size to global report size only if it match the
         * report type that is to be sent */
        if (report->items[iterator].type ==USBHID_ITEM_TYPE_MAIN &&
            report->items[iterator].tag == type) {
            log_printf("[USBHID] current report type matches. Add its size\n");
            /* report len, in bits */
            local_report_len = report_size * report_count;
            log_printf("[USBHID] current report size in bits: %d\n", local_report_len);
            /* padd to upper byte size  */
            if (local_report_len % 8) {
                local_report_len += (8 - (local_report_len % 8));
            }
            /* ... going back to byte size */
            local_report_len = local_report_len / 8;
            log_printf("[USBHID] current report size in bbytes: %d\n", local_report_len);
            /* add local MAIN item report size to current global report size */
            /* local overflow detection */
            uint32_t local_total = 0;
            local_total = report_len + local_report_len;
            if (local_total > MAX_HID_REPORT_SIZE) {
                log_printf("[USBHID] current report size is bigger than max report size!\n");
                report_len = 0;
                goto err;
            }
            report_len += local_report_len;
            /*@ assert 0 <= report_len <= MAX_HID_REPORT_SIZE; */
        }
    }
err:
    /*@ assert 0 <= report_len <= MAX_HID_REPORT_SIZE; */
    return report_len;
}


uint8_t usbhid_get_report_desc_len(uint8_t hid_handler, uint8_t index, __out uint8_t *len)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint32_t offset = 0;
    usbhid_context_t *ctx = usbhid_get_context();

    /* sanitize */
    if (!usbhid_interface_exists(hid_handler)) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /* TODO: add usbhid_interface_configured() */



    if (ctx->hid_ifaces[hid_handler].get_report_cb == NULL) {
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /*@ assert ctx->hid_ifaces[hid_handler].get_report_cb != NULL; */

    usbhid_report_infos_t *report ;
    /*@ assert ctx->hid_ifaces[hid_handler].get_report_cb \in {&oneidx_get_report_cb} ;*/
    /*@ calls oneidx_get_report_cb ; */
    report = ctx->hid_ifaces[hid_handler].get_report_cb(hid_handler, index);


    if (report == NULL) {
        errcode = MBED_ERROR_NOSTORAGE;
        goto err;
    }

    /*@
      @ loop invariant 0 <= iterator <= report->num_items ;
      @ loop assigns offset, iterator ;
      @ loop variant report->num_items - iterator ;
      */
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
        }
    }
    if (offset > 255) {
        /* descriptor size is encoded in 8bits field in the HID descriptor
         * (USB 2.0 standard) and can't be bigger than 255 bytes */
        log_printf("[USBHID] invalid descriptor size: %d!\n", offset);
        offset = 0;
    }
    *len = offset;
err:
    return errcode;
}

/*@
  @ requires \valid_read(item_info);
  @ requires \valid(buf + (0 .. sizeof(usbhid_short_item_t)-1));
  @ requires \valid(offset);
  @ assigns buf[0 .. sizeof(usbhid_short_item_t)-1], *offset;
*/
#ifndef __FRAMAC__
static inline
#endif
mbed_error_t set_short_item(usbhid_item_info_t const * const item_info, uint8_t *buf, uint32_t *offset)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    union short_item {
        uint8_t             buf[3];
        usbhid_short_item_t item;
    };
    union short_item si;
    usbhid_short_item_t *item = &si.item;

        item->bSize =  item_info->size;
        item->bType =  item_info->type;
        item->bTag =  item_info->tag;
        /* done for first byte, copy to buff */
        buf[0] = si.buf[0];

        if (item_info->size == 0) {
            *offset += 1;
        } else if (item_info->size == 1) {
            item->data1 =  item_info->data1;
            buf[1] = si.buf[1];
            *offset += 2;
        } else if (item_info->size == 2) {
            item->data1 =  item_info->data1;
            item->data2 =  item_info->data2;
            buf[1] = si.buf[1];
            buf[2] = si.buf[2];
            *offset += 3;
        } else {
            log_printf("[USBHID] invalid item size %d!\n", item_info->size);
            errcode = MBED_ERROR_INVPARAM;
            goto err;
        }
err:
        return errcode;
}


mbed_error_t usbhid_forge_report_descriptor(uint8_t hid_handler, uint8_t *buf, uint32_t *bufsize, uint8_t index)
{
    log_printf("[USBHID] forging report descriptor\n");
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbhid_context_t *ctx = usbhid_get_context();
    /* sanitize */
    if (!usbhid_interface_exists(hid_handler)) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    /* TODO: add usbhid_interface_configured() */
    if (ctx->hid_ifaces[hid_handler].get_report_cb == NULL) {
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }

    /* define a buffer of num_items x max item size
     * these informations should be rodata content, defining the number of
     * item of collections and reports, specific to each upper stack profile
     * (FIDO, keyboard, etc.), they should not be dynamic content */

    if (buf == NULL || bufsize == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    uint32_t offset = 0;
    usbhid_report_infos_t *report;

    /*@ assert ctx->hid_ifaces[hid_handler].get_report_cb \in {&oneidx_get_report_cb} ;*/
    /*@ calls oneidx_get_report_cb; */
    report  = ctx->hid_ifaces[hid_handler].get_report_cb(hid_handler, index);

    if (report == NULL) {
        log_printf("[USBHID] report for handler %d/index %d not found!\n", hid_handler, index);
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (*bufsize < (report->num_items * USBHID_STD_ITEM_LEN)) {
        log_printf("[USBHID] potential report size %d too big for buffer (%d bytes)\n",
                (report->num_items * USBHID_STD_ITEM_LEN), *bufsize);
    }

    /* let's forge the report */
    log_printf("[USBHID] collection size is %d\n", report->num_items);
#ifdef __FRAMAC__
 Previous:
#endif
    /*@
      @ loop invariant 0 <= iterator <= report->num_items ;
      @ loop assigns offset, buf[0..255], iterator, errcode ;
      @ loop variant report->num_items - iterator ;
      */
    for (uint32_t iterator = 0; iterator < report->num_items; ++iterator) {
        /*@ assert (offset < (255 - sizeof(usbhid_short_item_t))); */
        if ((errcode = set_short_item(&(report->items[iterator]), &(buf[offset]), &offset)) != MBED_ERROR_NONE) {
            goto err;
        }
    }
    usbhid_report_sent_trigger(hid_handler, index);
    /* and update the size with the report one */
    *bufsize = offset;
err:
    return errcode;
}
