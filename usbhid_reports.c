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


#define USBHID_STD_ITEM_LEN             4


uint32_t usbhid_get_report_len(uint8_t index)
{
    usbhid_report_infos_t *report = usbhid_get_report(index);
    uint8_t report_size = 0;
    uint8_t report_count = 0;
    uint32_t report_len = 0;
    if (report == NULL) {
        return 0;
    }
    /* The report len defines the length (in bits in USB HID 1.11) of
     * the data sent after the report identifier.
     * This length is based of the number of data, multiplied by the size
     * of each of them.
     *
     * for a given unique report identifier, even if there is multiple
     * collections with multiple REPORT_SIZE and REPORT_COUNT, these field
     * must handle the same values. If multiple collections handle
     * different REPORT_SIZE/REPORT_COUNT pairs, they must be declared
     * as a part of independent reports */
    for (uint32_t iterator = 0; iterator < report->num_items; ++iterator) {
        if (report->items[iterator].tag == USBHID_ITEM_GLOBAL_TAG_REPORT_SIZE) {
            report_size = report->items[iterator].data1;
        }
        if (report->items[iterator].tag == USBHID_ITEM_GLOBAL_TAG_REPORT_COUNT) {
            report_count = report->items[iterator].data1;
        }
    }

    report_len = report_size * report_count;
    return report_len;
}

/*
 * TODO: return mbed_error_t type, to handle errcode
 */
uint8_t usbhid_get_report_desc_len(uint8_t index)
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
    if (offset > 255) {
        /* descriptor size is encoded in 8bits field in the HID descriptor
         * (USB 2.0 standard) and can't be bigger than 255 bytes */
        log_printf("[USBHID] invalid descriptor size: %d!\n", offset);
        offset = 0;
    }
    return offset;
}



mbed_error_t usbhid_forge_report_descriptor(uint8_t *buf, uint32_t *bufsize, uint8_t index)
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
    usbhid_report_sent_trigger(index);
    /* and update the size with the report one */
    *bufsize = offset;
err:
    return errcode;
}

