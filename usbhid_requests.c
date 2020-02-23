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
#include "libusbotghs.h"
#include "autoconf.h"

/* USBHID class USB RQST */
#define USB_RQST_HID_GET_HID              0x21
#define USB_RQST_HID_GET_REPORT	          0x22
#define USB_RQST_HID_GET_PHYSICAL_DESC    0x23



/**
 * \brief Class request handling for bulk mode.
 *
 * @param packet Setup packet
 */
mbed_error_t usbhid_class_rqst_handler(usbctrl_context_t *ctx __attribute__((unused)),
                                       usbctrl_setup_pkt_t *packet)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    printf("[classRqst] handling HID class rqst\n");
    switch (packet->bRequest) {
        case USB_RQST_HID_GET_HID:
            printf("[classRqst] handling Get HID\n");
#if 0
            /*1. configure descriptor */
            /*2. send data */
            usbotghs_send_data(&desc, sizeof(max_lun), EP0);
            /*3. clear nak */
            usbotghs_endpoint_clear_nak(0, USBOTG_HS_EP_DIR_OUT);
#endif
            break;
        case USB_RQST_HID_GET_REPORT:
            printf("[classRqst] handling get report\n");
#if 0
            /*1. configure descriptor */
            /*2. send data */
            usbotghs_send_data(&desc, sizeof(max_lun), EP0);
            /*3. clear nak */
            usbotghs_endpoint_clear_nak(0, USBOTG_HS_EP_DIR_OUT);
#endif
            break;
        case USB_RQST_HID_GET_PHYSICAL_DESC:
            printf("[classRqst] handling get physical descriptor\n");
#if 0
            /*1. configure descriptor */
            /*2. send data */
            usbotghs_send_data(&desc, sizeof(max_lun), EP0);
            /*3. clear nak */
            usbotghs_endpoint_clear_nak(0, USBOTG_HS_EP_DIR_OUT);
#endif
            break;
        default:
            printf("Unhandled class request (%x)\n", packet->bRequest);
            usbotghs_endpoint_stall(0, USBOTG_HS_EP_DIR_IN);
            goto err;
            break;
    }
err:
    return errcode;
}


