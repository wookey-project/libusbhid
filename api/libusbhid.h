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
#ifndef LIBUSBHID_H_
#define LIBUSBHID_H_

#include "libc/types.h"
#include "libc/syscall.h"
#include "libusbctrl.h"
#include "autoconf.h"

/*
 * USB HID class is defined here:
 * https://www.usb.org/sites/default/files/documents/hid1_11.pdf
 */

typedef enum {
    USBHID_SUBCLASS_NONE = 0,
    USBHID_SUBCLASS_BOOT_IFACE = 1
} usbhid_subclass_t;

typedef enum {
    USBHID_PROTOCOL_NONE     = 0,
    USBHID_PROTOCOL_KEYBOARD = 1,
    USBHID_PROTOCOL_MOUSE    = 2
} usbhid_protocol_t;


mbed_error_t usbhid_declare(uint32_t usbxdci_handler,
                            usbhid_subclass_t hid_subclass,
                            usbhid_protocol_t hid_protocol);

mbed_error_t usbhid_configure(void);

mbed_error_t usbhid_send_report(uint8_t report_id,
                                uint8_t *report_data,
                                uint8_t report_data_len);

#endif/*!LIBUSBHID*/
