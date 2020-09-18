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
 * PARTICULAR PURPOSE. See the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this package; if not, write to the Free Software Foundation, Inc., 51
 * Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
 *
 */
#ifndef USBHID_REQUESTS_H_
#define USBHID_REQUESTS_H_

#include "libc/types.h"
#include "libc/syscall.h"
#include "libusbctrl.h"
#include "autoconf.h"

mbed_error_t usbhid_class_rqst_handler(uint32_t             usbxdci_handler,
                                       usbctrl_setup_pkt_t *packet);

#ifdef __FRAMAC__
mbed_error_t usbhid_handle_set_protocol(usbctrl_setup_pkt_t *pkt);
#endif

#endif/*!USBHID_REQUESTS_H_*/
