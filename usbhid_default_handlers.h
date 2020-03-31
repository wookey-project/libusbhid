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
#ifndef USBHID_DEFAULT_HANDLERS_H_
#define USBHID_DEFAULT_HANDLERS_H_

#include "libc/types.h"
#include "autoconf.h"

/*
 * Default callbacks for potential undefined handlers in upper stacks.
 * Some HID requests may not happen for some HID devices (such as Set_Protocol).
 * For these requests, the upper stack does not have to define an empty callback and
 * can let the HID stack respond to this requests autonomously.
 * The HID stack consider (exception for the Set_Idle request which is not mandatory)
 * that the execution of default callbacks is the consequence of an invalid request
 * from the host.
 */


mbed_error_t          usbhid_dflt_set_report(uint8_t hid_handler __attribute__((unused)),
                                             uint8_t index __attribute__((unused)));

mbed_error_t          usbhid_dflt_set_protocol(uint8_t hid_handler __attribute__((unused)),
                                               uint8_t proto __attribute__((unused)));

mbed_error_t          usbhid_dflt_set_idle(uint8_t hid_handler __attribute__((unused)),
                                           uint8_t idle_ms __attribute((unused)));

#endif/*!USBHID_DEFAULT_HANDLERS_H_*/
