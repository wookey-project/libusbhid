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
#include "usbhid_default_handlers.h"

mbed_error_t          usbhid_dflt_set_report(uint8_t hid_handler __attribute__((unused)),
                                             uint8_t index __attribute__((unused)))
{
    /* If not handler in the upper stack, this request should not be received */
    return MBED_ERROR_UNSUPORTED_CMD;
}

mbed_error_t          usbhid_dflt_set_protocol(uint8_t hid_handler __attribute__((unused)),
                                               uint8_t proto __attribute__((unused)))
{
    /* If not handler in the upper stack, this request should not be received */
    return MBED_ERROR_UNSUPORTED_CMD;
}

mbed_error_t          usbhid_dflt_set_idle(uint8_t hid_handler __attribute__((unused)),
                                           uint8_t idle_ms __attribute((unused)))
{
    /* this can be handled only at HID stack level. beware of the overload in the
     * upper stack if the device supports variadic periods */
    return MBED_ERROR_NONE;
}
