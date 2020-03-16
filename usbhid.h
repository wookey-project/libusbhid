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
#ifndef USBHID_H_
#define USBHID_H_

#include "libc/types.h"
#include "libc/stdio.h"
#include "libc/syscall.h"
#include "libusbctrl.h"
#include "autoconf.h"

#if CONFIG_USR_LIB_USBHID_DEBUG
# define log_printf(...) printf(__VA_ARGS__)
#else
# define log_printf(...)
#endif


#define MAX_REPORTS    8

typedef struct {
    uint8_t  id;
    uint16_t idle_ms;
    bool     silence;
} usbhid_report_state_t;

typedef struct {
    usbctrl_interface_t   iface;
    uint8_t               num_reports; /* number of reports */
    usbhid_report_state_t reports[MAX_REPORTS]; /* start at 1 (descriptor id start at 1) */
} usbhid_context_t;


usbhid_context_t *usbhid_get_context(void);

#endif/*!USBHID_H_*/
