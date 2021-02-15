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
#ifndef LIBUSBHID_FRAMAC_H_
#define LIBUSBHID_FRAMAC_H_

/* ifndef should be useless (caller responsability), but is also added here for protection */
#ifdef __FRAMAC__

#include "libusbotghs.h"

#define usb_backend_drv_declare usbotghs_declare
#define usb_backend_drv_stall usbotghs_endpoint_stall
#define usb_backend_drv_send_data usbotghs_send_data
#define usb_backend_drv_ack usbotghs_endpoint_clear_nak
#define usb_backend_drv_nak usbotghs_endpoint_set_nak
#define usb_backend_drv_send_zlp usbotghs_send_zlp
#define usb_backend_drv_configure_endpoint usbotghs_configure_endpoint
#define usb_backend_drv_set_recv_fifo usbotghs_set_recv_fifo
#define usb_backend_drv_get_ep_state usbotghs_get_ep_state
#define usb_backend_drv_set_recv_fifo usbotghs_set_recv_fifo
#define usb_backend_drv_activate_endpoint usbotghs_activate_endpoint


#define MAX_HID_DESCRIPTORS 8

#define MAX_USBHID_IFACES    4
#define MAX_HID_REPORTS 8

static bool data_being_sent = false;

typedef struct {
    uint8_t  id;      /* IN EP identifier */
    uint16_t idle_ms[MAX_HID_REPORTS]; /* per report (or global): idle time in ms  */
    bool     silence[MAX_HID_REPORTS]; /* per report (or global): is silence requested ?
                                        * a new event associated to this EP unlock it
                                        * (typically a Get_Report request for the
                                        * associated iface) */
} usbhid_inep_t;

/*
 * Each USB HID interface is composed of:
 * - an interface id (used to determine which interface is called by the host), set by libxDCI,
 *   as other classes may declare interfaces to libxDCI
 * - a usbctrl_interface_t structure, passed to the lower libxDCI interface
 * - an IN EP specific HID level meta-properties, associated to the IN EP declared in the
 *   usbctrl_interface_t
 * - various callbacks for standard HID requests
 * - a 'configured' flag, which control that the interface has been properly set and
 *   configured.
 */
typedef struct {
    uint8_t id;
    usbhid_inep_t         inep; /* start at 1 (descriptor id start at 1) */
    usbctrl_interface_t   iface;
    uint8_t               num_descriptors;
    bool                  dedicated_out_ep;
    uint8_t              *in_buff;
    uint32_t              in_buff_len;
    usbhid_get_report_t   get_report_cb;
    usbhid_set_report_t   set_report_cb;
    usbhid_set_protocol_t set_proto_cb;
    usbhid_set_idle_t     set_idle_cb;
    bool                  configured;
    bool                  declared;
} usbhid_iface_t;


/*
 * A USB HID context may have one or more concurrent HID interface(s).
 * These interfaces are declared successively.
 */
typedef struct {
    uint8_t               num_iface; /* number of reports */
    usbhid_iface_t        hid_ifaces[MAX_USBHID_IFACES];
} usbhid_context_t;


usbhid_context_t usbhid_ctx = { 0 };
// pmo addition done for FC
usbhid_report_infos_t report_oneindex;

usbhid_report_infos_t report_twoindex;

/* declaring entrypoint get_report cb prototypes */
/* specs are in entrypoint.c file */
usbhid_report_infos_t   *oneidx_get_report_cb(uint8_t hid_handler, uint8_t index);
usbhid_report_infos_t   *twoidx_get_report_cb(uint8_t hid_handler, uint8_t index);


#define TWOINDEX_ITEMS_NUM 25
#define ONEINDEX_ITEMS_NUM 16
#endif

#endif/*!LIBUSBHID_FRAMAC_H_*/
