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

/******************
 * Triggers various standard HID requests to upper stack
 */
#define USB_CLASS_RQST_GET_REPORT           0x01
#define USB_CLASS_RQST_GET_IDLE             0x02
#define USB_CLASS_RQST_GET_PROTOCOL         0x03
#define USB_CLASS_RQST_SET_REPORT           0x09
#define USB_CLASS_RQST_SET_IDLE             0x0A
#define USB_CLASS_RQST_SET_PROTOCOL         0x0B

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


/**********
 * About item tagging and typing
 * This enumerates permate to upper layers to generate their collections without taking into
 * account the way items are encoded in the HID stack.
 * Collection are passed to the HID layer, which handle the correct encoding based on each
 * successive item tag, type, length and data.
 */
/* TODO: to complete... */

/* usage page defined item, see USB HID usage page table doc 1.12 */
typedef enum {
    USBHID_ITEM_USAGE_PAGE_UNDEFINED = 0x0,
    USBHID_ITEM_USAGE_PAGE_GENERIC_DESKOP = 0x1,
    USBHID_ITEM_USAGE_PAGE_SIMULATION_CTRL = 0x2,
    USBHID_ITEM_USAGE_PAGE_VR_CTRL         = 0x3,
    USBHID_ITEM_USAGE_PAGE_SPORT_CTRL      = 0x4,
    USBHID_ITEM_USAGE_PAGE_GAME_CTRL       = 0x5,
    USBHID_ITEM_USAGE_PAGE_GENERIC_DEV_CTRL= 0x6,
    USBHID_ITEM_USAGE_PAGE_KEYBOARD_KEYPAD = 0x7,
    USBHID_ITEM_USAGE_PAGE_LEDS            = 0x8,
    USBHID_ITEM_USAGE_PAGE_BUTTONS         = 0x9,
    USBHID_ITEM_USAGE_PAGE_ORDINAL         = 0xa,
    USBHID_ITEM_USAGE_PAGE_TELEPHONY       = 0xb,
    USBHID_ITEM_USAGE_PAGE_CONSUMER        = 0xc,
    /* to continue, the list is huge */
} usbhid_item_usage_page_t;

typedef enum {
    USBHID_ITEM_TYPE_MAIN = 0,
    USBHID_ITEM_TYPE_GLOBAL = 1,
    USBHID_ITEM_TYPE_LOCAL = 2,
    USBHID_ITEM_TYPE_RESERVED = 3
} usbhid_item_type_t;


typedef enum {
    /* global item, typed GLOBAL : XXXX 01 NN where XXXX is
     * global item tag, and NN the item size */
    USBHID_ITEM_GLOBAL_TAG_USAGE_PAGE   = 0x0,
    USBHID_ITEM_GLOBAL_TAG_LOGICAL_MIN  = 0x1,
    USBHID_ITEM_GLOBAL_TAG_LOGICAL_MAX  = 0x2,
    USBHID_ITEM_GLOBAL_TAG_PHYSICAL_MIN = 0x3,
    USBHID_ITEM_GLOBAL_TAG_PHYSICAL_MAX = 0x4,
    USBHID_ITEM_GLOBAL_TAG_UNIT_EXPONENT = 0x5,
    USBHID_ITEM_GLOBAL_TAG_UNIT          = 0x6,
    USBHID_ITEM_GLOBAL_TAG_REPORT_SIZE   = 0x7,
    USBHID_ITEM_GLOBAL_TAG_REPORT_ID     = 0x8,
    USBHID_ITEM_GLOBAL_TAG_REPORT_COUNT  = 0x9,
    USBHID_ITEM_GLOBAL_TAG_PUSH          = 0xa,
    USBHID_ITEM_GLOBAL_TAG_POP           = 0xb,
    /* other are reserved */
} usbhid_item_tag_global_t;


typedef enum {
    /* main item, typed MAIN : XXXX 00 NN where XXXX is
     * main item tag, and NN the item size */
    USBHID_ITEM_MAIN_TAG_INPUT = 0x8,
    USBHID_ITEM_MAIN_TAG_OUTPUT = 0x9,
    USBHID_ITEM_MAIN_TAG_FEATURE = 0xb,
    USBHID_ITEM_MAIN_TAG_COLLECTION = 0xa,
    USBHID_ITEM_MAIN_TAG_END_COLLECTION = 0xc
    /* other are reserved */
} usbhid_item_tag_main_t;

/*
 * Types of reports that can be sent
 */
typedef enum {
    USBHID_INTPUT_REPORT  = USBHID_ITEM_MAIN_TAG_INPUT,
    USBHID_OUTPUT_REPORT  = USBHID_ITEM_MAIN_TAG_OUTPUT,
    USBHID_FEATURE_REPORT = USBHID_ITEM_MAIN_TAG_FEATURE
} usbhid_report_type_t;

/* About input, output and feature main item tag (bitfield) */
#define USBHID_IOF_ITEM_DATA        0x0
#define USBHID_IOF_ITEM_CONST       0x1
#define USBHID_IOF_ITEM_ARRAY       0x2
#define USBHID_IOF_ITEM_VARIABLE    0x3
#define USBHID_IOF_ITEM_ABSOLUTE    0x4
#define USBHID_IOF_ITEM_RELATIVE    0x5
#define USBHID_IOF_ITEM_NOWRAP      0x6
#define USBHID_IOF_ITEM_WRAP        0x7
#define USBHID_IOF_ITEM_LINEAR      0x8
#define USBHID_IOF_ITEM_NONLINEAR   0x9
#define USBHID_IOF_ITEM_PREFSTATE   0xa
#define USBHID_IOF_ITEM_NOPREF      0xb
#define USBHID_IOF_ITEM_NONULLPOS   0xc
#define USBHID_IOF_ITEM_NULLSTATE   0xd
#define USBHID_IOF_ITEM_NONVOLATILE 0xe /* Output item specific */
#define USBHID_IOF_ITEM_VOLATILE    0xf /* Output item specific */
#define USBHID_IOF_ITEM_BITFIELD    0x10
#define USBHID_IOF_ITEM_BUFFBYTES   0x11

/* collection tag type (mutually exclusive) */
#define USBHID_COLL_ITEM_PHYSICAL       0x0 /* group of axex */
#define USBHID_COLL_ITEM_APPLICATION    0x1 /* mouse, keyboard */
#define USBHID_COLL_ITEM_LOGICAL        0x2 /* interrrelated data */
#define USBHID_COLL_ITEM_REPORT         0x3
#define USBHID_COLL_ITEM_NAMED_ARRAY    0x4
#define USBHID_COLL_ITEM_USAGE_SWITCH   0x5
#define USBHID_COLL_ITEM_USAGE_MODIFIER 0x6

typedef enum {
    /* local item, typed MAIN : XXXX 10 NN where XXXX is
     * local item tag, and NN the item size */
    USBHID_ITEM_LOCAL_TAG_USAGE = 0x0,
    USBHID_ITEM_LOCAL_TAG_USAGE_MIN = 0x1,
    USBHID_ITEM_LOCAL_TAG_USAGE_MAX = 0x2,
    USBHID_ITEM_LOCAL_TAG_DESIGNATOR_IDX = 0x3,
    USBHID_ITEM_LOCAL_TAG_DESIGNATOR_MIN = 0x4,
    USBHID_ITEM_LOCAL_TAG_DESIGNATOR_MAX = 0x5,
    USBHID_ITEM_LOCAL_TAG_STRING_IDX     = 0x7,
    USBHID_ITEM_LOCAL_TAG_STRING_MIN     = 0x8,
    USBHID_ITEM_LOCAL_TAG_STRING_MAX     = 0x9,
    USBHID_ITEM_LOCAL_TAG_DELIMITER      = 0xa,
    /* other are reserved */
} usbhid_item_tag_local_t;

typedef enum {
    USBHID_INPUT_TYPE_CONSTANT = 0x01,
    USBHID_INPUT_TYPE_VARIABLE = 0x01 << 1,
    USBHID_INPUT_TYPE_COOR_ABS = 0x01 << 2,
    USBHID_INPUT_TYPE_MINMAXWR = 0x01 << 3,
    USBHID_INPUT_TYPE_PHYSREL  = 0x01 << 4,
    USBHID_INPUT_TYPE_PREFSTATE= 0x01 << 5,
    USBHID_INPUT_TYPE_NONULL   = 0x01 << 6,
} usbhid_input_data_type_t;

/*
 * A collection is an ordered set of items.
 * Each item is defined by its type, tag, size (0, 1 or 2 bytes) and data
 */
typedef struct {
    uint8_t type;
    uint8_t tag;
    uint8_t size;
    uint8_t data1;
    uint8_t data2;
} usbhid_item_info_t;

typedef struct {
    uint32_t num_items;
    uint32_t report_id;
    usbhid_item_info_t items[];
} usbhid_report_infos_t;


/* This is the reports that are sent to the host asynchronously on the
 * IN interrupt pipe */
typedef struct {
    uint8_t id;
    uint8_t data[1];
} usbhid_report_t;


/***********************************************************
 * Upper layer-defined callbacks
 *
 * On HID devices, it is complicated to handle upper layer functions as protoypes,
 * because such paradigm implies that there is a single upper HID stack being
 * executed in the same time.
 *
 * When using a hybrid HID device, for e.g. a device handling the following services:
 *
 * - FIDO device, for U2F service
 * - keyboard device
 *
 * As a consequence, the HID stack must handle upper layer calls through registered
 * callbacks, based on the interface registration. The HID stack will then
 * call, in the upper example, the FIDO callbacks or the keyboard callbacks when
 * receiving events:
 *
 *
 * [KBD(1)][ FIDO(2) ]
 *      ^    ^
 *      |    |
 * [   USB HID(1+2)  ]
 *    ^          ^
 *    |          |
 * [ driver   ][ xDCI]
 *
 * Above the HID stack, multiple callbacks are required. They are strictly typed
 * for security reason.
 */

/*
 * A Get_Report request has been received by the device.
 * The upper stack must return the report structure reference,
 * define by the usbhid_report_info_t type. This report is a list of items which
 * is strictly stack-specific.
 * Although, each item is composed of attributes defined by the HID standard.
 * See the usbhid_report_info_t type declaration for more information.
 */
typedef usbhid_report_infos_t *(*usbhid_get_report_t)(uint8_t hid_handler,
                                                     uint8_t index);



/*
 * A Set_Report() request has been received by the device. This can be
 * a request received on EP0 (when the interface only using one IN EP endpoint)
 * or directly a command received on the OUT EP endpoint.
 * The USB HID stack abstract the way the report is sent by the host and
 * call the upper stack in the same way, as the semantic of the request is
 * the same (see HID 1.11 specifications).
 */
typedef mbed_error_t          (*usbhid_set_report_t)(uint8_t hid_handler,
                                                    uint8_t index);


/*
 * For some specific device, a protocol swich may be requested. This is a typical
 * case of keyboards, which handle both Boot mode (BIOS compatibility) and standard
 * mode. For this type of devices, the host can request a protocol set.
 * As this request is a pure upper stack modification, the information is passed to it
 * directly.
 */
typedef mbed_error_t          (*usbhid_set_protocol_t)(uint8_t hid_handler,
                                                      uint8_t proto);


/*
 * The host may requires a non-zero IDLE time which differs from the one
 * previously declared. This value impact the upper layer loop period, which
 * is based on this idle_ms value to handle the periodic transmissions
 * (for stacks sending periodic content) or to handle minimum period between sporadic
 * tranmissions.
 * The upper stack is responsible, for a given interface, to respect the given idle_ms
 * time as a minimum.
 *
 * There is a complex mechansim in HID stack handling silent mode. To avoid too much
 * complexity in the upper stacks, the HID stack abstract the association between
 * idle_ms value, events, and silent mode, and return set_idle only if the value is
 * *non-zero*.
 * In the meantime, the HID stack provides a dedicated API to handle silent mode:
 *
 * bool usbhid_is_silence_requested(uint8_t hid_handler, uint8_t index)
 *
 * if this function return true, the upper stack must silent on the IN EP interface.
 */
typedef mbed_error_t          (*usbhid_set_idle_t)(uint8_t hid_handler,
                                                  uint8_t idle_ms);


/*
 * INFO:
 *
 * Get_Idle handling is directly returned by the HID stack, which keeps a copy of the
 * idle_ms value declared by the upper stack and potentially updated by the host.
 * This is required to handle silent mode during the HID device lifetime.
 *
 * As a consequence, the Get_Idle() event is not pushed to upper stacks.
 */

/*************************************************
 * USB HID stack API
 */

/*
 * Declaring a new USB HID interface. This HID interface is associated to a given
 * HID device type. This interface is composed of a:
 * EP0 IN control plane
 * EPx IN INTERRUPT plane
 * EPx+1 OUT INTERRUPT plane *or* EP0 OUT control plane (see below)
 *
 * The upper stack must pass the USB Control (libxDCI) handler that have been previously
 * declared by the application, as there may have multiple stacks being executed over the
 * same control plane. See the libxDCI API documentation for details.
 *
 * The upper stack declare the HID specific properties:
 * - subclass
 * - protocol
 * - descriptors number (including one report descriptor and potential physical descriptors)
 * - IN EP polling period (in milliseconds)
 * - wether the application requests a dedicated IN and OUT endpoint, or only IN Endpoint
 *   (out is optional in HID class specification, replaced by control Endpoint)
 * - Max packet size for IN (& potential dedicated OUT) EPs
 *
 * the USB HID stack return a handler to interact with this interface
 */
mbed_error_t usbhid_declare(uint32_t          usbxdci_handler,
                            usbhid_subclass_t hid_subclass,
                            usbhid_protocol_t hid_protocol,
                            uint8_t           num_descriptor,
                            uint8_t           poll_time,
                            bool              dedicated_out_ep,
                            uint16_t          ep_mpsize,
                            uint8_t          *hid_handler);

/*
 * Configure callbacks for the given HID interface, identified by its
 * HID handler.
 *
 * INFO: all callbacks are set using empty basic functions at HID level,
 * allowing the upper stack to leave some of the callback empty.
 * This allow, for HID stacks that do not handle some specific requests like
 * Set_Protocol(), to let the libUSBHID handle the default response.
 */
mbed_error_t usbhid_configure(uint8_t               hid_handler,
                              usbhid_get_report_t   get_report_cb,
                              usbhid_set_report_t   set_report_cb,
                              usbhid_set_protocol_t set_proto_cb,
                              usbhid_set_idle_t     set_idle_cb);

/*
 * sending an HID report. report index is the index of the
 * report in the report descriptor, starting with 0
 */
mbed_error_t usbhid_send_report(uint8_t hid_handler,
                                uint8_t *report,
                                usbhid_report_type_t type,
                                uint8_t report_index);


/*
 * Asynchronous report reception call. This API set the OUT Endpoint in order to
 * be ready to receive a HID report on the HID OUT Endpoint of the corresponding
 * HID interface associated to the given HID handler.
 *
 * When an effective reception arise, the usbhid_report_received_trigger is
 * triggered, the data being accessible directly in the report argument buffer.
 */
mbed_error_t usbhid_recv_report(uint8_t hid_handler,
                                uint8_t *report,
                                uint16_t size);
/*
 * USB HID getter (get back the current HID states information
 */

/*
 * get back requested values from standard HID requests. These functions return the
 * values of the host requested:
 * IDLE (Set_Idle command)
 * PROTOCOL (Set_Procotol command)
 */
bool     usbhid_is_silence_requested(uint8_t hid_handler, uint8_t index);

/***********************************************************
 * triggers
 *
 * On some HID specific events (received requests or transmition complete,
 * the upper stack may wish to receive event acknowledgement. They can
 * react to this events the way they want, using the upper API or just by
 * doing nothing.
 * There is two types of triggers:
 * - transmition done trigger (when HID data has been sent asynchronously
 *   on the IN interrupt EP)
 * - request received trigger (when the host has requested a HID specific information,
 *   handled at HID stack level). These requests may impact the upper stack which can,
 *   in consequence, react in the trigger.
 */
void usbhid_report_sent_trigger(uint8_t hid_handler, uint8_t index);

/*
 * This trigger is called for each of the above HID requests, when received.
 * This function must be defined by the upper stack in order to be triggered.
 * A weak symbol is defined if no trigger is used.
 */
mbed_error_t usbhid_request_trigger(uint8_t hid_handler, uint8_t hid_req);


/*
 * This trigger is called for each received HID request on DATA EP.
 * The difference with the request trigger is that requests are SETUP
 * packets, handled as class requests or standard requests targetting
 * HID interface. This handler is made for DATA packets (typically
 * reports sent from the hosts (OUT reports).
 * the hid_handler identifier permits to differenciate potential
 * multiple HID classes on the same HID library of the same application.
 * (e.g. CTAPHID+Keyboard+...)
 */
mbed_error_t usbhid_report_received_trigger(uint8_t hid_handler, uint16_t size);


#endif/*!LIBUSBHID*/
