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
#ifndef USBHID_DESCRIPTOR_H_
#define USBHID_DESCRIPTOR_H_

#include "libc/types.h"
#include "libc/syscall.h"
#include "libusbctrl.h"
#include "autoconf.h"


#define HID_DESCRIPTOR_TYPE 0x21

#define REPORT_DESCRIPTOR_TYPE 0x22

/*
 * About HID global descriptor
 */
typedef enum {
    USBHID_COUNTRYCODE_UNSUPORTED = 0x00,
    USBHID_COUNTRYCODE_ARABIC = 0x01,
    USBHID_COUNTRYCODE_BELGIAN = 0x02,
    USBHID_COUNTRYCODE_CANADIAN_BILIGUAL = 0x03,
    USBHID_COUNTRYCODE_CANADIAN_FRENCH = 0x04,
    USBHID_COUNTRYCODE_CZECH_REPUBLIC = 0x05,
    USBHID_COUNTRYCODE_DANISH = 0x06,
    USBHID_COUNTRYCODE_FINNISH = 0x07,
    USBHID_COUNTRYCODE_FRENCH = 0x08,
    USBHID_COUNTRYCODE_GERMAN = 0x09,
    USBHID_COUNTRYCODE_GREEK = 0x0a,
    USBHID_COUNTRYCODE_HEBREW = 0x0b,
    USBHID_COUNTRYCODE_HUNGARY = 0x0c,
    USBHID_COUNTRYCODE_INTERNATIONAL = 0x0d,
    USBHID_COUNTRYCODE_ITALIAN = 0x0e,
    USBHID_COUNTRYCODE_JAPAN = 0x0f,
    USBHID_COUNTRYCODE_KOREAN = 0x10,
    USBHID_COUNTRYCODE_LATIN_AMERICAN = 0x11,
    USBHID_COUNTRYCODE_DUTCH = 0x12,
    USBHID_COUNTRYCODE_NORWEGIAN = 0x13,
    USBHID_COUNTRYCODE_PERSIAN = 0x14,
    USBHID_COUNTRYCODE_POLAND = 0x15,
    USBHID_COUNTRYCODE_PORTUGUESE = 0x16,
    USBHID_COUNTRYCODE_RUSSIA = 0x17,
    USBHID_COUNTRYCODE_SLOVAKIA = 0x18,
    USBHID_COUNTRYCODE_SPANISH = 0x19,
    USBHID_COUNTRYCODE_SWEDISH = 0x1a,
    USBHID_COUNTRYCODE_SWISS_FRENCH = 0x1b,
    USBHID_COUNTRYCODE_SWISS_GERMAN = 0x1c,
    USBHID_COUNTRYCODE_SWITZERLAND = 0x1d,
    USBHID_COUNTRYCODE_TAIWAN = 0x1e,
    USBHID_COUNTRYCODE_TURKISH_Q = 0x1f,
    USBHID_COUNTRYCODE_UK = 0x20,
    USBHID_COUNTRYCODE_US = 0x21,
    USBHID_COUNTRYCODE_YUGOSLAVIA = 0x22,
    USBHID_COUNTRYCODE_TURKISH_F = 0x23,
} usbhid_contry_code_t;

/* USB HID content descriptor (report, physical) header, that is concatenated to
 * the HID descriptor header, just after the bNumDescriptor field. The number of
 * content descriptor headers is equal to the bNumDescriptors value */
typedef struct __packed {
    uint8_t bDescriptorType; /* type of decriptor */
    uint16_t wDescriptorLength; /* length (in bytes) of descriptor */
} usbhid_content_descriptor_t;


/* USB HID descriptor header */
typedef struct __packed {
    uint8_t bLength;
    uint8_t bDescriptorType;
    uint16_t bcdHID;
    uint8_t bCountryCode;
    uint8_t bNumDescriptors; /* num of class descriptors, at least 1 (report descriptor) */
    /* other potential descriptors */
    usbhid_content_descriptor_t descriptors[];
} usbhid_descriptor_t;


/**********************************************************************************
 * Let's talk about various content descriptors.
 * There is various content descriptor in HID protocol stack. These descriptors are
 * defined here.
 */

/*
 * About physical descriptor. This descriptor is used to specify human body information
 * on physical interactions (finger position, and so on).
 */

/*
 * First, the physical descriptor header, declaring how many physical descriptors
 * are transmitted and the asslocated length.
 */
typedef struct __packed {
    uint8_t bNumber;
    uint16_t bLength;
} usbhid_content_physical_descriptor_header_t;

/*
 * Then, for each physical descriptor, the associated informations
 */
typedef enum {
    USBHID_PHYSICAL_INFO_TYPE_NOTAPPLICABLE = 0,
    USBHID_PHYSICAL_INFO_TYPE_RIGHT_HAND    = 1,
    USBHID_PHYSICAL_INFO_TYPE_LEFT_HAND     = 2,
    USBHID_PHYSICAL_INFO_TYPE_NOTH_HANDS    = 3,
    USBHID_PHYSICAL_INFO_TYPE_EITHER_HAND   = 4,
    /* other bitfields value are reserved */
} usbhid_content_physical_info_t;

typedef struct __packed {
    uint8_t  bPhysicalInfo_preference:5; /* type of physical info, (see enumerate above) */
    uint8_t  bPhysicalInfo_biais:3; /* type of physical info, (see enumerate above) */
    uint8_t  dPhysical[]; /* number of physical data may vary */
} usbhid_content_physical_descriptor_data_t;


/*
 * About HID items
 */
typedef enum {
  USBHID_ITEM_DATA_SIZE_OBYTES = 0,
  USBHID_ITEM_DATA_SIZE_1BYTES = 1,
  USBHID_ITEM_DATA_SIZE_2BYTES = 2,
  USBHID_ITEM_DATA_SIZE_4BYTES = 3,
} usbhid_item_data_size_t;


typedef struct __packed {
    uint32_t bSize:2;
    uint32_t bType:2;
    uint32_t bTag:4;
    uint8_t  data1;
    uint8_t  data2;
} usbhid_short_item_t;


/*
 * Long items. USB HID 1.11 specifications say that Lont item tams are not yet defined
 * and are reserved for future use.
 */
typedef struct __packed {
    uint32_t bSize:2;
    uint32_t bType:2;
    uint32_t bTag:4;
    uint8_t  bDataSize;
    uint8_t  bLongItemTag;
    uint8_t  data[]; /* CAUTION: not allocated here. Data size depends on the item */
} usbhid_long_item_t;

/*
 * TODO: enumerate of item tags (global, local, etc. See chap. 6.2.2.4 and below of USB HI
 * 1.11 specifications)
 */

mbed_error_t      usbhid_get_descriptor(uint8_t             iface_id,
                                        uint8_t            *buf,
                                        uint8_t            *desc_size,
                                        uint32_t            usbdci_handler __attribute__((unused)));


#endif/*!USBHID_DESCRIPTOR_H_*/
