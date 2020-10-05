#ifndef ENTRY_H_
#define ENTRY_H_

#include "libc/types.h"

#define MAX_EPx_PKT_SIZE 512

extern volatile bool Frama_C_entropy_source_b __attribute__((unused)) __attribute__((FRAMA_C_MODEL));
extern volatile uint8_t Frama_C_entropy_source_8 __attribute__((unused)) __attribute__((FRAMA_C_MODEL));
extern volatile uint16_t Frama_C_entropy_source_16 __attribute__((unused)) __attribute__((FRAMA_C_MODEL));
extern volatile uint32_t Frama_C_entropy_source_32 __attribute__((unused)) __attribute__((FRAMA_C_MODEL));


/*@ requires order: 0 <= min <= max <= 1;
    assigns \result \from min, max, Frama_C_entropy_source_b;
    assigns Frama_C_entropy_source_b \from Frama_C_entropy_source_b;
    ensures result_bounded: min <= \result <= max ;
 */
bool Frama_C_interval_b(bool min, bool max);



/*@ requires order: 0 <= min <= max <= 255;
    assigns \result \from min, max, Frama_C_entropy_source_8;
    assigns Frama_C_entropy_source_8 \from Frama_C_entropy_source_8;
    ensures result_bounded: min <= \result <= max ;
 */
uint8_t Frama_C_interval_8(uint8_t min, uint8_t max);

/*@ requires order: 0 <= min <= max <= 65535;
    assigns \result \from min, max, Frama_C_entropy_source_16;
    assigns Frama_C_entropy_source_16 \from Frama_C_entropy_source_16;
    ensures result_bounded: min <= \result <= max ;
 */
uint16_t Frama_C_interval_16(uint16_t min, uint16_t max);

/*@ requires order: 0 <= min <= max <= 4294967295;
    assigns \result \from min, max, Frama_C_entropy_source_32;
    assigns Frama_C_entropy_source_32 \from Frama_C_entropy_source_32;
    ensures result_bounded: min <= \result <= max ;
 */
uint32_t Frama_C_interval_32(uint32_t min, uint32_t max);

/*
 * exported prototypes for internal functions
 */
uint16_t usbhid_get_requested_idle(uint8_t hid_handler, uint8_t index);

/*
 * prototypes only
 */
usbhid_report_infos_t   *oneidx_get_report_cb(uint8_t hid_handler, uint8_t index);

usbhid_report_infos_t   *twoidx_get_report_cb(uint8_t hid_handler, uint8_t index);

mbed_error_t set_report_cb(uint8_t hid_handler, uint8_t index);

mbed_error_t set_proto_cb(uint8_t hid_handler, uint8_t index);

mbed_error_t set_idle_cb(uint8_t hid_handler, uint8_t idle);

#endif/*!ENTRY_H_*/
