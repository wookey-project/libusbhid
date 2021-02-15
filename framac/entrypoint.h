#ifndef ENTRY_H_
#define ENTRY_H_

#include "libc/types.h"

#define MAX_EPx_PKT_SIZE 512

extern volatile bool Frama_C_entropy_source_b __attribute__((unused)) __attribute__((FRAMA_C_MODEL));
extern volatile uint8_t Frama_C_entropy_source_8 __attribute__((unused)) __attribute__((FRAMA_C_MODEL));
extern volatile uint16_t Frama_C_entropy_source_16 __attribute__((unused)) __attribute__((FRAMA_C_MODEL));
extern volatile uint32_t Frama_C_entropy_source_32 __attribute__((unused)) __attribute__((FRAMA_C_MODEL));


/*@ requires order: 0 <= min <= max <= 1;
    assigns \nothing;
    ensures result_bounded: min <= \result <= max ;
 */
bool Frama_C_interval_b(bool min, bool max);



/*@ requires order: 0 <= min <= max <= 255;
    assigns \nothing;
    ensures result_bounded: min <= \result <= max ;
 */
uint8_t Frama_C_interval_8(uint8_t min, uint8_t max);

/*@ requires order: 0 <= min <= max <= 65535;
    assigns \nothing;
    ensures result_bounded: min <= \result <= max ;
 */
uint16_t Frama_C_interval_16(uint16_t min, uint16_t max);

/*@ requires order: 0 <= min <= max <= 4294967295;
    assigns \nothing;
    ensures result_bounded: min <= \result <= max ;
 */
uint32_t Frama_C_interval_32(uint32_t min, uint32_t max);


//@ assigns Frama_C_entropy_source_b \from Frama_C_entropy_source_b;
void Frama_C_update_entropy_b(void);


//@ assigns Frama_C_entropy_source_8 \from Frama_C_entropy_source_8;
void Frama_C_update_entropy_8(void);


//@ assigns Frama_C_entropy_source_16 \from Frama_C_entropy_source_16;
void Frama_C_update_entropy_16(void);

//@ assigns Frama_C_entropy_source_32 \from Frama_C_entropy_source_32;
void Frama_C_update_entropy_32(void);

/*
 * exported prototypes for internal functions
 */
uint16_t usbhid_get_requested_idle(uint8_t hid_handler, uint8_t index);

/*
 * prototypes only
 */

usbhid_report_infos_t   *oneidx_get_report_cb(uint8_t hid_handler, uint8_t index);

usbhid_report_infos_t   *twoidx_get_report_cb(uint8_t hid_handler, uint8_t index);

/*@ assigns \nothing;
  */
mbed_error_t set_report_cb(uint8_t hid_handler, uint8_t index);

/*@ assigns \nothing;
  */
mbed_error_t set_proto_cb(uint8_t hid_handler, uint8_t index);

/*@ assigns \nothing;
  */
mbed_error_t set_idle_cb(uint8_t hid_handler, uint8_t idle);

uint32_t ctxh1;
uint32_t hid_handler_valid;

uint8_t  hid_handler;

/*@
  @ requires \separated(&GHOST_opaque_drv_privates,&ctxh1,&hid_handler_valid,&hid_handler, ctx_list+ (..));
  @ requires \valid(ctx_list + (0..(GHOST_num_ctx-1))) ;
  @ ensures GHOST_num_ctx == num_ctx ;


  @ behavior bad_num_ctx:
  @   assumes num_ctx >= MAX_USB_CTRL_CTX   ;
  @   ensures ctxh1 == \old(ctxh1) &&  num_ctx == \old(num_ctx) &&  GHOST_opaque_drv_privates == \old(GHOST_opaque_drv_privates) && ctx_list[\old(num_ctx)] == \old(ctx_list[\old(num_ctx)]) ;
  @   ensures \result == MBED_ERROR_NOMEM ;
  @
  @  behavior ok:
  @   assumes num_ctx < MAX_USB_CTRL_CTX ;
  @   ensures \result == MBED_ERROR_NONE ==> (ctxh1 == \old(GHOST_num_ctx));
  @
  @ complete behaviors;
  @ disjoint behaviors;
*/
mbed_error_t prepare_ctrl_ctx(void);

/*@ assigns \nothing; */
void usbhid_report_sent_trigger(uint8_t hid_handler,uint8_t index);


#endif/*!ENTRY_H_*/
