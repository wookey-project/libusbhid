#include "generated/devlist.h"
#include "api/libusbhid.h"
#include "autoconf.h"
#include "libc/types.h"
#include "libc/string.h"
//#include <string.h>
#include "usbctrl.h"
#include "usbctrl_state.h"
#include "usbctrl_handlers.h"
#include "usbctrl_requests.h"
#include "usbctrl_descriptors.h"
#include "framac/entrypoint.h"

/*
 * Support for Frama-C testing
 */

uint8_t my_report[256] = { 0 };
/* sample, non-empty, report */
#if 0
static usbhid_report_infos_t report = {
    .num_items = 16,
    .report_id = 0,
    .items = {
        /* this is the standard, datasheet defined FIDO2 HID report */
        { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_USAGE_PAGE, 2, 0x20, 0x32 },
        { USBHID_ITEM_TYPE_LOCAL, USBHID_ITEM_LOCAL_TAG_USAGE, 1, 0x45, 0 },
        { USBHID_ITEM_TYPE_MAIN, USBHID_ITEM_MAIN_TAG_COLLECTION, 1, USBHID_COLL_ITEM_APPLICATION, 0 },
        { USBHID_ITEM_TYPE_LOCAL, USBHID_ITEM_LOCAL_TAG_USAGE, 1, 0x23, 0 },
        { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_LOGICAL_MIN, 1, 0x0, 0 },
        { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_LOGICAL_MAX, 2, 0xff, 0 },
        { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_REPORT_SIZE, 1, 0x8, 0 },
        { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_REPORT_COUNT, 1, 64, 0 }, /* report count in bytes */
        { USBHID_ITEM_TYPE_MAIN, USBHID_ITEM_MAIN_TAG_INPUT, 1, USBHID_IOF_ITEM_DATA|USBHID_IOF_ITEM_CONST|USBHID_IOF_ITEM_VARIABLE|USBHID_IOF_ITEM_RELATIVE, 0 },
        { USBHID_ITEM_TYPE_LOCAL, USBHID_ITEM_LOCAL_TAG_USAGE, 1, 0x23, 0 },
        { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_LOGICAL_MIN, 1, 0x0, 0 },
        { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_LOGICAL_MAX, 2, 0xff, 0 },
        { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_REPORT_SIZE, 1, 0x8, 0 },
        { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_REPORT_COUNT, 1, 64, 0 }, /* report count in bytes */
        { USBHID_ITEM_TYPE_MAIN, USBHID_ITEM_MAIN_TAG_OUTPUT, 1, USBHID_IOF_ITEM_DATA|USBHID_IOF_ITEM_CONST|USBHID_IOF_ITEM_VARIABLE|USBHID_IOF_ITEM_RELATIVE, 0 },
        { USBHID_ITEM_TYPE_MAIN, USBHID_ITEM_MAIN_TAG_END_COLLECTION, 0, 0, 0 }, /* C0 */
    }
};
#endif



//@ assigns Frama_C_entropy_source_b \from Frama_C_entropy_source_b;
void Frama_C_update_entropy_b(void) {
  Frama_C_entropy_source_b = Frama_C_entropy_source_b;
}


//@ assigns Frama_C_entropy_source_8 \from Frama_C_entropy_source_8;
void Frama_C_update_entropy_8(void) {
  Frama_C_entropy_source_8 = Frama_C_entropy_source_8;
}

//@ assigns Frama_C_entropy_source_16 \from Frama_C_entropy_source_16;
void Frama_C_update_entropy_16(void) {
  Frama_C_entropy_source_16 = Frama_C_entropy_source_16;
}

//@ assigns Frama_C_entropy_source_32 \from Frama_C_entropy_source_32;
void Frama_C_update_entropy_32(void) {
  Frama_C_entropy_source_32 = Frama_C_entropy_source_32;
}


/*@ requires order: 0 <= min <= max <= 1;
    assigns \result \from min, max, Frama_C_entropy_source_b;
    assigns Frama_C_entropy_source_b \from Frama_C_entropy_source_b;
    ensures result_bounded: min <= \result <= max ;
 */

bool Frama_C_interval_b(bool min, bool max)
{
  bool r,aux;
  Frama_C_update_entropy_b();
  aux = Frama_C_entropy_source_b;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}



/*@ requires order: 0 <= min <= max <= 255;
    assigns \result \from min, max, Frama_C_entropy_source_8;
    assigns Frama_C_entropy_source_8 \from Frama_C_entropy_source_8;
    ensures result_bounded: min <= \result <= max ;
 */

uint8_t Frama_C_interval_8(uint8_t min, uint8_t max)
{
  uint8_t r,aux;
  Frama_C_update_entropy_8();
  aux = Frama_C_entropy_source_8;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}

/*@ requires order: 0 <= min <= max <= 65535;
    assigns \result \from min, max, Frama_C_entropy_source_16;
    assigns Frama_C_entropy_source_16 \from Frama_C_entropy_source_16;
    ensures result_bounded: min <= \result <= max ;
 */

uint16_t Frama_C_interval_16(uint16_t min, uint16_t max)
{
  uint16_t r,aux;
  Frama_C_update_entropy_16();
  aux = Frama_C_entropy_source_16;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}

/*@ requires order: 0 <= min <= max <= 4294967295;
    assigns \result \from min, max, Frama_C_entropy_source_32;
    assigns Frama_C_entropy_source_32 \from Frama_C_entropy_source_32;
    ensures result_bounded: min <= \result <= max ;
 */

uint32_t Frama_C_interval_32(uint32_t min, uint32_t max)
{
  uint32_t r,aux;
  Frama_C_update_entropy_32();
  aux = Frama_C_entropy_source_32;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}

/*

 test_fcn_usbctrl : test des fonctons définies dans usbctrl.c avec leurs paramètres
 					correctement définis (pas de débordement de tableaux, pointeurs valides...)

*/

uint8_t recv_buf[65535];

/*********************************************************************
 * Callbacks implementations that are required by libusbhid API
 */
usbhid_report_infos_t   *get_report_cb(uint8_t hid_handler, uint8_t index)
{
    return NULL;
}

mbed_error_t set_report_cb(uint8_t hid_handler, uint8_t index)
{
    hid_handler = hid_handler;
    index = index;
    /* FIXME: interval on errors */
    return MBED_ERROR_NONE;
}

mbed_error_t set_proto_cb(uint8_t hid_handler, uint8_t index) {
    hid_handler = hid_handler;
    index = index;
    /* FIXME: interval on errors */
    return MBED_ERROR_NONE;

}

mbed_error_t set_idle_cb(uint8_t hid_handler, uint8_t idle) {
    hid_handler = hid_handler;
    idle = idle;
    /* FIXME: interval on errors */
    return MBED_ERROR_NONE;
}


void usbhid_report_sent_trigger(uint8_t hid_handler,
                                       uint8_t index) {
    hid_handler = hid_handler;
    index = index;
    return;
}

mbed_error_t usbhid_request_trigger(uint8_t hid_handler,
                                    uint8_t hid_req) {
    hid_handler = hid_handler;
    hid_req = hid_req;
    /* FIXME: replace with interval on mbed_error_t */
    return MBED_ERROR_NONE;
}

mbed_error_t usbhid_report_received_trigger(uint8_t hid_handler,
                                            uint16_t size) {
    hid_handler = hid_handler;
    size = size;
    /* FIXME: replace with interval on mbed_error_t */
    return MBED_ERROR_NONE;
}

uint32_t ctxh1=0;

void prepare_ctrl_ctx(){
    usbctrl_declare(6, &ctxh1);
    /*@ assert ctxh1 == 0 ; */
    usbctrl_initialize(ctxh1);
    /*@ assert ctxh1 == 0 ; */
}

void test_fcn_usbhid(){

/*
    def d'une nouvelle interface pour test de la fonction usbctrl_declare_interface
    Déclaration d'une structure usb_rqst_handler_t utilisée dans les interfaces, qui nécessite aussi une structure usbctrl_setup_pkt_t
*/


    uint8_t USB_subclass = Frama_C_interval_8(0,255);
    uint8_t USB_protocol = Frama_C_interval_8(0,255);
    uint16_t mpsize = Frama_C_interval_16(0,65535);
    uint16_t maxlen = Frama_C_interval_16(0,65535);
    uint8_t poll = Frama_C_interval_8(0,255);

    bool     dedicated_out = Frama_C_interval_b(false, true);



    uint8_t  hid_handler;
    mbed_error_t errcode;



    ///////////////////////////////////////////////////
    //        premier context (all callbacks set)
    ///////////////////////////////////////////////////

    errcode = usbhid_declare(ctxh1,
            USB_subclass, USB_protocol,
            1, poll, dedicated_out,
            mpsize, &(hid_handler),
            recv_buf,
            maxlen);

    if(errcode == MBED_ERROR_NONE) {
        errcode = usbhid_configure(hid_handler, NULL, NULL, NULL, NULL);
        errcode = usbhid_configure(hid_handler, get_report_cb, NULL, NULL, NULL);
        errcode = usbhid_configure(hid_handler, get_report_cb, set_report_cb, NULL, NULL);
        errcode = usbhid_configure(hid_handler, get_report_cb, set_report_cb, set_proto_cb, NULL);
        errcode = usbhid_configure(hid_handler, get_report_cb, set_report_cb, set_proto_cb, set_idle_cb);
    }

    if(errcode == MBED_ERROR_NONE){
        usbhid_recv_report(hid_handler, recv_buf, maxlen);
    }
    usbhid_is_silence_requested(hid_handler, 0);

    usbhid_report_type_t my_report_type = Frama_C_interval_8(0, 2);
    uint8_t my_report_index = 0;
    uint8_t my_response_len = Frama_C_interval_8(0, 255);

    usbhid_send_report(hid_handler, my_report, my_report_type, my_report_index);
    usbhid_send_response(hid_handler, my_report, my_response_len);
    usbhid_response_done(hid_handler);

    ///////////////////////////////////////////////////
    //        2nd context (one callback set)
    ///////////////////////////////////////////////////
    //

    errcode = usbhid_declare(ctxh1,
            USB_subclass, USB_protocol,
            1, poll, dedicated_out,
            mpsize, &(hid_handler),
            recv_buf,
            maxlen);

    if(errcode == MBED_ERROR_NONE){
        errcode = usbhid_configure(hid_handler, NULL, NULL, NULL, NULL);
        errcode = usbhid_configure(hid_handler, get_report_cb, NULL, NULL, NULL);
    }

    if(errcode == MBED_ERROR_NONE){
        usbhid_recv_report(hid_handler, recv_buf, maxlen);
    }
    usbhid_is_silence_requested(hid_handler, 0);

    my_report_type = Frama_C_interval_8(0, 2);
    my_report_index = 0;
    my_response_len = Frama_C_interval_8(0, 255);

    usbhid_send_report(hid_handler, my_report, my_report_type, my_report_index);
    usbhid_send_response(hid_handler, my_report, my_response_len);
    usbhid_response_done(hid_handler);


}

/*

 test_fcn_erreur : test des fonctons définies dans usbctrl.c afin d'atteindre les portions de code défensif
                    (pointeurs nulls, débordement de tableaux...)

*/

void test_fcn_usbhid_erreur(){

    uint8_t USB_subclass = Frama_C_interval_8(0,255);
    uint8_t USB_protocol = Frama_C_interval_8(0,255);
    uint16_t mpsize = Frama_C_interval_16(0,65535);
    uint16_t maxlen = Frama_C_interval_16(0,65535);
    uint8_t poll = Frama_C_interval_8(0,255);

    bool     dedicated_out = Frama_C_interval_b(false, true);



    uint8_t  hid_handler;
    mbed_error_t errcode;


    // invalid ctxh
    errcode = usbhid_declare(ctxh1 + 1,
            USB_subclass, USB_protocol,
            1, poll, dedicated_out,
            mpsize, &(hid_handler),
            recv_buf,
            maxlen);

    // invalid ctxh
    errcode = usbhid_declare(ctxh1 + 1,
            USB_subclass, USB_protocol,
            1, poll, dedicated_out,
            mpsize, NULL, // no HID handler here
            recv_buf,
            maxlen);

    errcode = usbhid_declare(ctxh1,
            USB_subclass, USB_protocol,
            1, poll, dedicated_out,
            mpsize, &(hid_handler),
            NULL, // no buffer
            maxlen);

    errcode = usbhid_declare(ctxh1,
            USB_subclass, USB_protocol,
            0, poll, dedicated_out,
            mpsize, &(hid_handler),
            NULL, // no buffer
            maxlen);

    errcode = usbhid_declare(ctxh1,
            USB_subclass, USB_protocol,
            42, poll, dedicated_out,
            mpsize, &(hid_handler),
            NULL, // no buffer
            maxlen);




    errcode = usbhid_declare(ctxh1,
            USB_subclass, USB_protocol,
            1, poll, dedicated_out,
            mpsize, &(hid_handler),
            recv_buf,
            0); // no length


    /* finishing with valid declratation */
    errcode = usbhid_declare(ctxh1,
            USB_subclass, USB_protocol,
            1, poll, dedicated_out,
            mpsize, &(hid_handler),
            recv_buf,
            maxlen);

        errcode = usbhid_configure(hid_handler + 1, get_report_cb, NULL, NULL, NULL);

        errcode = usbhid_configure(hid_handler, NULL, NULL, NULL, NULL);

        errcode = usbhid_configure(hid_handler, get_report_cb, set_report_cb, set_proto_cb, set_idle_cb);

        usbhid_recv_report(hid_handler + 1, recv_buf, maxlen);
        usbhid_recv_report(hid_handler, NULL, Frama_C_interval(0,maxlen));
        usbhid_recv_report(hid_handler, recv_buf, Frama_C_interval(0,maxlen));
    usbhid_is_silence_requested(hid_handler + 1, Frama_C_interval_8(0,255));

    usbhid_report_type_t my_report_type = Frama_C_interval_8(0, 2);
    uint8_t my_report_index = 0;
    uint8_t my_response_len = Frama_C_interval_8(0, 255);


    usbhid_send_report(hid_handler, NULL, my_report_type, Frama_C_interval_8(my_report_index,5));
    usbhid_send_report(hid_handler, my_report, my_report_type, Frama_C_interval_8(my_report_index,5));
    usbhid_send_response(hid_handler + 1, my_report, my_response_len);
    usbhid_send_response(hid_handler + 1, NULL, my_response_len);
    usbhid_send_response(hid_handler + 1, my_report, Frama_C_interval_16(0,my_response_len));
    usbhid_response_done(hid_handler + 1);
    usbhid_response_done(hid_handler);

}

/*requests, triggers... */
void test_fcn_driver_eva(){
}

void main(void)
{
    prepare_ctrl_ctx();
    test_fcn_usbhid() ;
    test_fcn_usbhid_erreur() ;
    test_fcn_driver_eva() ;

}
