#include "generated/devlist.h"
#include "api/libusbhid.h"
#include "autoconf.h"
#include "libc/types.h"
#include "libc/string.h"
//#include <string.h>
#include "usbctrl.h"
#include "usbhid.h"
#include "usbhid_requests.h"
#include "usbhid_default_handlers.h"
#include "usbhid_descriptor.h"
#include "framac/entrypoint.h"

/*
 * Support for Frama-C testing
 */

/* defined in usbhid.c, not exported  */
mbed_error_t usbhid_ep_trigger(uint32_t dev_id, uint32_t size, uint8_t ep_id);

uint8_t my_report[256] = { 0 };
usbhid_report_type_t my_report_type;
uint8_t my_report_index = 0;
/* sample, non-empty, report */

#define ONEINDEX_ITEMS_NUM 16
static usbhid_item_info_t oneindex_items[16] = {
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
};

#define TWOINDEX_ITEMS_NUM 23
static usbhid_item_info_t twoindex_items[23] = {
    /* type, tag, size, data1, data2 */
    { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_USAGE_PAGE, 1, 0x1, 0 }, /* 05 01 */
    { USBHID_ITEM_TYPE_LOCAL, USBHID_ITEM_LOCAL_TAG_USAGE, 1, 0x6, 0 }, /* 09 06 */
    { USBHID_ITEM_TYPE_MAIN, USBHID_ITEM_MAIN_TAG_COLLECTION, 1, USBHID_COLL_ITEM_APPLICATION, 0 },     /* A1 01 */
    /* first, modifier byte */
    { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_USAGE_PAGE, 1, 0x42, 0 },  /* 05 07 */
    { USBHID_ITEM_TYPE_LOCAL, USBHID_ITEM_LOCAL_TAG_USAGE_MIN, 1, 0xe0, 0 }, /* 15 00 */
    { USBHID_ITEM_TYPE_LOCAL, USBHID_ITEM_LOCAL_TAG_USAGE_MAX, 1, 0xe7, 0 }, /* 25 01 */
    { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_LOGICAL_MIN, 1, 0x0, 0 }, /* 15 00 */
    { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_LOGICAL_MAX, 1, 0x1, 0 }, /* 25 64 */
    { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_REPORT_SIZE, 1, 0x1, 0 }, /* 75 01 */
    { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_REPORT_COUNT, 1, 0x8, 0 }, /* 95 08 */
    { USBHID_ITEM_TYPE_MAIN, USBHID_ITEM_MAIN_TAG_INPUT, 1, USBHID_INPUT_TYPE_VARIABLE, 0 }, /* 81 02 */
    /* then reserved byte */
    { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_REPORT_COUNT, 1, 0x1, 0 }, /* 95 08 */
    { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_REPORT_SIZE, 1, 0x8, 0 }, /* 75 01 */
    { USBHID_ITEM_TYPE_MAIN, USBHID_ITEM_MAIN_TAG_INPUT, 1, USBHID_INPUT_TYPE_CONSTANT, 0 }, /* 81 02 */
    /* then key codes  */
    /* each sent report handling one field (report size) of 8 bits (report count).
     *          * This means that sent reports are made of [ data 1B ][ report id (1B) ] */
    { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_REPORT_COUNT, 1, 0x6, 0 }, /* 95 08, 6 items */
    { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_REPORT_SIZE, 1, 0x8, 0 }, /* 75 08, 8 bits per item */
    { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_LOGICAL_MIN, 1, 0x0, 0 }, /* 15 00 */
    { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_LOGICAL_MAX, 1, 0x64, 0 }, /* 25 64 */
    { USBHID_ITEM_TYPE_GLOBAL, USBHID_ITEM_GLOBAL_TAG_USAGE_PAGE, 1, 0x7, 0 },  /* 05 07 */
    { USBHID_ITEM_TYPE_LOCAL, USBHID_ITEM_LOCAL_TAG_USAGE_MIN, 1, 0x0, 0 }, /* 19 00 */
    { USBHID_ITEM_TYPE_LOCAL, USBHID_ITEM_LOCAL_TAG_USAGE_MAX, 1, 0x65, 0 }, /* 19 65 */
    { USBHID_ITEM_TYPE_MAIN, USBHID_ITEM_MAIN_TAG_INPUT, 1, 0x0, 0 }, /* 81 00 */
    { USBHID_ITEM_TYPE_MAIN, USBHID_ITEM_MAIN_TAG_END_COLLECTION, 0, 0, 0 }, /* C0 */
};





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

usbhid_report_infos_t report_oneindex = {
    .num_items = ONEINDEX_ITEMS_NUM,
    .report_id = 0,
    .items = &oneindex_items
};

usbhid_report_infos_t report_twoindex = {
    .num_items = TWOINDEX_ITEMS_NUM,
    .report_id = 0,
    .items = &twoindex_items
};

/*********************************************************************
 * Callbacks implementations that are required by libusbhid API
 */
usbhid_report_infos_t   *oneidx_get_report_cb(uint8_t hid_handler, uint8_t index)
{
    return &report_oneindex;
}

usbhid_report_infos_t   *twoidx_get_report_cb(uint8_t hid_handler, uint8_t index)
{
    return &report_twoindex;
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

uint8_t  hid_handler;

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

    my_report_type = Frama_C_interval_8(0, 2);

    uint8_t USB_subclass = Frama_C_interval_8(0,255);
    uint8_t USB_protocol = Frama_C_interval_8(0,255);
    uint16_t mpsize = Frama_C_interval_16(0,65535);
    uint16_t maxlen = Frama_C_interval_16(0,65535);
    uint8_t poll = Frama_C_interval_8(0,255);

    bool     dedicated_out = Frama_C_interval_b(false, true);



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
        errcode = usbhid_configure(hid_handler, oneidx_get_report_cb, NULL, NULL, NULL);
        errcode = usbhid_configure(hid_handler, oneidx_get_report_cb, set_report_cb, NULL, NULL);
        errcode = usbhid_configure(hid_handler, oneidx_get_report_cb, set_report_cb, set_proto_cb, NULL);
        errcode = usbhid_configure(hid_handler, oneidx_get_report_cb, set_report_cb, set_proto_cb, set_idle_cb);
    }

    if(errcode == MBED_ERROR_NONE){
        usbhid_recv_report(hid_handler, recv_buf, maxlen);
    }
    usbhid_is_silence_requested(hid_handler, 0);

    uint8_t my_response_len = Frama_C_interval_8(0, 255);

    usbhid_send_report(hid_handler, my_report, my_report_type, my_report_index);
    usbhid_send_response(hid_handler, my_report, my_response_len);
    usbhid_response_done(hid_handler);

    /* set two index report */
    errcode = usbhid_configure(hid_handler, NULL, NULL, NULL, NULL);
    errcode = usbhid_configure(hid_handler, twoidx_get_report_cb, NULL, NULL, NULL);
    errcode = usbhid_configure(hid_handler, twoidx_get_report_cb, set_report_cb, NULL, NULL);
    errcode = usbhid_configure(hid_handler, twoidx_get_report_cb, set_report_cb, set_proto_cb, NULL);
    errcode = usbhid_configure(hid_handler, twoidx_get_report_cb, set_report_cb, set_proto_cb, set_idle_cb);

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

    ///////////////////////////////////////////////////
    //        2nd context (one callback set)
    ///////////////////////////////////////////////////
    //

    my_report_type = Frama_C_interval_8(0, 2);
    errcode = usbhid_declare(ctxh1,
            USB_subclass, USB_protocol,
            1, poll, dedicated_out,
            mpsize, &(hid_handler),
            recv_buf,
            maxlen);

    if(errcode == MBED_ERROR_NONE){
        errcode = usbhid_configure(hid_handler, NULL, NULL, NULL, NULL);
        errcode = usbhid_configure(hid_handler, oneidx_get_report_cb, NULL, NULL, NULL);
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

    my_report_type = Frama_C_interval_8(0, 2);
    uint8_t USB_subclass = Frama_C_interval_8(0,255);
    uint8_t USB_protocol = Frama_C_interval_8(0,255);
    uint16_t mpsize = Frama_C_interval_16(0,65535);
    uint16_t maxlen = Frama_C_interval_16(0,65535);
    uint8_t poll = Frama_C_interval_8(0,255);

    bool     dedicated_out = Frama_C_interval_b(false, true);



    uint8_t  hid_handler_err;
    mbed_error_t errcode;


    // invalid ctxh
    errcode = usbhid_declare(ctxh1 + 1,
            USB_subclass, USB_protocol,
            1, poll, dedicated_out,
            mpsize, &(hid_handler_err),
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
            mpsize, &(hid_handler_err),
            NULL, // no buffer
            maxlen);

    errcode = usbhid_declare(ctxh1,
            USB_subclass, USB_protocol,
            0, poll, dedicated_out,
            mpsize, &(hid_handler_err),
            NULL, // no buffer
            maxlen);

    errcode = usbhid_declare(ctxh1,
            USB_subclass, USB_protocol,
            42, poll, dedicated_out,
            mpsize, &(hid_handler_err),
            NULL, // no buffer
            maxlen);




    errcode = usbhid_declare(ctxh1,
            USB_subclass, USB_protocol,
            1, poll, dedicated_out,
            mpsize, &(hid_handler_err),
            recv_buf,
            0); // no length


    /* finishing with valid declratation */
    errcode = usbhid_declare(ctxh1,
            USB_subclass, USB_protocol,
            1, poll, dedicated_out,
            mpsize, &(hid_handler_err),
            recv_buf,
            maxlen);

        errcode = usbhid_configure(hid_handler_err + 1, oneidx_get_report_cb, NULL, NULL, NULL);

        errcode = usbhid_configure(hid_handler_err, NULL, NULL, NULL, NULL);

        errcode = usbhid_configure(hid_handler_err, oneidx_get_report_cb, set_report_cb, set_proto_cb, set_idle_cb);

        usbhid_recv_report(hid_handler_err + 1, recv_buf, maxlen);
        usbhid_recv_report(hid_handler_err, NULL, Frama_C_interval_16(0,maxlen));
        usbhid_recv_report(hid_handler_err, recv_buf, Frama_C_interval_16(0,maxlen));
    usbhid_is_silence_requested(hid_handler_err + 1, Frama_C_interval_8(0,255));

    usbhid_report_type_t my_report_type = Frama_C_interval_8(0, 2);
    uint8_t my_report_index = 0;
    uint8_t my_response_len = Frama_C_interval_8(0, 255);


    usbhid_send_report(hid_handler_err, NULL, my_report_type, Frama_C_interval_8(my_report_index,5));
    usbhid_send_report(hid_handler_err, my_report, my_report_type, Frama_C_interval_8(my_report_index,5));
    usbhid_send_response(hid_handler_err + 1, my_report, my_response_len);
    usbhid_send_response(hid_handler_err + 1, NULL, my_response_len);
    usbhid_send_response(hid_handler_err + 1, my_report, Frama_C_interval_16(0,my_response_len));
    usbhid_response_done(hid_handler_err + 1);
    usbhid_response_done(hid_handler_err);

}

/*requests, triggers... */
void test_fcn_driver_eva() {

    my_report_type = Frama_C_interval_8(0, 2);
    mbed_error_t errcode;
    usbctrl_context_t *ctx = NULL;
    usbctrl_get_context(6, &ctx);

    uint16_t maxlen = Frama_C_interval_16(0,65535);
    /*@ assert ctx != (usbctrl_context_t*)NULL ; */
    uint8_t curr_cfg = 0; /* first cfg declared */
    uint8_t iface = 0; /* first iface declared */
    uint8_t max_ep = ctx->cfg[curr_cfg].interfaces[iface].usb_ep_number ;  // cyril : meme chose que pour max_iface, wp passe maintenant


    /* we set properly backend driver content to be sure that IN/OUT functions have
     * correct driver state on their EP */
    for (uint8_t i = 0; i < max_ep; ++i) {
        usb_backend_drv_ep_dir_t dir;
        if (ctx->cfg[curr_cfg].interfaces[iface].eps[i].type != USB_EP_TYPE_CONTROL) {
            switch (ctx->cfg[curr_cfg].interfaces[iface].eps[i].dir) {
                case USB_EP_DIR_OUT:
                    dir = USB_BACKEND_DRV_EP_DIR_OUT;
                    break;
                case USB_EP_DIR_IN:
                    dir = USB_BACKEND_DRV_EP_DIR_IN;
                    break;
                case USB_EP_DIR_BOTH:
                    dir = USB_BACKEND_DRV_EP_DIR_BOTH;
                    break;
                default:
                    log_printf("[USBCTRL] invalid EP type !\n");
                    errcode = MBED_ERROR_INVPARAM;
                    break;
            }
            /* @assert errcode != MBED_ERROR_INVPARAM ; */
            usb_backend_drv_configure_endpoint(ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num,
                    ctx->cfg[curr_cfg].interfaces[iface].eps[i].type,
                    dir,
                    ctx->cfg[curr_cfg].interfaces[iface].eps[i].pkt_maxsize,
                    USB_BACKEND_EP_ODDFRAME,
                    ctx->cfg[curr_cfg].interfaces[iface].eps[i].handler);
        }
        ctx->cfg[curr_cfg].interfaces[iface].eps[i].configured = true;
    }
    usbctrl_configuration_set();

    /* set input FIFO */
    usbhid_recv_report(hid_handler, recv_buf, maxlen);


    usbctrl_setup_pkt_t pkt = { 0 };
    pkt.wIndex = Frama_C_interval_16(0,65535);
    pkt.bRequest = Frama_C_interval_8(0,255);
    pkt.wLength = Frama_C_interval_16(0,65535);
    pkt.wValue = Frama_C_interval_16(0,65535);
    pkt.bmRequestType = Frama_C_interval_8(0,255);

    uint8_t buf[256];
    uint8_t desc_size = 255;
    /* now we can emulate triggers */
    usbhid_get_descriptor((uint8_t)0, &(buf[0]), &desc_size, 0);

    usbhid_class_rqst_handler(ctxh1, &pkt);

    uint8_t dflt_hid_handler = Frama_C_interval_8(0,255);
    uint8_t dflt_index = Frama_C_interval_8(0,255);
    uint8_t dflt_idle = Frama_C_interval_8(0,255);


    usbhid_dflt_set_report(dflt_hid_handler,dflt_index);
    usbhid_dflt_set_protocol(dflt_hid_handler,dflt_index);
    usbhid_dflt_set_idle(dflt_hid_handler,dflt_idle);

    usbhid_send_report(hid_handler, my_report, my_report_type, my_report_index);
    usbhid_ep_trigger(6, 255, 1);
}

void main(void)
{
    prepare_ctrl_ctx();
    test_fcn_usbhid() ;
    test_fcn_usbhid_erreur() ;
    test_fcn_driver_eva() ;

}
