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



usbhid_report_infos_t   *get_report(void)
{
    return NULL;
}

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

void test_fcn_usbhid(){


    uint32_t dev_id = (uint32_t)Frama_C_interval_32(0,4294967295) ;
    uint32_t size = Frama_C_interval_32(0,4294967295) ;
    uint32_t handler ;
    uint8_t ep = Frama_C_interval_8(0,255);
    uint8_t iface = Frama_C_interval_8(0,MAX_INTERFACES_PER_DEVICE-1);
    uint8_t ep_number = Frama_C_interval_8(0,MAX_EP_PER_INTERFACE);
    uint8_t EP_type = Frama_C_interval_8(0,3);
    uint8_t EP_dir = Frama_C_interval_8(0,2);
    uint8_t USB_class = Frama_C_interval_8(0,17);
    uint32_t USBdci_handler = Frama_C_interval_32(0,4294967295) ;
    usb_device_trans_t transition = Frama_C_interval_8(0,MAX_TRANSITION_STATE-1) ;
    usb_device_state_t current_state = Frama_C_interval_8(0,9);
    usbctrl_request_code_t request = Frama_C_interval_8(0x0,0xc);
    uint8_t interval = Frama_C_interval_8(0,255);
    //uint8_t class_descriptor_size = Frama_C_interval_8(0,255);




/*
    def d'une nouvelle interface pour test de la fonction usbctrl_declare_interface
    Déclaration d'une structure usb_rqst_handler_t utilisée dans les interfaces, qui nécessite aussi une structure usbctrl_setup_pkt_t
*/

    uint8_t RequestType = Frama_C_interval_8(0,255);
    uint8_t Request = Frama_C_interval_8(0,0xd);
    uint16_t Value = Frama_C_interval_16(0,65535);
    uint16_t Index = Frama_C_interval_16(0,65535);
    uint16_t Length = Frama_C_interval_16(0,65535);


    uint16_t mpsize = Frama_C_interval_16(0,65535);
    uint16_t maxlen = Frama_C_interval_16(0,65535);
    uint8_t poll = Frama_C_interval_8(0,255);

    bool     dedicated_out = Frama_C_interval_b(false, true);



    usbctrl_context_t *ctx1 = NULL;
    usbctrl_context_t *ctx2 = NULL;

    uint32_t ctxh1=0;
    uint32_t ctxh2=0;
    uint8_t  hid_handler;
    mbed_error_t errcode;



    ///////////////////////////////////////////////////
    //        premier context
    ///////////////////////////////////////////////////
    usbctrl_declare(8, &ctxh1);  // in order to check dev_id !=6 and != 7 ;
    usbctrl_declare(6, &ctxh1);
    /*@ assert ctxh1 == 0 ; */
    usbctrl_initialize(ctxh1);
    /*@ assert ctxh1 == 0 ; */

    //usbctrl_get_context(dev_id, &ctx1);
    errcode = usbhid_declare(ctxh1,
            USBHID_SUBCLASS_NONE, USBHID_PROTOCOL_NONE,
            1, poll, dedicated_out,
            mpsize, &(hid_handler),
            recv_buf,
            maxlen);

    if(errcode == MBED_ERROR_NONE){
        errcode = usbhid_configure(hid_handler, get_report, NULL, NULL, NULL);
    }

    if(errcode == MBED_ERROR_NONE){
        usbhid_recv_report(hid_handler, recv_buf, maxlen);
    }


}

/*

 test_fcn_erreur : test des fonctons définies dans usbctrl.c afin d'atteindre les portions de code défensif
                    (pointeurs nulls, débordement de tableaux...)

*/

void test_fcn_usbhid_erreur(){
}

void test_fcn_driver_eva(){
}

void main(void)
{

    test_fcn_usbhid() ;
    test_fcn_usbhid_erreur() ;
    test_fcn_driver_eva() ;

}
