.. _lib_usbhid:


.. highlight:: c

The USB HID 1.1 protocol stack
==============================

.. contents::

Overview
--------

A lot of devices are using the HID class to communicate with the host.
HID class is made for Human Interface Devices, including devices like
keybards, authentication (FIDO U2F) tokens, and a lot of other devices.

The USB HID class defines the way data are transmitted to the host and
the way USB endpoints and descriptors are handled. The goal of this
stack is to handle all the USB-relative part (endpoints declaration,
descriptors, HID report packaging and so on), leaving to the upper
stack the feature related work only (FIDO specific items contents, keyboard
items and report content, etc.), entirely abstracting the USB-specific part.

This library support multiple HID interfaces in the same time, allowing the
declaration of complex HID devices.

The USB HID stack is based on the libxDCI stack which handle the USB 2.0 and
1.1 USB control plane on the device side.

The USB HID types and definitions
---------------------------------

TODO

The USB HID requested triggers
------------------------------

TODO

The USB HID API
---------------

TODO
