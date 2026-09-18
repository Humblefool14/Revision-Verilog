#!/usr/bin/env python3
"""
xhci_trb_parser.py
===================

A parser for xHCI (eXtensible Host Controller Interface) Transfer Request
Blocks (TRBs), covering the Command TRBs and a handful of Event TRBs defined
in the xHCI specification (section 6.4).

Every TRB is a fixed 16-byte (4 x 32-bit DWORD) structure:

    DWORD0  (bytes 00h-03h)
    DWORD1  (bytes 04h-07h)
    DWORD2  (bytes 08h-0Bh)
    DWORD3  (bytes 0Ch-0Fh)  -> always carries Cycle bit (bit 0) and
                                TRB Type (bits 15:10)

What this script does
----------------------
1. Defines the TRB Type enumeration (Table 6-91 in the spec).
2. Defines a generic 16-byte TRB container that can pull out the Cycle bit
   and TRB Type from any TRB, regardless of its specific layout.
3. Defines per-TRB-type field decoders (one function per TRB type) that know
   the specific bit layout of that TRB, as laid out in the Field Definition
   tables (e.g. Table 6-58 for No Op Command, Table 6-61/6-62 for Address
   Device Command, etc.).
4. Dispatches an arbitrary 16-byte blob to the right decoder based on its
   TRB Type field, and returns a structured, human-readable result.

Supported TRB types
--------------------
Transfer TRBs (section 6.4.1):
    - Normal TRB                           (6.4.1.1, figure 6-8)
    - Setup Stage TRB                      (6.4.1.2.1, figure 6-9)
    - Data Stage TRB                       (6.4.1.2.2, figure 6-10)
    - Status Stage TRB                     (6.4.1.2.3, figure 6-11)
    - Isoch TRB                            (6.4.1.3, figure 6-12)
    - No Op TRB (transfer ring)            (6.4.1.4, figure 6-13)

Command TRBs:
    - No Op Command                     (6.4.3.1)
    - Enable Slot Command                (6.4.3.2)
    - Disable Slot Command                (6.4.3.3)
    - Address Device Command             (6.4.3.4)
    - Configure Endpoint Command          (6.4.3.5)
    - Evaluate Context Command            (6.4.3.6)
    - Reset Endpoint Command              (6.4.3.7)
    - Stop Endpoint Command                (6.4.3.8)
    - Set TR Dequeue Pointer Command      (6.4.3.9)
    - Reset Device Command                  (6.4.3.10)
    - Force Event Command                    (6.4.3.11)
    - Set Latency Tolerance Value Command    (6.4.3.13)
    - Get Port Bandwidth Command             (6.4.3.14, figure 6-34)
    - Force Header Command                    (6.4.3.15)
    - Get Extended Property Command           (6.4.3.16)
    - Set Extended Property Command          (6.4.3.17 style, tables 6-82/6-83)

Event TRBs (section 6.4.2):
    - Transfer Event                       (6.4.2.1, figure 6-14)
    - Command Completion Event             (6.4.2.2, figure 6-15)
    - Port Status Change Event             (6.4.2.3, figure 6-16)
    - Bandwidth Request Event              (6.4.2.4, figure 6-17)
    - Doorbell Event                       (6.4.2.5, figure 6-18)
    - Host Controller Event               (6.4.2.6)
    - Device Notification Event           (6.4.2.7)
    - MFINDEX Wrap Event                   (6.4.2.8)

Usage
-----
As a library:

    from xhci_trb_parser import parse_trb

    raw = bytes.fromhex("00000000 00000000 00000000 01004001".replace(" ", ""))
    trb = parse_trb(raw)
    print(trb.describe())

As a CLI:

    $ python3 xhci_trb_parser.py 00000000000000000000000001004001
    $ python3 xhci_trb_parser.py --file trb_dump.bin
"""

from __future__ import annotations

import argparse
import struct
import sys
from dataclasses import dataclass, field
from enum import IntEnum
from typing import Callable, Dict, List, Optional


TRB_SIZE = 16  # bytes; every TRB is 4 DWORDs


# ---------------------------------------------------------------------------
# TRB Type enumeration (xHCI spec, Table 6-91)
# ---------------------------------------------------------------------------

class TRBType(IntEnum):
    RESERVED = 0
    NORMAL = 1
    SETUP_STAGE = 2
    DATA_STAGE = 3
    STATUS_STAGE = 4
    ISOCH = 5
    LINK = 6
    EVENT_DATA = 7
    NO_OP_TRANSFER = 8
    ENABLE_SLOT_COMMAND = 9
    DISABLE_SLOT_COMMAND = 10
    ADDRESS_DEVICE_COMMAND = 11
    CONFIGURE_ENDPOINT_COMMAND = 12
    EVALUATE_CONTEXT_COMMAND = 13
    RESET_ENDPOINT_COMMAND = 14
    STOP_ENDPOINT_COMMAND = 15
    SET_TR_DEQUEUE_POINTER_COMMAND = 16
    RESET_DEVICE_COMMAND = 17
    FORCE_EVENT_COMMAND = 18
    NEGOTIATE_BANDWIDTH_COMMAND = 19
    SET_LATENCY_TOLERANCE_VALUE_COMMAND = 20
    GET_PORT_BANDWIDTH_COMMAND = 21
    FORCE_HEADER_COMMAND = 22
    NO_OP_COMMAND = 23
    GET_EXTENDED_PROPERTY_COMMAND = 24
    SET_EXTENDED_PROPERTY_COMMAND = 25
    # 26-31 reserved
    TRANSFER_EVENT = 32
    COMMAND_COMPLETION_EVENT = 33
    PORT_STATUS_CHANGE_EVENT = 34
    BANDWIDTH_REQUEST_EVENT = 35
    DOORBELL_EVENT = 36
    HOST_CONTROLLER_EVENT = 37
    DEVICE_NOTIFICATION_EVENT = 38
    MFINDEX_WRAP_EVENT = 39
    # 40-47 reserved
    # 48-63 vendor defined

    @classmethod
    def _missing_(cls, value):
        # Unknown/reserved/vendor-defined TRB types shouldn't blow up parsing.
        return None


TRB_TYPE_NAMES: Dict[int, str] = {t.value: t.name for t in TRBType}


def trb_type_name(value: int) -> str:
    if value in TRB_TYPE_NAMES:
        return TRB_TYPE_NAMES[value]
    if 26 <= value <= 31 or 40 <= value <= 47:
        return f"RESERVED({value})"
    if 48 <= value <= 63:
        return f"VENDOR_DEFINED({value})"
    return f"UNKNOWN({value})"


# ---------------------------------------------------------------------------
# Completion Code enumeration (subset, xHCI spec section 6.4.5) - used by
# Event TRBs.
# ---------------------------------------------------------------------------

class CompletionCode(IntEnum):
    INVALID = 0
    SUCCESS = 1
    DATA_BUFFER_ERROR = 2
    BABBLE_DETECTED_ERROR = 3
    USB_TRANSACTION_ERROR = 4
    TRB_ERROR = 5
    STALL_ERROR = 6
    RESOURCE_ERROR = 7
    BANDWIDTH_ERROR = 8
    NO_SLOTS_AVAILABLE_ERROR = 9
    INVALID_STREAM_TYPE_ERROR = 10
    SLOT_NOT_ENABLED_ERROR = 11
    ENDPOINT_NOT_ENABLED_ERROR = 12
    SHORT_PACKET = 13
    RING_UNDERRUN = 14
    RING_OVERRUN = 15
    VF_EVENT_RING_FULL_ERROR = 16
    PARAMETER_ERROR = 17
    BANDWIDTH_OVERRUN_ERROR = 18
    CONTEXT_STATE_ERROR = 19
    NO_PING_RESPONSE_ERROR = 20
    EVENT_RING_FULL_ERROR = 21
    INCOMPATIBLE_DEVICE_ERROR = 22
    MISSED_SERVICE_ERROR = 23
    COMMAND_RING_STOPPED = 24
    COMMAND_ABORTED = 25
    STOPPED = 26
    STOPPED_LENGTH_INVALID = 27
    STOPPED_SHORT_PACKET = 28
    MAX_EXIT_LATENCY_TOO_LARGE_ERROR = 29
    ISOCH_BUFFER_OVERRUN = 31
    EVENT_LOST_ERROR = 32
    UNDEFINED_ERROR = 33
    INVALID_STREAM_ID_ERROR = 34
    SECONDARY_BANDWIDTH_ERROR = 35
    SPLIT_TRANSACTION_ERROR = 36

    @classmethod
    def _missing_(cls, value):
        return None


def completion_code_name(value: int) -> str:
    try:
        return CompletionCode(value).name
    except ValueError:
        return f"UNKNOWN({value})"


# ---------------------------------------------------------------------------
# Bit extraction helpers
# ---------------------------------------------------------------------------

def bits(dword: int, hi: int, lo: int) -> int:
    """Extract bits [hi:lo] (inclusive) from a 32-bit value."""
    mask = (1 << (hi - lo + 1)) - 1
    return (dword >> lo) & mask


def bit(dword: int, n: int) -> int:
    return (dword >> n) & 1


# ---------------------------------------------------------------------------
# Result container
# ---------------------------------------------------------------------------

@dataclass
class ParsedTRB:
    raw: bytes
    dwords: List[int]
    trb_type_value: int
    trb_type_name: str
    cycle_bit: Optional[int]
    fields: Dict[str, object] = field(default_factory=dict)
    notes: List[str] = field(default_factory=list)

    def describe(self) -> str:
        lines = []
        lines.append(f"TRB Type   : {self.trb_type_value} ({self.trb_type_name})")
        if self.cycle_bit is not None:
            lines.append(f"Cycle (C)  : {self.cycle_bit}")
        lines.append(f"Raw DWORDs : " + " ".join(f"{d:08x}" for d in self.dwords))
        if self.fields:
            lines.append("Fields:")
            for k, v in self.fields.items():
                lines.append(f"  {k}: {v}")
        for n in self.notes:
            lines.append(f"Note: {n}")
        return "\n".join(lines)


# ---------------------------------------------------------------------------
# Core: split a 16-byte TRB into 4 little-endian DWORDs
# ---------------------------------------------------------------------------

def to_dwords(raw: bytes) -> List[int]:
    if len(raw) != TRB_SIZE:
        raise ValueError(f"TRB must be exactly {TRB_SIZE} bytes, got {len(raw)}")
    return list(struct.unpack("<4I", raw))


# ---------------------------------------------------------------------------
# Per-TRB-type field decoders.
#
# Each decoder takes the 4 dwords and returns a dict of field-name -> value.
# Field bit ranges follow the tables cited in each docstring.
# ---------------------------------------------------------------------------

# --- Transfer TRBs (Transfer Ring) ------------------------------------------

def _decode_data_buffer_pointer(dw: List[int]) -> int:
    """Data/TRB Buffer Pointer Hi:Lo spans all of DW0 and DW1 (byte-aligned,
    unlike the 16-byte-aligned context pointers used by Command TRBs)."""
    return (dw[1] << 32) | dw[0]


def _decode_normal_trb(dw: List[int]) -> Dict[str, object]:
    """Tables 6-20/6-21 (figure 6-8): Normal TRB."""
    return {
        "Data Buffer Pointer": f"0x{_decode_data_buffer_pointer(dw):016x}",
        "TRB Transfer Length (16:0 of DW2)": bits(dw[2], 16, 0),
        "TD Size (21:17 of DW2)": bits(dw[2], 21, 17),
        "Interrupter Target (31:22 of DW2)": bits(dw[2], 31, 22),
        "Cycle (C, bit 0)": bit(dw[3], 0),
        "Evaluate Next TRB (ENT, bit 1)": bit(dw[3], 1),
        "Interrupt-on Short Packet (ISP, bit 2)": bit(dw[3], 2),
        "No Snoop (NS, bit 3)": bit(dw[3], 3),
        "Chain bit (CH, bit 4)": bit(dw[3], 4),
        "Interrupt On Completion (IOC, bit 5)": bit(dw[3], 5),
        "Immediate Data (IDT, bit 6)": bit(dw[3], 6),
        "Block Event Interrupt (BEI, bit 9)": bit(dw[3], 9),
    }


def _decode_setup_stage_trb(dw: List[int]) -> Dict[str, object]:
    """Tables 6-23/6-24/6-25/6-26 (figure 6-9): Setup Stage TRB."""
    trt_names = {0: "No Data Stage", 1: "Reserved", 2: "OUT Data Stage", 3: "IN Data Stage"}
    trt = bits(dw[3], 17, 16)
    return {
        "bmRequestType (7:0 of DW0)": bits(dw[0], 7, 0),
        "bRequest (15:8 of DW0)": bits(dw[0], 15, 8),
        "wValue (31:16 of DW0)": bits(dw[0], 31, 16),
        "wIndex (15:0 of DW1)": bits(dw[1], 15, 0),
        "wLength (31:16 of DW1)": bits(dw[1], 31, 16),
        "TRB Transfer Length (16:0 of DW2, always 8)": bits(dw[2], 16, 0),
        "Interrupter Target (31:22 of DW2)": bits(dw[2], 31, 22),
        "Cycle (C, bit 0)": bit(dw[3], 0),
        "Interrupt On Completion (IOC, bit 5)": bit(dw[3], 5),
        "Immediate Data (IDT, bit 6, always 1)": bit(dw[3], 6),
        "Transfer Type (TRT, 17:16)": f"{trt} ({trt_names.get(trt, 'Unknown')})",
    }


def _decode_data_stage_trb(dw: List[int]) -> Dict[str, object]:
    """Tables 6-27/6-28/6-29 (figure 6-10): Data Stage TRB."""
    direction = bit(dw[3], 16)
    return {
        "Data Buffer Pointer": f"0x{_decode_data_buffer_pointer(dw):016x}",
        "TRB Transfer Length (16:0 of DW2)": bits(dw[2], 16, 0),
        "TD Size (21:17 of DW2)": bits(dw[2], 21, 17),
        "Interrupter Target (31:22 of DW2)": bits(dw[2], 31, 22),
        "Cycle (C, bit 0)": bit(dw[3], 0),
        "Evaluate Next TRB (ENT, bit 1)": bit(dw[3], 1),
        "Interrupt-on Short Packet (ISP, bit 2)": bit(dw[3], 2),
        "No Snoop (NS, bit 3)": bit(dw[3], 3),
        "Chain bit (CH, bit 4)": bit(dw[3], 4),
        "Interrupt On Completion (IOC, bit 5)": bit(dw[3], 5),
        "Immediate Data (IDT, bit 6)": bit(dw[3], 6),
        "Direction (DIR, bit 16)": "IN (device-to-host)" if direction else "OUT (host-to-device)",
    }


def _decode_status_stage_trb(dw: List[int]) -> Dict[str, object]:
    """Tables 6-30/6-31 (figure 6-11): Status Stage TRB."""
    direction = bit(dw[3], 16)
    return {
        "Interrupter Target (31:22 of DW2)": bits(dw[2], 31, 22),
        "Cycle (C, bit 0)": bit(dw[3], 0),
        "Evaluate Next TRB (ENT, bit 1)": bit(dw[3], 1),
        "Chain bit (CH, bit 4)": bit(dw[3], 4),
        "Interrupt On Completion (IOC, bit 5)": bit(dw[3], 5),
        "Direction (DIR, bit 16)": "IN (device-to-host)" if direction else "OUT (host-to-device)",
    }


def _decode_isoch_trb(dw: List[int]) -> Dict[str, object]:
    """Tables 6-32/6-33/6-34 (figure 6-12): Isoch TRB."""
    return {
        "Data Buffer Pointer": f"0x{_decode_data_buffer_pointer(dw):016x}",
        "TRB Transfer Length (16:0 of DW2)": bits(dw[2], 16, 0),
        "TD Size / TBC (21:17 of DW2)": bits(dw[2], 21, 17),
        "Interrupter Target (31:22 of DW2)": bits(dw[2], 31, 22),
        "Cycle (C, bit 0)": bit(dw[3], 0),
        "Evaluate Next TRB (ENT, bit 1)": bit(dw[3], 1),
        "Interrupt-on Short Packet (ISP, bit 2)": bit(dw[3], 2),
        "No Snoop (NS, bit 3)": bit(dw[3], 3),
        "Chain bit (CH, bit 4)": bit(dw[3], 4),
        "Interrupt On Completion (IOC, bit 5)": bit(dw[3], 5),
        "Immediate Data (IDT, bit 6)": bit(dw[3], 6),
        "TBC / TRBSts (8:7)": bits(dw[3], 8, 7),
        "Block Event Interrupt (BEI, bit 9)": bit(dw[3], 9),
        "TLBPC (18:16)": bits(dw[3], 18, 16),
        "Frame ID (30:20)": bits(dw[3], 30, 20),
        "Start Isoch ASAP (SIA, bit 31)": bit(dw[3], 31),
    }


def _decode_no_op_transfer_trb(dw: List[int]) -> Dict[str, object]:
    """Tables 6-35/6-36 (figure 6-13): No Op TRB (Transfer Ring)."""
    return {
        "Interrupter Target (31:22 of DW2)": bits(dw[2], 31, 22),
        "Cycle (C, bit 0)": bit(dw[3], 0),
        "Evaluate Next TRB (ENT, bit 1)": bit(dw[3], 1),
        "Chain bit (CH, bit 4)": bit(dw[3], 4),
        "Interrupt On Completion (IOC, bit 5)": bit(dw[3], 5),
    }


def _decode_no_op_command(dw: List[int]) -> Dict[str, object]:
    """Table 6-58: Offset 0Ch - No Op Command TRB."""
    return {
        "Slot Type (20:16)": bits(dw[3], 20, 16),
        "TRB Type (15:10)": bits(dw[3], 15, 10),
    }


def _decode_enable_slot_command(dw: List[int]) -> Dict[str, object]:
    """Table 6-59: Offset 0Ch - Enable Slot Command TRB."""
    return {
        "Slot Type (20:16)": bits(dw[3], 20, 16),
    }


def _decode_disable_slot_command(dw: List[int]) -> Dict[str, object]:
    """Table 6-60: Offset 0Ch - Disable Slot Command TRB."""
    return {
        "Slot ID (31:24)": bits(dw[3], 31, 24),
    }


def _decode_input_context_pointer(dw: List[int]) -> int:
    """Common to Address Device / Configure Endpoint / Evaluate Context.
    Input Context Pointer Lo occupies bits 31:4 of DWORD0 (bits 3:0 RsvdZ),
    Input Context Pointer Hi is all of DWORD1.
    """
    ptr_lo = dw[0] & 0xFFFFFFF0
    ptr_hi = dw[1]
    return (ptr_hi << 32) | ptr_lo


def _decode_address_device_command(dw: List[int]) -> Dict[str, object]:
    """Tables 6-61/6-62: Address Device Command TRB."""
    return {
        "Input Context Pointer": f"0x{_decode_input_context_pointer(dw):016x}",
        "Block Set Address Request (BSR, bit 9)": bit(dw[3], 9),
        "Slot ID (31:24)": bits(dw[3], 31, 24),
    }


def _decode_configure_endpoint_command(dw: List[int]) -> Dict[str, object]:
    """Tables 6-63/6-64: Configure Endpoint Command TRB."""
    return {
        "Input Context Pointer": f"0x{_decode_input_context_pointer(dw):016x}",
        "Deconfigure (DC, bit 9)": bit(dw[3], 9),
        "Slot ID (31:24)": bits(dw[3], 31, 24),
    }


def _decode_evaluate_context_command(dw: List[int]) -> Dict[str, object]:
    """Figure 6-27: Evaluate Context Command TRB (same layout as Address
    Device Command, but BSR bit is unused)."""
    return {
        "Input Context Pointer": f"0x{_decode_input_context_pointer(dw):016x}",
        "Slot ID (31:24)": bits(dw[3], 31, 24),
    }


def _decode_reset_endpoint_command(dw: List[int]) -> Dict[str, object]:
    """Table 6-65: Offset 0Ch - Reset Endpoint Command TRB."""
    return {
        "Transfer State Preserve (TSP, bit 9)": bit(dw[3], 9),
        "Endpoint ID (20:16)": bits(dw[3], 20, 16),
        "Slot ID (31:24)": bits(dw[3], 31, 24),
    }


def _decode_stop_endpoint_command(dw: List[int]) -> Dict[str, object]:
    """Table 6-66: Offset 0Ch - Stop Endpoint Command TRB."""
    return {
        "Endpoint ID (20:16)": bits(dw[3], 20, 16),
        "Suspend (SP, bit 23)": bit(dw[3], 23),
        "Slot ID (31:24)": bits(dw[3], 31, 24),
    }


def _decode_set_tr_dequeue_pointer_command(dw: List[int]) -> Dict[str, object]:
    """Tables 6-67/6-68/6-69: Set TR Dequeue Pointer Command TRB."""
    dcs = bit(dw[0], 0)
    sct = bits(dw[0], 3, 1)
    new_tr_dq_ptr_lo = dw[0] & 0xFFFFFFF0
    new_tr_dq_ptr_hi = dw[1]
    new_tr_dq_ptr = (new_tr_dq_ptr_hi << 32) | new_tr_dq_ptr_lo
    stream_id = bits(dw[2], 31, 16)
    return {
        "Dequeue Cycle State (DCS, bit 0 of DW0)": dcs,
        "Stream Context Type (SCT, bits 3:1 of DW0)": sct,
        "New TR Dequeue Pointer": f"0x{new_tr_dq_ptr:016x}",
        "Stream ID (31:16 of DW2)": stream_id,
        "Endpoint ID (20:16)": bits(dw[3], 20, 16),
        "Slot ID (31:24)": bits(dw[3], 31, 24),
    }


def _decode_reset_device_command(dw: List[int]) -> Dict[str, object]:
    """Table 6-70: Offset 0Ch - Reset Device Command TRB."""
    return {
        "Slot ID (31:24)": bits(dw[3], 31, 24),
    }


def _decode_force_event_command(dw: List[int]) -> Dict[str, object]:
    """Tables 6-71/6-72/6-73: Force Event Command TRB."""
    ptr_lo = dw[0] & 0xFFFFFFF0
    ptr_hi = dw[1]
    event_trb_ptr = (ptr_hi << 32) | ptr_lo
    vf_interrupter_target = bits(dw[2], 31, 22)
    return {
        "Event TRB Pointer": f"0x{event_trb_ptr:016x}",
        "VF Interrupter Target (31:22 of DW2)": vf_interrupter_target,
        "VF ID (23:16)": bits(dw[3], 23, 16),
    }


def _decode_set_ltv_command(dw: List[int]) -> Dict[str, object]:
    """Table 6-74: Offset 0Ch - Set Latency Tolerance Value Command TRB."""
    return {
        "Best Effort Latency Tolerance Value (BELT, 27:16)": bits(dw[3], 27, 16),
    }


def _decode_get_port_bandwidth_command(dw: List[int]) -> Dict[str, object]:
    """Tables 6-75/6-76: Get Port Bandwidth Command TRB."""
    ptr_lo = dw[0] & 0xFFFFFFF0
    ptr_hi = dw[1]
    ctx_ptr = (ptr_hi << 32) | ptr_lo
    return {
        "Port Bandwidth Context Pointer": f"0x{ctx_ptr:016x}",
        "Dev Speed (19:16)": bits(dw[3], 19, 16),
        "Hub Slot ID (31:24)": bits(dw[3], 31, 24),
    }


def _decode_force_header_command(dw: List[int]) -> Dict[str, object]:
    """Tables 6-77/6-78: Force Header Command TRB."""
    packet_type = bits(dw[0], 4, 0)
    # Header Info spans bits 95:5 across DW0[31:5], DW1[31:0], DW2[31:0].
    header_info = (dw[0] >> 5) | (dw[1] << 27) | (dw[2] << 59)
    return {
        "Packet Type (4:0 of DW0)": packet_type,
        "Header Info (95:5, 91-bit value)": f"0x{header_info:023x}",
        "Root Hub Port Number (31:24)": bits(dw[3], 31, 24),
    }


def _decode_get_extended_property_command(dw: List[int]) -> Dict[str, object]:
    """Table 6-79 and adjoining tables: Get Extended Property Command TRB."""
    ptr_lo = dw[0] & 0xFFFFFFF0
    ptr_hi = dw[1]
    ctx_ptr = (ptr_hi << 32) | ptr_lo
    eci = bits(dw[2], 15, 0)
    return {
        "Extended Property Context Pointer": f"0x{ctx_ptr:016x}",
        "Extended Capability Identifier (ECI, 15:0 of DW2)": eci,
        "Slot ID (31:24)": bits(dw[3], 31, 24),
        "Endpoint ID (23:19)": bits(dw[3], 23, 19),
        "Command SubType (18:16)": bits(dw[3], 18, 16),
    }


def _decode_set_extended_property_command(dw: List[int]) -> Dict[str, object]:
    """Tables 6-82/6-83: Set Extended Property Command TRB."""
    eci = bits(dw[2], 15, 0)
    capability_parameter = bits(dw[2], 23, 15)
    return {
        "Extended Capability Identifier (ECI, 15:0 of DW2)": eci,
        "Capability Parameter (23:15 of DW2)": capability_parameter,
        "Command SubType (18:16)": bits(dw[3], 18, 16),
        "Endpoint ID (23:19)": bits(dw[3], 23, 19),
        "Slot ID (31:24)": bits(dw[3], 31, 24),
    }


# --- Event TRBs -------------------------------------------------------------

def _decode_transfer_event(dw: List[int]) -> Dict[str, object]:
    """Tables 6-37/6-38/6-39 (figure 6-14): Transfer Event TRB."""
    code = bits(dw[2], 31, 24)
    ed = bit(dw[3], 2)
    ptr = _decode_data_buffer_pointer(dw)
    return {
        "TRB Pointer / Event Data (63:0)": f"0x{ptr:016x}",
        "TRB Transfer Length (23:0 of DW2)": bits(dw[2], 23, 0),
        "Completion Code (31:24 of DW2)": f"{code} ({completion_code_name(code)})",
        "Event Data (ED, bit 2)": ed,
        "Endpoint ID (20:16)": bits(dw[3], 20, 16),
        "Slot ID (31:24)": bits(dw[3], 31, 24),
    }


def _decode_command_completion_event(dw: List[int]) -> Dict[str, object]:
    """Tables 6-40/6-41/6-42 (figure 6-15): Command Completion Event TRB."""
    ptr_lo = dw[0] & 0xFFFFFFF0
    ptr_hi = dw[1]
    cmd_trb_ptr = (ptr_hi << 32) | ptr_lo
    code = bits(dw[2], 31, 24)
    return {
        "Command TRB Pointer": f"0x{cmd_trb_ptr:016x}",
        "Command Completion Parameter (23:0 of DW2)": bits(dw[2], 23, 0),
        "Completion Code (31:24 of DW2)": f"{code} ({completion_code_name(code)})",
        "VF ID (23:16)": bits(dw[3], 23, 16),
        "Slot ID (31:24)": bits(dw[3], 31, 24),
    }


def _decode_port_status_change_event(dw: List[int]) -> Dict[str, object]:
    """Tables 6-43/6-44/6-45 (figure 6-16): Port Status Change Event TRB."""
    code = bits(dw[2], 31, 24)
    return {
        "Port ID (31:24 of DW0)": bits(dw[0], 31, 24),
        "Completion Code (31:24 of DW2)": f"{code} ({completion_code_name(code)})",
    }


def _decode_bandwidth_request_event(dw: List[int]) -> Dict[str, object]:
    """Tables 6-46/6-47 (figure 6-17): Bandwidth Request Event TRB."""
    code = bits(dw[2], 31, 24)
    return {
        "Completion Code (31:24 of DW2)": f"{code} ({completion_code_name(code)})",
        "Slot ID (31:24 of DW3)": bits(dw[3], 31, 24),
    }


def _decode_doorbell_event(dw: List[int]) -> Dict[str, object]:
    """Tables 6-48/6-49/6-50 (figure 6-18): Doorbell Event TRB."""
    code = bits(dw[2], 31, 24)
    return {
        "DB Reason (4:0 of DW0)": bits(dw[0], 4, 0),
        "Completion Code (31:24 of DW2)": f"{code} ({completion_code_name(code)})",
        "VF ID (23:16 of DW3)": bits(dw[3], 23, 16),
        "Slot ID (31:24 of DW3)": bits(dw[3], 31, 24),
    }


def _decode_host_controller_event(dw: List[int]) -> Dict[str, object]:
    """Tables 6-51/6-52: Host Controller Event TRB."""
    code = bits(dw[2], 31, 24)
    return {
        "Completion Code (31:24 of DW2)": f"{code} ({completion_code_name(code)})",
    }


def _decode_device_notification_event(dw: List[int]) -> Dict[str, object]:
    """Tables 6-53/6-54/6-55: Device Notification Event TRB."""
    notification_type = bits(dw[0], 7, 4)
    data_lo = dw[0] & 0xFFFFFF00  # bits 63:8 actually spans dw0[31:8] and dw1
    device_notification_data = (dw[1] << 24) | (dw[0] >> 8)
    code = bits(dw[2], 31, 24)
    return {
        "Notification Type (7:4 of DW0)": notification_type,
        "Device Notification Data (63:8)": f"0x{device_notification_data:014x}",
        "Completion Code (31:24 of DW2)": f"{code} ({completion_code_name(code)})",
        "Slot ID (31:24 of DW3)": bits(dw[3], 31, 24),
    }


def _decode_mfindex_wrap_event(dw: List[int]) -> Dict[str, object]:
    """Tables 6-56/6-57: MFINDEX Wrap Event TRB."""
    code = bits(dw[2], 31, 24)
    return {
        "Completion Code (31:24 of DW2)": f"{code} ({completion_code_name(code)})",
    }


# ---------------------------------------------------------------------------
# Dispatch table: TRB Type value -> decoder function
# ---------------------------------------------------------------------------

DECODERS: Dict[int, Callable[[List[int]], Dict[str, object]]] = {
    # Transfer TRBs
    TRBType.NORMAL: _decode_normal_trb,
    TRBType.SETUP_STAGE: _decode_setup_stage_trb,
    TRBType.DATA_STAGE: _decode_data_stage_trb,
    TRBType.STATUS_STAGE: _decode_status_stage_trb,
    TRBType.ISOCH: _decode_isoch_trb,
    TRBType.NO_OP_TRANSFER: _decode_no_op_transfer_trb,
    # Command TRBs
    TRBType.NO_OP_COMMAND: _decode_no_op_command,
    TRBType.ENABLE_SLOT_COMMAND: _decode_enable_slot_command,
    TRBType.DISABLE_SLOT_COMMAND: _decode_disable_slot_command,
    TRBType.ADDRESS_DEVICE_COMMAND: _decode_address_device_command,
    TRBType.CONFIGURE_ENDPOINT_COMMAND: _decode_configure_endpoint_command,
    TRBType.EVALUATE_CONTEXT_COMMAND: _decode_evaluate_context_command,
    TRBType.RESET_ENDPOINT_COMMAND: _decode_reset_endpoint_command,
    TRBType.STOP_ENDPOINT_COMMAND: _decode_stop_endpoint_command,
    TRBType.SET_TR_DEQUEUE_POINTER_COMMAND: _decode_set_tr_dequeue_pointer_command,
    TRBType.RESET_DEVICE_COMMAND: _decode_reset_device_command,
    TRBType.FORCE_EVENT_COMMAND: _decode_force_event_command,
    TRBType.SET_LATENCY_TOLERANCE_VALUE_COMMAND: _decode_set_ltv_command,
    TRBType.GET_PORT_BANDWIDTH_COMMAND: _decode_get_port_bandwidth_command,
    TRBType.FORCE_HEADER_COMMAND: _decode_force_header_command,
    TRBType.GET_EXTENDED_PROPERTY_COMMAND: _decode_get_extended_property_command,
    TRBType.SET_EXTENDED_PROPERTY_COMMAND: _decode_set_extended_property_command,
    # Event TRBs
    TRBType.TRANSFER_EVENT: _decode_transfer_event,
    TRBType.COMMAND_COMPLETION_EVENT: _decode_command_completion_event,
    TRBType.PORT_STATUS_CHANGE_EVENT: _decode_port_status_change_event,
    TRBType.BANDWIDTH_REQUEST_EVENT: _decode_bandwidth_request_event,
    TRBType.DOORBELL_EVENT: _decode_doorbell_event,
    TRBType.HOST_CONTROLLER_EVENT: _decode_host_controller_event,
    TRBType.DEVICE_NOTIFICATION_EVENT: _decode_device_notification_event,
    TRBType.MFINDEX_WRAP_EVENT: _decode_mfindex_wrap_event,
}


# ---------------------------------------------------------------------------
# Top-level parse function
# ---------------------------------------------------------------------------

def parse_trb(raw: bytes) -> ParsedTRB:
    """Parse a single 16-byte TRB and return a ParsedTRB with decoded fields.

    Every TRB carries its Cycle bit at bit 0 and its TRB Type at bits 15:10
    of the last DWORD (offset 0Ch), regardless of TRB kind, so those two are
    always extracted generically. The remaining, type-specific fields are
    decoded by dispatching to the matching function in DECODERS.
    """
    dw = to_dwords(raw)
    trb_type_value = bits(dw[3], 15, 10)
    cycle_bit = bit(dw[3], 0)

    result = ParsedTRB(
        raw=raw,
        dwords=dw,
        trb_type_value=trb_type_value,
        trb_type_name=trb_type_name(trb_type_value),
        cycle_bit=cycle_bit,
    )

    decoder = DECODERS.get(trb_type_value)
    if decoder is None:
        result.notes.append(
            "No field decoder implemented for this TRB Type "
            "(it may be a Transfer/Isoch/Link/other Event TRB not yet "
            "covered by this parser)."
        )
        return result

    try:
        result.fields = decoder(dw)
    except Exception as exc:  # keep the parser resilient to malformed input
        result.notes.append(f"Error decoding fields: {exc!r}")

    return result


def parse_trb_stream(raw: bytes) -> List[ParsedTRB]:
    """Parse a buffer containing back-to-back 16-byte TRBs (e.g. a captured
    Command Ring or Event Ring segment)."""
    if len(raw) % TRB_SIZE != 0:
        raise ValueError(
            f"Buffer length {len(raw)} is not a multiple of {TRB_SIZE} bytes"
        )
    return [parse_trb(raw[i:i + TRB_SIZE]) for i in range(0, len(raw), TRB_SIZE)]


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _cli() -> None:
    ap = argparse.ArgumentParser(
        description="Parse xHCI TRBs (16-byte command/event structures) "
                    "from a hex string or a binary file."
    )
    group = ap.add_mutually_exclusive_group(required=True)
    group.add_argument(
        "hex", nargs="?",
        help="Hex string of one or more TRBs, e.g. "
             "'00000000000000000000000001004001'. Whitespace is ignored.",
    )
    group.add_argument(
        "--file", "-f", help="Path to a binary file containing raw TRB bytes."
    )
    args = ap.parse_args()

    if args.file:
        with open(args.file, "rb") as fh:
            raw = fh.read()
    else:
        raw = bytes.fromhex(args.hex.replace(" ", "").replace("\n", ""))

    try:
        trbs = parse_trb_stream(raw)
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        sys.exit(1)

    for i, trb in enumerate(trbs):
        print(f"--- TRB #{i} (offset {i * TRB_SIZE:#06x}) ---")
        print(trb.describe())
        print()


if __name__ == "__main__":
    _cli()
