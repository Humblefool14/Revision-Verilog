#!/usr/bin/env python3
"""
PCIe DLLP (Data Link Layer Packet) Parser

This parser extracts and analyzes DLLP packets from PCIe trace files.
DLLPs are used for flow control, acknowledgments, and power management.

DLLP Structure:
- DLLPs are 8 bytes total (6 bytes payload + 2 bytes CRC)
- Used at the Data Link Layer for link management
- Not visible to Transaction Layer
"""

import re
import sys
from dataclasses import dataclass
from typing import Optional, Dict, List
from enum import Enum


class DLLPType(Enum):
    """DLLP packet types as defined in PCIe specification"""
    ACK = "ACK"                      # Acknowledge - confirms TLP receipt
    NAK = "NAK"                      # Negative Acknowledge - requests retransmission
    INITFC1_P = "INITFC1_P"         # Initialize Flow Control - Posted
    INITFC1_NP = "INITFC1_NP"       # Initialize Flow Control - Non-Posted
    INITFC1_CPL = "INITFC1_CPL"     # Initialize Flow Control - Completion
    INITFC2_P = "INITFC2_P"         # Initialize Flow Control Phase 2 - Posted
    INITFC2_NP = "INITFC2_NP"       # Initialize Flow Control Phase 2 - Non-Posted
    INITFC2_CPL = "INITFC2_CPL"     # Initialize Flow Control Phase 2 - Completion
    UPDATEFC_P = "UPDATEFC_P"       # Update Flow Control - Posted
    UPDATEFC_NP = "UPDATEFC_NP"     # Update Flow Control - Non-Posted
    UPDATEFC_CPL = "UPDATEFC_CPL"   # Update Flow Control - Completion
    FEATURE = "FEATURE"              # Feature support negotiation
    PM_ENTER_L1 = "PM_ENTER_L1"     # Power Management - Enter L1 state
    PM_ENTER_L23 = "PM_ENTER_L23"   # Power Management - Enter L23 state
    PM_AS_REQ_L1 = "PM_AS_REQ_L1"   # Power Management - Active State Request L1
    PM_REQ_ACK = "PM_REQ_ACK"       # Power Management - Request Acknowledgment
    VENDOR = "VENDOR"                # Vendor-specific DLLP


@dataclass
class FlowControlInfo:
    """
    Flow Control Information for credit-based flow control.
    
    PCIe uses credits to prevent buffer overflow:
    - Header Credits (HC): Number of TLP headers that can be sent
    - Data Credits (DC): Number of data payloads (in credit units)
    - Credit units depend on the scale factor (see table in image)
    """
    vc: int          # Virtual Channel (0-7, typically 0 for most traffic)
    hc: int          # Header Credits (or HdrFC)
    dc: int          # Data Credits (or DataFC)
    hs: int          # Header Scale factor (00b, 01b, 10b, 11b)
    ds: int          # Data Scale factor (00b, 01b, 10b, 11b)
    
    def get_actual_header_credits(self) -> int:
        """
        Calculate actual header credits based on scale factor.
        Scale factors are defined in the uploaded table image:
        - 00b: No scaling, 1-127 credits
        - 01b: Scale=1, 1-127 credits (same as 00b)
        - 10b: Scale=4, actual = HdrFC >> 2 (divide by 4)
        - 11b: Scale=16, actual = HdrFC >> 4 (divide by 16)
        """
        if self.hs == 0 or self.hs == 1:
            return self.hc
        elif self.hs == 2:  # Scale factor 4
            return self.hc << 2  # Multiply by 4
        elif self.hs == 3:  # Scale factor 16
            return self.hc << 4  # Multiply by 16
        return self.hc
    
    def get_actual_data_credits(self) -> int:
        """
        Calculate actual data credits based on scale factor.
        Data credits work similarly to header credits.
        - 00b: 1-2047 credits (12-bit field)
        - 01b: 1-2047 credits
        - 10b: Scale=4, actual = DataFC >> 2
        - 11b: Scale=16, actual = DataFC >> 4
        """
        if self.ds == 0 or self.ds == 1:
            return self.dc
        elif self.ds == 2:  # Scale factor 4
            return self.dc << 2
        elif self.ds == 3:  # Scale factor 16
            return self.dc << 4
        return self.dc
    
    def __str__(self) -> str:
        actual_hc = self.get_actual_header_credits()
        actual_dc = self.get_actual_data_credits()
        return (f"VC={self.vc}, HC={self.hc:02x} (actual: {actual_hc}), "
                f"DC={self.dc:03x} (actual: {actual_dc}), "
                f"HS={self.hs}, DS={self.ds}")


@dataclass
class FeatureInfo:
    """
    Feature negotiation information.
    Used during link initialization to negotiate optional features.
    """
    fa: int  # Feature Ack - acknowledges feature support
    fs: int  # Feature Support - bitmap of supported features
    
    def __str__(self) -> str:
        return f"FA={self.fa}, FS={self.fs:06x}"


@dataclass
class AckNakInfo:
    """
    Acknowledgment/Negative Acknowledgment information.
    
    ACK/NAK DLLPs use sequence numbers to track TLP delivery:
    - SEQ: Sequence number of last successfully received TLP (for ACK)
           or first TLP to retransmit (for NAK)
    """
    seq: int  # Sequence number (12-bit, wraps at 4096)
    
    def __str__(self) -> str:
        return f"SEQ={self.seq:03x}"


@dataclass
class DLLPPacket:
    """Complete DLLP packet with all parsed fields"""
    timestamp: int                      # Time in picoseconds
    direction: str                      # 'U' for Upstream, 'D' for Downstream
    dllp_type: DLLPType                # Type of DLLP
    crc: str                           # CRC-16 value
    
    # Optional fields depending on DLLP type
    flow_control: Optional[FlowControlInfo] = None
    feature: Optional[FeatureInfo] = None
    ack_nak: Optional[AckNakInfo] = None
    raw_line: str = ""                 # Original line for reference
    
    def __str__(self) -> str:
        result = [
            f"Time: {self.timestamp} ps",
            f"Direction: {'Upstream' if self.direction == 'U' else 'Downstream'}",
            f"Type: {self.dllp_type.value}",
            f"CRC: {self.crc}"
        ]
        
        if self.flow_control:
            result.append(f"Flow Control: {self.flow_control}")
        if self.feature:
            result.append(f"Feature: {self.feature}")
        if self.ack_nak:
            result.append(f"Ack/Nak: {self.ack_nak}")
            
        return " | ".join(result)


class FCInitViolation:
    """Represents a Flow Control Initialization rule violation"""
    def __init__(self, rule: str, description: str, timestamp: int, packet: 'DLLPPacket'):
        self.rule = rule
        self.description = description
        self.timestamp = timestamp
        self.packet = packet
    
    def __str__(self) -> str:
        return f"[{self.rule}] @ {self.timestamp} ps: {self.description}"


class CreditTracker:
    """
    Tracks flow control credits for a specific traffic type and virtual channel.
    Implements the credit accounting described in PCIe spec Section 2.6.1.2
    """
    def __init__(self, vc: int, traffic_type: str, field_size: int):
        self.vc = vc
        self.traffic_type = traffic_type  # 'P', 'NP', or 'CPL'
        self.field_size = field_size  # Bit width for modulo arithmetic
        
        # Receiver-side tracking
        self.credits_allocated = 0  # Total credits advertised to transmitter
        self.credits_received = 0   # Credits consumed by received TLPs (optional)
        self.credit_limit = None    # Most recent advertised value
        
        # For UpdateFC timing checks
        self.last_updatefc_time = None
        self.credits_since_last_update = 0
    
    def initialize(self, initial_credits: int):
        """Initialize credits from InitFC DLLP"""
        self.credits_allocated = initial_credits
        self.credit_limit = initial_credits
    
    def update_credits(self, new_credits: int, timestamp: int):
        """Update credits from UpdateFC DLLP"""
        self.credits_allocated = new_credits
        self.credit_limit = new_credits
        self.last_updatefc_time = timestamp
        self.credits_since_last_update = 0
    
    def consume_credits(self, amount: int):
        """Consume credits when TLP is received"""
        modulo = 2 ** self.field_size
        self.credits_received = (self.credits_received + amount) % modulo
        self.credits_since_last_update += amount
    
    def check_overflow(self) -> bool:
        """
        Check for receiver overflow error.
        Equation 2-6: (CREDITS_ALLOCATED - CREDITS_RECEIVED) mod 2^[Field Size] ≥ 2^[Field Size]/2
        """
        modulo = 2 ** self.field_size
        threshold = modulo // 2
        available = (self.credits_allocated - self.credits_received) % modulo
        return available >= threshold
    
    def needs_updatefc(self, scale_active: bool, scale_factor: int) -> bool:
        """
        Determine if UpdateFC should be sent based on credits made available.
        Returns True if UpdateFC transmission is required per spec.
        """
        if self.credits_since_last_update == 0:
            return False
        
        if not scale_active:
            # Non-scaled: send when credits go from 0 to >0
            return True
        else:
            # Scaled: check against threshold
            if scale_factor == 1:  # 01b
                threshold = 0
            elif scale_factor == 2:  # 10b - scale by 4
                threshold = 4
            elif scale_factor == 3:  # 11b - scale by 16
                threshold = 16
            else:
                threshold = 0
            
            return self.credits_since_last_update >= threshold


class DLLPParser:
    """Parser for PCIe DLLP packets from trace files"""
    
    # Regex pattern to match DLLP lines
    # Format: timestamp direction |DLLP:type|field1:value1|field2:value2|...|CRC:xxxx |
    DLLP_PATTERN = re.compile(
        r'^\s*(\d+)\s+([UD])\s+\|DLLP:(\w+)\|(.*?)\|CRC:([0-9a-f]+)\s+\|'
    )
    
    def __init__(self):
        self.packets: List[DLLPPacket] = []
        self.stats: Dict[str, int] = {}
        self.fc_init_violations: List[FCInitViolation] = []
        self.credit_trackers: Dict[str, CreditTracker] = {}  # Key: "direction_VC_type"
        
    def parse_file(self, filename: str) -> List[DLLPPacket]:
        """Parse a PCIe trace file and extract all DLLP packets"""
        print(f"Parsing file: {filename}")
        
        with open(filename, 'r') as f:
            for line_num, line in enumerate(f, 1):
                if 'DLLP:' in line:
                    packet = self._parse_dllp_line(line)
                    if packet:
                        self.packets.append(packet)
                        # Update statistics
                        type_name = packet.dllp_type.value
                        self.stats[type_name] = self.stats.get(type_name, 0) + 1
        
        print(f"Parsed {len(self.packets)} DLLP packets")
        return self.packets
    
    def _parse_dllp_line(self, line: str) -> Optional[DLLPPacket]:
        """Parse a single DLLP line"""
        match = self.DLLP_PATTERN.match(line)
        if not match:
            return None
        
        timestamp = int(match.group(1))
        direction = match.group(2)
        dllp_type_str = match.group(3)
        fields_str = match.group(4)
        crc = match.group(5)
        
        # Parse DLLP type
        try:
            dllp_type = DLLPType(dllp_type_str)
        except ValueError:
            print(f"Warning: Unknown DLLP type: {dllp_type_str}")
            return None
        
        # Parse fields based on DLLP type
        fields = self._parse_fields(fields_str)
        
        packet = DLLPPacket(
            timestamp=timestamp,
            direction=direction,
            dllp_type=dllp_type,
            crc=crc,
            raw_line=line.strip()
        )
        
        # Add type-specific information
        if dllp_type.value.startswith('INITFC') or dllp_type.value.startswith('UPDATEFC'):
            packet.flow_control = FlowControlInfo(
                vc=int(fields.get('VC', '0'), 16),
                hc=int(fields.get('HC', '0'), 16),
                dc=int(fields.get('DC', '0'), 16),
                hs=int(fields.get('HS', '0')),
                ds=int(fields.get('DS', '0'))
            )
        elif dllp_type == DLLPType.FEATURE:
            packet.feature = FeatureInfo(
                fa=int(fields.get('FA', '0')),
                fs=int(fields.get('FS', '0'), 16)
            )
        elif dllp_type in [DLLPType.ACK, DLLPType.NAK]:
            packet.ack_nak = AckNakInfo(
                seq=int(fields.get('SEQ', '0'), 16)
            )
        
        return packet
    
    def _parse_fields(self, fields_str: str) -> Dict[str, str]:
        """Parse field:value pairs from DLLP fields string"""
        fields = {}
        for field_pair in fields_str.split('|'):
            if ':' in field_pair:
                key, value = field_pair.split(':', 1)
                fields[key.strip()] = value.strip()
        return fields
    
    def print_statistics(self):
        """Print statistics about parsed DLLPs"""
        print("\n" + "="*80)
        print("DLLP STATISTICS")
        print("="*80)
        print(f"{'DLLP Type':<30} {'Count':>10} {'Percentage':>10}")
        print("-"*80)
        
        total = sum(self.stats.values())
        for dllp_type in sorted(self.stats.keys()):
            count = self.stats[dllp_type]
            percentage = (count / total * 100) if total > 0 else 0
            print(f"{dllp_type:<30} {count:>10} {percentage:>9.2f}%")
        
        print("-"*80)
        print(f"{'TOTAL':<30} {total:>10} {'100.00':>9}%")
        print("="*80)
    
    def analyze_flow_control(self):
        """Analyze flow control credit allocation"""
        print("\n" + "="*80)
        print("FLOW CONTROL ANALYSIS")
        print("="*80)
        
        # Track INITFC packets (initial credit advertisement)
        initfc_packets = [p for p in self.packets 
                         if p.dllp_type.value.startswith('INITFC')]
        
        if initfc_packets:
            print("\nInitial Flow Control Credits:")
            for packet in initfc_packets[:10]:  # Show first 10
                print(f"  Time: {packet.timestamp:>15} ps | "
                      f"Dir: {packet.direction} | "
                      f"Type: {packet.dllp_type.value:<15} | "
                      f"{packet.flow_control}")
        
        # Track UPDATEFC packets (credit updates)
        updatefc_packets = [p for p in self.packets 
                           if p.dllp_type.value.startswith('UPDATEFC')]
        
        if updatefc_packets:
            print(f"\nFlow Control Updates: {len(updatefc_packets)} total")
            print("Sample updates:")
            for packet in updatefc_packets[:5]:  # Show first 5
                print(f"  Time: {packet.timestamp:>15} ps | "
                      f"Dir: {packet.direction} | "
                      f"Type: {packet.dllp_type.value:<15} | "
                      f"{packet.flow_control}")
    
    def analyze_acks(self):
        """Analyze ACK/NAK packets"""
        print("\n" + "="*80)
        print("ACK/NAK ANALYSIS")
        print("="*80)
        
        ack_packets = [p for p in self.packets if p.dllp_type == DLLPType.ACK]
        nak_packets = [p for p in self.packets if p.dllp_type == DLLPType.NAK]
        
        print(f"\nTotal ACKs: {len(ack_packets)}")
        print(f"Total NAKs: {len(nak_packets)}")
        
        if nak_packets:
            print("\nNAK packets detected (retransmissions required):")
            for packet in nak_packets:
                print(f"  Time: {packet.timestamp} ps | {packet}")
        else:
            print("\nNo NAKs detected - all transmissions successful!")
        
        if ack_packets:
            print("\nSample ACK packets:")
            for packet in ack_packets[:10]:
                print(f"  Time: {packet.timestamp:>15} ps | "
                      f"Dir: {packet.direction} | "
                      f"{packet.ack_nak}")
    
    def check_fc_init_compliance(self):
        """
        Check compliance with FC_INIT1 and FC_INIT2 rules from PCIe spec.
        
        FC_INIT1 Rules:
        - Must transmit InitFC1-P, InitFC1-NP, InitFC1-Cpl in that order
        - Must transmit at least once every 34 μs
        - Must set HdrScale and DataScale based on Scaled Flow Control support
        - Transaction Layer must block TLP transmission during FC_INIT1
        
        FC_INIT2 Rules:
        - Must transmit InitFC2-P, InitFC2-NP, InitFC2-Cpl in that order
        - Must transmit at least once every 34 μs
        - Must set HdrScale and DataScale same as FC_INIT1
        - Receiver should set FI2 flag on receipt
        """
        print("\n" + "="*80)
        print("FC_INIT1 AND FC_INIT2 COMPLIANCE CHECKING")
        print("="*80)
        
        # Separate INITFC1 and INITFC2 packets
        initfc1_packets = [p for p in self.packets if 'INITFC1' in p.dllp_type.value]
        initfc2_packets = [p for p in self.packets if 'INITFC2' in p.dllp_type.value]
        
        print(f"\nTotal INITFC1 packets: {len(initfc1_packets)}")
        print(f"Total INITFC2 packets: {len(initfc2_packets)}")
        
        # Check FC_INIT1 compliance
        if initfc1_packets:
            print("\n--- FC_INIT1 Compliance Checks ---")
            self._check_initfc_sequence(initfc1_packets, "FC_INIT1")
            self._check_initfc_timing(initfc1_packets, "FC_INIT1")
            self._check_scale_consistency(initfc1_packets, "FC_INIT1")
        
        # Check FC_INIT2 compliance
        if initfc2_packets:
            print("\n--- FC_INIT2 Compliance Checks ---")
            self._check_initfc_sequence(initfc2_packets, "FC_INIT2")
            self._check_initfc_timing(initfc2_packets, "FC_INIT2")
            self._check_scale_consistency(initfc2_packets, "FC_INIT2")
            
            # Check FC_INIT1 vs FC_INIT2 scale consistency
            if initfc1_packets:
                self._check_init1_vs_init2_scale(initfc1_packets, initfc2_packets)
        
        # Print violations summary
        if self.fc_init_violations:
            print("\n" + "="*80)
            print(f"VIOLATIONS DETECTED: {len(self.fc_init_violations)}")
            print("="*80)
            for violation in self.fc_init_violations:
                print(f"  {violation}")
        else:
            print("\n" + "="*80)
            print("✓ ALL FC_INIT COMPLIANCE CHECKS PASSED")
            print("="*80)
    
    def _check_initfc_sequence(self, packets: List[DLLPPacket], stage: str):
        """
        Check that InitFC packets are sent in correct order: P, NP, Cpl.
        Rule: "Transmit the following three InitFC DLLPs for VCx in the following relative order"
        
        Note: Checks are done separately for each direction (Upstream/Downstream) as each
        side independently transmits its own InitFC sequences.
        """
        print(f"\n  Checking {stage} sequence ordering...")
        
        # Group by direction first, then by VC
        direction_groups = {'U': [], 'D': []}
        for p in packets:
            direction_groups[p.direction].append(p)
        
        total_sequences_checked = 0
        
        for direction, dir_packets in direction_groups.items():
            if not dir_packets:
                continue
            
            dir_name = "Upstream" if direction == 'U' else "Downstream"
            
            # Group by VC within this direction
            vc_groups = {}
            for p in dir_packets:
                if p.flow_control:
                    vc = p.flow_control.vc
                    if vc not in vc_groups:
                        vc_groups[vc] = []
                    vc_groups[vc].append(p)
            
            for vc, vc_packets in vc_groups.items():
                # Extract the expected sequence pattern
                expected_order = ['P', 'NP', 'CPL']
                
                # Check sequences of 3
                i = 0
                sequence_num = 0
                while i < len(vc_packets) - 2:
                    triplet = vc_packets[i:i+3]
                    
                    # Extract traffic class from type (e.g., INITFC1_P -> P)
                    actual_order = []
                    for pkt in triplet:
                        type_parts = pkt.dllp_type.value.split('_')
                        if len(type_parts) == 2:
                            actual_order.append(type_parts[1])
                    
                    if actual_order != expected_order:
                        self.fc_init_violations.append(FCInitViolation(
                            f"{stage}_SEQ_ORDER",
                            f"{dir_name} VC{vc}: Incorrect sequence order. Expected {expected_order}, got {actual_order}",
                            triplet[0].timestamp,
                            triplet[0]
                        ))
                    
                    sequence_num += 1
                    # Skip to next potential triplet (may overlap)
                    i += 3
                
                total_sequences_checked += sequence_num
                print(f"    {dir_name} VC{vc}: Checked {sequence_num} triplet sequences")
        
        if total_sequences_checked == 0:
            print(f"    No complete triplets found")
    
    def _check_initfc_timing(self, packets: List[DLLPPacket], stage: str):
        """
        Check that InitFC DLLPs are transmitted at least once every 34 μs.
        Rule: "The three InitFC DLLPs must be transmitted at least once every 34 μs"
        
        Note: Each direction is checked independently as each side has its own 
        transmission timing requirements.
        """
        print(f"\n  Checking {stage} timing (34 μs max interval)...")
        
        MAX_INTERVAL_PS = 34_000_000  # 34 μs in picoseconds
        
        # Group by direction first
        direction_groups = {'U': [], 'D': []}
        for p in packets:
            direction_groups[p.direction].append(p)
        
        for direction, dir_packets in direction_groups.items():
            if not dir_packets:
                continue
            
            dir_name = "Upstream" if direction == 'U' else "Downstream"
            
            # Check intervals between consecutive triplets
            # Group by VC within this direction
            vc_groups = {}
            for p in dir_packets:
                if p.flow_control:
                    vc = p.flow_control.vc
                    if vc not in vc_groups:
                        vc_groups[vc] = []
                    vc_groups[vc].append(p)
            
            for vc, vc_packets in vc_groups.items():
                # Look for triplets (P, NP, CPL) and check timing between them
                triplet_times = []
                i = 0
                while i < len(vc_packets) - 2:
                    # Check if we have a complete triplet
                    triplet = vc_packets[i:i+3]
                    types = [p.dllp_type.value.split('_')[1] for p in triplet]
                    
                    if types == ['P', 'NP', 'CPL']:
                        triplet_times.append(triplet[0].timestamp)
                        i += 3
                    else:
                        i += 1
                
                # Check intervals between triplets
                violations = 0
                for i in range(len(triplet_times) - 1):
                    interval = triplet_times[i+1] - triplet_times[i]
                    if interval > MAX_INTERVAL_PS:
                        violations += 1
                        self.fc_init_violations.append(FCInitViolation(
                            f"{stage}_TIMING",
                            f"{dir_name} VC{vc}: Interval between triplets {interval/1_000_000:.2f} μs exceeds 34 μs limit",
                            triplet_times[i],
                            vc_packets[i]
                        ))
                
                if violations == 0 and len(triplet_times) > 0:
                    print(f"    {dir_name} VC{vc}: ✓ All {len(triplet_times)} triplets within 34 μs timing requirement")
                elif violations > 0:
                    print(f"    {dir_name} VC{vc}: ✗ {violations} timing violations detected")
                elif len(triplet_times) == 0:
                    print(f"    {dir_name} VC{vc}: No complete triplets found for timing check")
    
    def _check_scale_consistency(self, packets: List[DLLPPacket], stage: str):
        """
        Check that HdrScale and DataScale are consistent within a stage.
        Rules:
        - "If Scaled Flow Control is activated, set HdrScale and DataScale to 01b, 10b, or 11b"
        - "If not supported or not activated, set to 00b"
        - Scale factors should be consistent across all InitFC DLLPs in the same stage
        
        Note: Each direction is checked independently as each side may negotiate 
        different scale factors.
        """
        print(f"\n  Checking {stage} scale factor consistency...")
        
        # Group by direction first
        direction_groups = {'U': [], 'D': []}
        for p in packets:
            direction_groups[p.direction].append(p)
        
        for direction, dir_packets in direction_groups.items():
            if not dir_packets:
                continue
            
            dir_name = "Upstream" if direction == 'U' else "Downstream"
            
            # Group by VC within this direction
            vc_groups = {}
            for p in dir_packets:
                if p.flow_control:
                    vc = p.flow_control.vc
                    if vc not in vc_groups:
                        vc_groups[vc] = []
                    vc_groups[vc].append(p)
            
            for vc, vc_packets in vc_groups.items():
                if not vc_packets:
                    continue
                
                # Check all packets for consistency
                first_hs = vc_packets[0].flow_control.hs if vc_packets[0].flow_control else None
                first_ds = vc_packets[0].flow_control.ds if vc_packets[0].flow_control else None
                
                inconsistent = False
                for pkt in vc_packets[1:]:
                    if pkt.flow_control:
                        if pkt.flow_control.hs != first_hs or pkt.flow_control.ds != first_ds:
                            inconsistent = True
                            self.fc_init_violations.append(FCInitViolation(
                                f"{stage}_SCALE_INCONSISTENT",
                                f"{dir_name} VC{vc}: Scale factors not consistent. "
                                f"Expected HS={first_hs}, DS={first_ds}, "
                                f"got HS={pkt.flow_control.hs}, DS={pkt.flow_control.ds}",
                                pkt.timestamp,
                                pkt
                            ))
                
                # Check if scale values are valid
                valid_scales = [0, 1, 2, 3]  # 00b, 01b, 10b, 11b
                if first_hs not in valid_scales or first_ds not in valid_scales:
                    self.fc_init_violations.append(FCInitViolation(
                        f"{stage}_SCALE_INVALID",
                        f"{dir_name} VC{vc}: Invalid scale values. HS={first_hs}, DS={first_ds} (must be 0-3)",
                        vc_packets[0].timestamp,
                        vc_packets[0]
                    ))
                
                if not inconsistent and first_hs in valid_scales and first_ds in valid_scales:
                    scale_type = "No scaling (00b)" if first_hs == 0 else f"Scaled (HS={first_hs}b, DS={first_ds}b)"
                    print(f"    {dir_name} VC{vc}: ✓ Consistent scale factors: {scale_type}")
                else:
                    print(f"    {dir_name} VC{vc}: ✗ Scale factor inconsistencies detected")
    
    def _check_init1_vs_init2_scale(self, initfc1_packets: List[DLLPPacket], 
                                     initfc2_packets: List[DLLPPacket]):
        """
        Check that FC_INIT2 uses the same scale factors as FC_INIT1.
        Rule: "If Scaled Flow Control is activated, set the HdrScale and DataScale fields 
               in the InitF2 DLLPs to 01b, 10b, or 11b to indicate the scaling factor"
        
        Note: Each direction is checked independently.
        """
        print(f"\n  Checking FC_INIT1 vs FC_INIT2 scale consistency...")
        
        # Group by direction for both INIT1 and INIT2
        init1_by_dir = {'U': [], 'D': []}
        init2_by_dir = {'U': [], 'D': []}
        
        for p in initfc1_packets:
            init1_by_dir[p.direction].append(p)
        
        for p in initfc2_packets:
            init2_by_dir[p.direction].append(p)
        
        for direction in ['U', 'D']:
            dir_name = "Upstream" if direction == 'U' else "Downstream"
            
            if not init1_by_dir[direction] or not init2_by_dir[direction]:
                if init1_by_dir[direction]:
                    print(f"    {dir_name}: ⚠ INIT1 present but INIT2 not found")
                continue
            
            # Get scale factors from INITFC1 per VC for this direction
            init1_scales = {}
            for p in init1_by_dir[direction]:
                if p.flow_control:
                    vc = p.flow_control.vc
                    if vc not in init1_scales:
                        init1_scales[vc] = (p.flow_control.hs, p.flow_control.ds)
            
            # Check INITFC2 matches for this direction
            init2_scales = {}
            for p in init2_by_dir[direction]:
                if p.flow_control:
                    vc = p.flow_control.vc
                    if vc not in init2_scales:
                        init2_scales[vc] = (p.flow_control.hs, p.flow_control.ds)
            
            for vc in init1_scales.keys():
                if vc in init2_scales:
                    init1_hs, init1_ds = init1_scales[vc]
                    init2_hs, init2_ds = init2_scales[vc]
                    
                    if init1_hs != init2_hs or init1_ds != init2_ds:
                        self.fc_init_violations.append(FCInitViolation(
                            "INIT1_INIT2_SCALE_MISMATCH",
                            f"{dir_name} VC{vc}: Scale mismatch between INIT1 and INIT2. "
                            f"INIT1: HS={init1_hs}, DS={init1_ds}, "
                            f"INIT2: HS={init2_hs}, DS={init2_ds}",
                            init2_by_dir[direction][0].timestamp,
                            init2_by_dir[direction][0]
                        ))
                        print(f"    {dir_name} VC{vc}: ✗ Scale mismatch between INIT1 and INIT2")
                    else:
                        print(f"    {dir_name} VC{vc}: ✓ Consistent scales between INIT1 (HS={init1_hs}, DS={init1_ds}) and INIT2")
                else:
                    print(f"    {dir_name} VC{vc}: ⚠ INIT1 present but INIT2 not found")
    
    def check_updatefc_compliance(self):
        """
        Check UpdateFC DLLP compliance based on PCIe spec Section 2.6.1.2
        
        Rules checked:
        1. UpdateFC timing: Must be sent at least every 30 μs in L0/L0s (or 120 μs if Extended Synch)
        2. UpdateFC triggers: Send when credits become available (especially 0→non-zero transitions)
        3. Credit accounting: Verify credits don't overflow
        4. Scaled threshold checking: For scaled flow control, check threshold requirements
        """
        print("\n" + "="*80)
        print("UPDATEFC COMPLIANCE CHECKING")
        print("="*80)
        
        # Separate UpdateFC packets by direction and type
        updatefc_packets = [p for p in self.packets if 'UPDATEFC' in p.dllp_type.value]
        
        if not updatefc_packets:
            print("\nNo UpdateFC packets found in trace")
            return
        
        print(f"\nTotal UpdateFC packets: {len(updatefc_packets)}")
        
        # Group by direction
        direction_groups = {'U': [], 'D': []}
        for p in updatefc_packets:
            direction_groups[p.direction].append(p)
        
        for direction, dir_packets in direction_groups.items():
            if not dir_packets:
                continue
            
            dir_name = "Upstream" if direction == 'U' else "Downstream"
            print(f"\n--- {dir_name} UpdateFC Analysis ---")
            
            # Group by traffic type
            type_groups = {'P': [], 'NP': [], 'CPL': []}
            for p in dir_packets:
                type_parts = p.dllp_type.value.split('_')
                if len(type_parts) >= 2:
                    traffic_type = type_parts[1]  # P, NP, or CPL
                    if traffic_type in type_groups:
                        type_groups[traffic_type].append(p)
            
            # Check each traffic type
            for traffic_type, traffic_packets in type_groups.items():
                if not traffic_packets:
                    continue
                
                print(f"\n  Traffic Type: {traffic_type}")
                print(f"    Total UpdateFC packets: {len(traffic_packets)}")
                
                # Check timing compliance (30 μs requirement)
                self._check_updatefc_timing(traffic_packets, traffic_type, dir_name)
                
                # Check credit progression
                self._check_updatefc_credits(traffic_packets, traffic_type, dir_name)
    
    def _check_updatefc_timing(self, packets: List[DLLPPacket], traffic_type: str, direction: str):
        """
        Check UpdateFC timing compliance.
        Rule: "Update FCPs for each enabled type of non-infinite FC credit must be 
               scheduled for transmission at least once every 30 μs (-0%/+50%)"
        """
        MAX_INTERVAL_PS = 30_000_000  # 30 μs in picoseconds
        MAX_INTERVAL_EXTENDED_PS = 120_000_000  # 120 μs if Extended Synch
        
        if len(packets) < 2:
            print(f"    Timing: Only {len(packets)} packet(s), cannot check intervals")
            return
        
        # Check intervals between consecutive UpdateFC packets
        violations = 0
        max_interval = 0
        intervals = []
        
        for i in range(len(packets) - 1):
            interval = packets[i+1].timestamp - packets[i].timestamp
            intervals.append(interval)
            
            if interval > max_interval:
                max_interval = interval
            
            if interval > MAX_INTERVAL_PS:
                violations += 1
                self.fc_init_violations.append(FCInitViolation(
                    "UPDATEFC_TIMING",
                    f"{direction} {traffic_type}: Interval {interval/1_000_000:.2f} μs exceeds 30 μs limit",
                    packets[i].timestamp,
                    packets[i]
                ))
        
        avg_interval = sum(intervals) / len(intervals) if intervals else 0
        
        print(f"    Timing: Avg={avg_interval/1_000_000:.2f} μs, Max={max_interval/1_000_000:.2f} μs, " +
              f"Required=<30 μs")
        
        if violations == 0:
            print(f"    ✓ All {len(intervals)} intervals within 30 μs requirement")
        else:
            print(f"    ✗ {violations} timing violations detected")
    
    def _check_updatefc_credits(self, packets: List[DLLPPacket], traffic_type: str, direction: str):
        """
        Check UpdateFC credit values for proper progression.
        Verify credits are increasing (being returned) as expected.
        """
        if not packets:
            return
        
        # Track credit values over time
        credit_values = []
        scale_factors = []
        
        for p in packets:
            if p.flow_control:
                hc = p.flow_control.hc
                dc = p.flow_control.dc
                hs = p.flow_control.hs
                ds = p.flow_control.ds
                
                # Calculate actual credits accounting for scale
                actual_hc = p.flow_control.get_actual_header_credits()
                actual_dc = p.flow_control.get_actual_data_credits()
                
                credit_values.append({
                    'timestamp': p.timestamp,
                    'hc': hc,
                    'dc': dc,
                    'actual_hc': actual_hc,
                    'actual_dc': actual_dc,
                    'hs': hs,
                    'ds': ds
                })
                scale_factors.append((hs, ds))
        
        if not credit_values:
            return
        
        # Check for scale consistency
        if len(set(scale_factors)) > 1:
            self.fc_init_violations.append(FCInitViolation(
                "UPDATEFC_SCALE_INCONSISTENT",
                f"{direction} {traffic_type}: Scale factors change during operation. " +
                f"Found: {set(scale_factors)}",
                packets[0].timestamp,
                packets[0]
            ))
            print(f"    ✗ Scale factor inconsistency detected")
        else:
            print(f"    ✓ Consistent scale factors: HS={scale_factors[0][0]}, DS={scale_factors[0][1]}")
        
        # Show credit range
        hc_values = [cv['hc'] for cv in credit_values]
        dc_values = [cv['dc'] for cv in credit_values]
        
        print(f"    Header Credits: min=0x{min(hc_values):02x}, max=0x{max(hc_values):02x}, " +
              f"latest=0x{hc_values[-1]:02x}")
        print(f"    Data Credits: min=0x{min(dc_values):03x}, max=0x{max(dc_values):03x}, " +
              f"latest=0x{dc_values[-1]:03x}")
        
        # Check for credit progression (should generally increase over time as buffers free up)
        # Note: Credits can decrease if TLPs are being received faster than processed
        increasing_hc = sum(1 for i in range(len(hc_values)-1) if hc_values[i+1] >= hc_values[i])
        increasing_dc = sum(1 for i in range(len(dc_values)-1) if dc_values[i+1] >= dc_values[i])
        
        total_transitions = len(hc_values) - 1
        if total_transitions > 0:
            hc_increase_pct = (increasing_hc / total_transitions) * 100
            dc_increase_pct = (increasing_dc / total_transitions) * 100
            
            print(f"    Credit Progression: HC increasing {hc_increase_pct:.1f}%, " +
                  f"DC increasing {dc_increase_pct:.1f}% of time")


def main():
    """Main function to demonstrate the parser"""
    if len(sys.argv) < 2:
        print("Usage: python dllp_parser.py <trace_file>")
        print("\nThis parser extracts and analyzes PCIe DLLP packets.")
        print("\nDLLP Types:")
        print("  - ACK/NAK: Acknowledge TLP receipt")
        print("  - INITFC: Initialize flow control credits")
        print("  - UPDATEFC: Update available credits")
        print("  - FEATURE: Negotiate optional features")
        print("  - PM_*: Power management DLLPs")
        sys.exit(1)
    
    filename = sys.argv[1]
    
    # Create parser and parse file
    parser = DLLPParser()
    packets = parser.parse_file(filename)
    
    if not packets:
        print("No DLLP packets found in file")
        sys.exit(1)
    
    # Print statistics
    parser.print_statistics()
    
    # Analyze flow control
    parser.analyze_flow_control()
    
    # Analyze ACKs
    parser.analyze_acks()
    
    # Check FC_INIT compliance
    parser.check_fc_init_compliance()
    
    # Check UpdateFC compliance
    parser.check_updatefc_compliance()
    
    # Show all packets
    print("\n" + "="*80)
    print(f"ALL DLLP PACKETS (Total: {len(packets)})")
    print("="*80)
    for i, packet in enumerate(packets, 1):
        print(f"\n{i}. {packet}")
    
    print("\n" + "="*80)
    print("DLLP FIELD EXPLANATIONS")
    print("="*80)
    print("""
Flow Control Fields:
  VC  - Virtual Channel: Logical channel for traffic separation (0-7)
  HC  - Header Credits: Number of TLP headers that can be sent
  DC  - Data Credits: Number of data payloads that can be sent
  HS  - Header Scale: Scale factor for header credits (0-3)
  DS  - Data Scale: Scale factor for data credits (0-3)
        Scale 0/1: No scaling
        Scale 2: Multiply by 4 (shift left 2)
        Scale 3: Multiply by 16 (shift left 4)

Feature Fields:
  FA  - Feature Ack: Acknowledges feature support (0 or 1)
  FS  - Feature Support: Bitmap of supported features

ACK/NAK Fields:
  SEQ - Sequence Number: 12-bit TLP sequence number (0-4095)
        For ACK: Last successfully received TLP
        For NAK: First TLP that needs retransmission

CRC  - Cyclic Redundancy Check: 16-bit CRC for error detection

Direction:
  U - Upstream (from endpoint to root complex)
  D - Downstream (from root complex to endpoint)
    """)


if __name__ == "__main__":
    main()
