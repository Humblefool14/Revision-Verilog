"""
USB Port Status Field (wPortStatus) Parser
Parses the 16-bit port status value according to USB specification Table 10-13
"""

class USBPortStatus:
    # Port Link State values
    LINK_STATES = {
        0x00: "U0 State",
        0x01: "U1 State",
        0x02: "U2 State",
        0x03: "U3 State",
        0x04: "eSS.Disabled State",
        0x05: "Rx.Detect State",
        0x06: "eSS.Inactive State",
        0x07: "Polling State",
        0x08: "Recovery State",
        0x09: "Hot Reset State",
        0x0A: "Compliance Mode State",
        0x0B: "Loopback State"
    }
    
    def __init__(self, status_value):
        """
        Initialize parser with a 16-bit port status value
        
        Args:
            status_value: 16-bit integer representing wPortStatus
        """
        self.status_value = status_value & 0xFFFF
        
    def get_bit(self, bit_pos):
        """Extract a single bit from the status value"""
        return (self.status_value >> bit_pos) & 1
    
    def get_bits(self, start_bit, end_bit):
        """Extract a range of bits from the status value"""
        mask = (1 << (end_bit - start_bit + 1)) - 1
        return (self.status_value >> start_bit) & mask
    
    @property
    def port_connection(self):
        """Bit 0: Current Connect Status"""
        return bool(self.get_bit(0))
    
    @property
    def port_enabled(self):
        """Bit 1: Port Enabled/Disabled"""
        return bool(self.get_bit(1))
    
    @property
    def over_current(self):
        """Bit 3: Over-current condition"""
        return bool(self.get_bit(3))
    
    @property
    def port_reset(self):
        """Bit 4: Reset signaling"""
        return bool(self.get_bit(4))
    
    @property
    def port_link_state(self):
        """Bits 5-8: Port Link State"""
        state_value = self.get_bits(5, 8)
        return {
            'value': state_value,
            'description': self.LINK_STATES.get(state_value, "Reserved")
        }
    
    @property
    def port_power(self):
        """Bit 9: Port Power state"""
        return bool(self.get_bit(9))
    
    @property
    def port_speed(self):
        """Bits 10-12: Negotiated speed (only valid for Enhanced SuperSpeed)"""
        speed_value = self.get_bits(10, 12)
        return {
            'value': speed_value,
            'description': "Enhanced SuperSpeed" if speed_value == 0 else "Reserved"
        }
    
    def parse(self):
        """
        Parse the complete port status value
        
        Returns:
            dict: Dictionary containing all parsed fields
        """
        return {
            'raw_value': f"0x{self.status_value:04X}",
            'binary': f"{self.status_value:016b}",
            'fields': {
                'port_connection': {
                    'bit': 0,
                    'value': self.port_connection,
                    'description': "Device present" if self.port_connection else "No device present"
                },
                'port_enabled': {
                    'bit': 1,
                    'value': self.port_enabled,
                    'description': "Port enabled" if self.port_enabled else "Port disabled"
                },
                'over_current': {
                    'bit': 3,
                    'value': self.over_current,
                    'description': "Over-current condition exists" if self.over_current else "No over-current"
                },
                'port_reset': {
                    'bit': 4,
                    'value': self.port_reset,
                    'description': "Reset signaling asserted" if self.port_reset else "Reset signaling not asserted"
                },
                'port_link_state': {
                    'bits': '5-8',
                    'value': self.port_link_state['value'],
                    'hex': f"0x{self.port_link_state['value']:02X}",
                    'description': self.port_link_state['description']
                },
                'port_power': {
                    'bit': 9,
                    'value': self.port_power,
                    'description': "Not in Powered-off state" if self.port_power else "In Powered-off state"
                },
                'port_speed': {
                    'bits': '10-12',
                    'value': self.port_speed['value'],
                    'description': self.port_speed['description']
                }
            }
        }
    
    def __str__(self):
        """String representation of the port status"""
        result = [f"USB Port Status: 0x{self.status_value:04X} (0b{self.status_value:016b})"]
        result.append("-" * 60)
        
        parsed = self.parse()
        fields = parsed['fields']
        
        result.append(f"[Bit 0]  Connection:    {fields['port_connection']['description']}")
        result.append(f"[Bit 1]  Enabled:       {fields['port_enabled']['description']}")
        result.append(f"[Bit 2]  Reserved")
        result.append(f"[Bit 3]  Over-current:  {fields['over_current']['description']}")
        result.append(f"[Bit 4]  Reset:         {fields['port_reset']['description']}")
        result.append(f"[Bit 5-8] Link State:   {fields['port_link_state']['description']} (0x{fields['port_link_state']['value']:X})")
        result.append(f"[Bit 9]  Power:         {fields['port_power']['description']}")
        result.append(f"[Bit 10-12] Speed:      {fields['port_speed']['description']} ({fields['port_speed']['value']})")
        result.append(f"[Bit 13-15] Reserved")
        
        return "\n".join(result)


# Example usage and testing
if __name__ == "__main__":
    # Example 1: Device connected, port enabled, powered, in U0 state
    print("Example 1: Normal operation")
    status1 = USBPortStatus(0x0203)  # Binary: 0000 0010 0000 0011
    print(status1)
    print("\n" + "="*60 + "\n")
    
    # Example 2: Device connected, but port disabled due to over-current
    print("Example 2: Over-current condition")
    status2 = USBPortStatus(0x0209)  # Binary: 0000 0010 0000 1001
    print(status2)
    print("\n" + "="*60 + "\n")
    
    # Example 3: Port in reset state
    print("Example 3: Port reset")
    status3 = USBPortStatus(0x0213)  # Binary: 0000 0010 0001 0011
    print(status3)
    print("\n" + "="*60 + "\n")
    
    # Example 4: Using parse() method for JSON-like output
    print("Example 4: Parsed data structure")
    status4 = USBPortStatus(0x02A3)
    import json
    print(json.dumps(status4.parse(), indent=2))
