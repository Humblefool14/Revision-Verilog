#!/usr/bin/env python3
import gzip
import re
import sys
import os

def parse_def_pins(filename):
    """
    Parse a DEF file (gzipped) and extract pins categorized by direction
    """
    # Initialize pin lists
    input_pins = []
    output_pins = []
    inout_pins = []
    
    # Check if file exists
    if not os.path.exists(filename):
        print(f"Error: File '{filename}' not found")
        return
    
    # Open the gzipped file
    try:
        with gzip.open(filename, 'rt') as f:
            content = f.read()
    except gzip.BadGzipFile:
        print(f"Error: '{filename}' is not a valid gzip file")
        return
    except UnicodeDecodeError:
        print(f"Error: Unable to decode '{filename}' as text")
        return
    
    # Find the PINS section using regex
    pins_section_pattern = re.compile(r'PINS\s+.*?END\s+PINS', re.DOTALL)
    pins_section_match = pins_section_pattern.search(content)
    
    if not pins_section_match:
        print(f"No PINS...END PINS section found in {filename}")
        return
    
    pins_section = pins_section_match.group(0)
    
    # Find individual pin definitions
    pin_pattern = re.compile(r'-\s+(\S+).*?DIRECTION\s+(\S+)', re.DOTALL)
    pin_matches = pin_pattern.finditer(pins_section)
    
    # Categorize pins by direction
    for match in pin_matches:
        pin_name = match.group(1)
        direction = match.group(2)
        
        if direction == "INPUT":
            input_pins.append(pin_name)
        elif direction == "OUTPUT":
            output_pins.append(pin_name)
        elif direction == "INOUT":
            inout_pins.append(pin_name)
    
    # Print results
    print("Pin Analysis Results:")
    print("-" * 50)
    
    print("\nINPUT PINS:")
    if input_pins:
        for pin in sorted(input_pins):
            print(f"  - {pin}")
    else:
        print("  None found")
    
    print("\nOUTPUT PINS:")
    if output_pins:
        for pin in sorted(output_pins):
            print(f"  - {pin}")
    else:
        print("  None found")
    
    print("\nINOUT PINS:")
    if inout_pins:
        for pin in sorted(inout_pins):
            print(f"  - {pin}")
    else:
        print("  None found")
    
    # Print summary counts
    print("\nSUMMARY:")
    print(f"  Input pins: {len(input_pins)}")
    print(f"  Output pins: {len(output_pins)}")
    print(f"  Inout pins: {len(inout_pins)}")
    print(f"  Total pins: {len(input_pins) + len(output_pins) + len(inout_pins)}")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python parse_def_pins.py <def_file.def.gz>")
        sys.exit(1)
    
    parse_def_pins(sys.argv[1])