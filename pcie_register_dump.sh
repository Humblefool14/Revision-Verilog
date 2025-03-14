#!/bin/bash

# Script to dump all PCI configuration registers for a specified device with register names

# Display help information
display_help() {
    echo "# Script to dump all PCI configuration registers for a specified device with register names"
    echo "# Usage: ./pci_dump.sh <PCI_ADDRESS> [OUTPUT_FILE]"
    echo "# Example: ./pci_dump.sh 01:00.0 pci_dump.log"
    echo ""
    echo "This script dumps all PCI configuration registers for a given PCI device address"
    echo "and labels them with their standard register names where known."
    echo ""
    echo "Options:"
    echo "  -h, --help    Display this help message and exit"
    echo ""
    echo "Arguments:"
    echo "  <PCI_ADDRESS>  PCI address in the format of domain:bus:device.function (e.g., 01:00.0)"
    echo "  [OUTPUT_FILE]  Optional output file name (default: pci_dump_<PCI_ADDRESS>.log)"
    exit 0
}

# Check for help flag
if [ "$1" = "-h" ] || [ "$1" = "--help" ]; then
    display_help
fi

# Check if the script has the correct number of arguments
if [ $# -lt 1 ]; then
    echo "Usage: $0 <PCI_ADDRESS> [OUTPUT_FILE]"
    echo "Example: $0 01:00.0 pci_dump.log"
    echo "Use '$0 -h' for more information"
    exit 1
fi

# Assign arguments to variables
PCI_ADDRESS="$1"
OUTPUT_FILE="${2:-pci_dump_$PCI_ADDRESS.log}"

# Check if the PCI address is valid
if ! lspci -s "$PCI_ADDRESS" &>/dev/null; then
    echo "Error: Invalid PCI address. Use lspci to find valid addresses."
    exit 1
fi

# Timestamp for the log
echo "PCI Register Dump for device $PCI_ADDRESS - $(date)" > "$OUTPUT_FILE"
echo "Device description: $(lspci -s "$PCI_ADDRESS" | cut -d' ' -f2-)" >> "$OUTPUT_FILE"
echo "=======================================================" >> "$OUTPUT_FILE"

# Define standard PCI configuration register names
declare -A PCI_REGISTERS=(
    # Standard header registers (for all PCI devices)
    ["0x0"]="Vendor ID (16-bit)/Device ID (16-bit)"
    ["0x4"]="Command (16-bit)/Status (16-bit)"
    ["0x8"]="Revision ID (8-bit)/Class Code (24-bit)"
    ["0xc"]="Cache Line Size (8-bit)/Latency Timer (8-bit)/Header Type (8-bit)/BIST (8-bit)"
    ["0x10"]="Base Address Register 0 (BAR0)"
    ["0x14"]="Base Address Register 1 (BAR1)"
    ["0x18"]="Base Address Register 2 (BAR2)"
    ["0x1c"]="Base Address Register 3 (BAR3)"
    ["0x20"]="Base Address Register 4 (BAR4)"
    ["0x24"]="Base Address Register 5 (BAR5)"
    ["0x28"]="CardBus CIS Pointer"
    ["0x2c"]="Subsystem Vendor ID (16-bit)/Subsystem ID (16-bit)"
    ["0x30"]="Expansion ROM Base Address"
    ["0x34"]="Capabilities Pointer (8-bit)"
    ["0x38"]="Reserved"
    ["0x3c"]="Interrupt Line (8-bit)/Interrupt Pin (8-bit)/Min_Gnt (8-bit)/Max_Lat (8-bit)"
)

# Define PCIe extended capability register names
declare -A PCIE_CAPABILITIES=(
    ["0x100"]="PCIe Capability Header"
    ["0x104"]="Device Capabilities"
    ["0x108"]="Device Control/Device Status"
    ["0x10c"]="Link Capabilities"
    ["0x110"]="Link Control/Link Status"
    ["0x114"]="Slot Capabilities"
    ["0x118"]="Slot Control/Slot Status"
    ["0x11c"]="Root Control/Root Capabilities/Root Status"
    ["0x120"]="Device Capabilities 2"
    ["0x124"]="Device Control 2/Device Status 2"
    ["0x128"]="Link Capabilities 2"
    ["0x12c"]="Link Control 2/Link Status 2"
    ["0x150"]="AER Capability Header"
    ["0x154"]="Uncorrectable Error Status"
    ["0x158"]="Uncorrectable Error Mask"
    ["0x15c"]="Uncorrectable Error Severity"
    ["0x160"]="Correctable Error Status"
    ["0x164"]="Correctable Error Mask"
    ["0x168"]="Advanced Error Capabilities and Control"
)

# Function to dump a register with proper name
dump_register() {
    local addr=$1
    local width=$2
    local hex_addr=$(printf "0x%x" $addr)
    local register_name=""
    
    # Look up the register name
    if [ $addr -lt 256 ]; then
        register_name="${PCI_REGISTERS[$hex_addr]:-Unknown register}"
    else
        register_name="${PCIE_CAPABILITIES[$hex_addr]:-Extended register}"
    fi
    
    # Read the register value using setpci
    if [ "$width" -eq 1 ]; then
        cmd="setpci -s $PCI_ADDRESS $hex_addr.B"
    elif [ "$width" -eq 2 ]; then
        cmd="setpci -s $PCI_ADDRESS $hex_addr.W"
    elif [ "$width" -eq 4 ]; then
        cmd="setpci -s $PCI_ADDRESS $hex_addr.L"
    fi
    
    value=$(eval $cmd)
    
    # Print the result
    printf "Register %s (%s): %s\n" "$hex_addr" "$register_name" "$value" >> "$OUTPUT_FILE"
}

# Function to dump a range of registers
dump_range() {
    local start=$1
    local end=$2
    local width=$3
    
    for addr in $(seq $start $width $end); do
        dump_register $addr $width
    done
}

echo "Dumping standard PCI configuration space (256 bytes)..." | tee -a "$OUTPUT_FILE"

# Dump standard configuration space (0x00-0xFF)
# First 64 bytes (0x00-0x3F) as 32-bit (DWORD) registers
echo "DWORD Registers (0x00-0x3F):" >> "$OUTPUT_FILE"
dump_range 0 60 4

# Next 192 bytes (0x40-0xFF) as 8-bit (BYTE) registers
echo "BYTE Registers (0x40-0xFF):" >> "$OUTPUT_FILE"
dump_range 64 255 1

# Check if the device has extended configuration space (PCIe)
if lspci -vv -s "$PCI_ADDRESS" | grep -q "Capabilities: \[.*\] Express"; then
    echo "Device has PCIe extended configuration space. Dumping extended space (256-4095 bytes)..." | tee -a "$OUTPUT_FILE"
    
    # Dump extended configuration space (0x100-0xFFF)
    echo "Extended Configuration Space (0x100-0xFFF):" >> "$OUTPUT_FILE"
    dump_range 256 4095 4
    
    echo "Performing detailed PCIe capability parsing..." | tee -a "$OUTPUT_FILE"
    
    # Use lspci to get detailed device info
    echo -e "\nDetailed PCIe Capability Information:" >> "$OUTPUT_FILE"
    lspci -vvv -s "$PCI_ADDRESS" >> "$OUTPUT_FILE"
fi

# Parse capability registers if available
echo -e "\nParsing PCI Capabilities:" >> "$OUTPUT_FILE"
cap_ptr=$(setpci -s $PCI_ADDRESS 0x34.B)

if [ "$cap_ptr" != "00" ]; then
    echo "Capability pointer found at 0x34: $cap_ptr" >> "$OUTPUT_FILE"
    
    # Convert hex string to decimal for calculation
    cap_addr=$(printf "%d" 0x$cap_ptr)
    
    while [ $cap_addr -ne 0 ] && [ $cap_addr -lt 256 ]; do
        # Read capability ID and next pointer
        cap_id=$(setpci -s $PCI_ADDRESS $(printf "0x%x" $cap_addr).B)
        next_ptr=$(setpci -s $PCI_ADDRESS $(printf "0x%x" $(($cap_addr + 1))).B)
        
        # Interpret capability ID
        case "$cap_id" in
            "01") cap_name="PCI Power Management" ;;
            "03") cap_name="VGA Palette Snooping" ;;
            "05") cap_name="MSI" ;;
            "10") cap_name="PCIe" ;;
            "11") cap_name="MSI-X" ;;
            "14") cap_name="Advanced Features" ;;
            *) cap_name="Unknown Capability" ;;
        esac
        
        echo "Capability at 0x$(printf "%x" $cap_addr): ID=$cap_id ($cap_name), Next=0x$next_ptr" >> "$OUTPUT_FILE"
        
        # Get next capability pointer or exit loop
        if [ "$next_ptr" == "00" ]; then
            break
        fi
        cap_addr=$(printf "%d" 0x$next_ptr)
    done
else
    echo "No capabilities found." >> "$OUTPUT_FILE"
fi

echo "PCI register dump completed. Results saved to $OUTPUT_FILE"

# Optional: Display device tree information if available
if command -v lspci >/dev/null 2>&1; then
    echo -e "\nDevice Tree Information:" >> "$OUTPUT_FILE"
    lspci -t -s "$PCI_ADDRESS" >> "$OUTPUT_FILE" 2>/dev/null || echo "Device tree information not available" >> "$OUTPUT_FILE"
fi