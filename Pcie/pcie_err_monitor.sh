#!/bin/bash

# Find Processing accelerators
accelerator_devices=$(lspci | grep "Processing accelerators")

if [ -z "$accelerator_devices" ]; then
    echo "No Processing accelerator devices found."
    exit 1
fi

# Display found devices and let user choose
echo "Found Processing accelerator devices:"
echo "$accelerator_devices"
echo
echo "Enter the PCIe address of the device you want to check (e.g., 00:1f.6):"
read device_address

# Validate input
if ! [[ $device_address =~ ^[0-9a-fA-F]{2}:[0-9a-fA-F]{2}\.[0-9a-fA-F]$ ]]; then
    echo "Invalid PCIe address format. Please use the format XX:XX.X"
    exit 1
fi

# Function to check ASPM status
check_aspm_status() {
    echo "ASPM Status:"
    sudo lspci -vv -s $device_address | grep -A1 "ASPM" | grep -v "Kernel driver in use"
}

# Initial check
check_aspm_status

# Offer continuous monitoring
echo
echo "Do you want to continuously monitor the ASPM status? (y/n)"
read monitor_choice

if [[ $monitor_choice == "y" || $monitor_choice == "Y" ]]; then
    echo "Monitoring ASPM status. Press Ctrl+C to stop."
    while true; do
        echo "$(date):"
        check_aspm_status
        echo "----------------------------------------"
        sleep 5
    done
fi