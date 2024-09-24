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

# Check PCIe status
echo "Checking PCIe status for device $device_address"
sudo lspci -vv -s $device_address | grep -E "LnkCap|LnkSta"

# Offer continuous monitoring
echo
echo "Do you want to continuously monitor the link status? (y/n)"
read monitor_choice

if [[ $monitor_choice == "y" || $monitor_choice == "Y" ]]; then
    echo "Monitoring link status. Press Ctrl+C to stop."
    while true; do
        echo "$(date): $(sudo lspci -vv -s $device_address | grep -E 'LnkSta:')"
        sleep 1
    done
fi