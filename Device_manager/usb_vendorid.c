#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <dirent.h>
#include <cstring>
#include <algorithm>
#include <sstream>

class USBDeviceManager {
private:
    std::vector<std::string> vendorFiles;
    
public:
    // Function to recursively search for vendor files
    void findVendorFiles(const std::string& path, std::vector<std::string>& vendorFiles, 
                         const std::string& targetVendorId) {
        DIR* dir = opendir(path.c_str());
        if (!dir) {
            return; // Can't open directory
        }
        struct dirent* entry;
        while ((entry = readdir(dir)) != nullptr) {
            // Skip "." and ".." directories
            if (strcmp(entry->d_name, ".") == 0 || strcmp(entry->d_name, "..") == 0) {
                continue;
            }
            std::string entryPath = path + "/" + entry->d_name;
            // If it's a directory, search recursively
            if (entry->d_type == DT_DIR) {
                findVendorFiles(entryPath, vendorFiles, targetVendorId);
            } 
            // If it's a file named "vendor", check its content
            else if (entry->d_type == DT_REG && strcmp(entry->d_name, "vendor") == 0) {
                std::ifstream vendorFile(entryPath);
                if (vendorFile.is_open()) {
                    std::string vendorId;
                    std::getline(vendorFile, vendorId);
                    vendorFile.close();
                    // Remove any trailing whitespace
                    vendorId.erase(vendorId.find_last_not_of(" \n\r\t") + 1);
                    // Check if the vendor ID matches the target
                    if (vendorId == targetVendorId) {
                        vendorFiles.push_back(entryPath);
                        std::cout << "Found matching vendor file: " << entryPath << std::endl;
                    }
                }
            }
        }
        closedir(dir);
    }
    
    // Find USB devices with specific vendor ID
    std::vector<std::string> findUSBDevicesByVendor(const std::string& vendorId) {
        vendorFiles.clear();
        findVendorFiles("/sys/bus/usb/devices", vendorFiles, vendorId);
        return vendorFiles;
    }
    
    // Get device path from vendor file path
    std::string getDevicePathFromVendorFile(const std::string& vendorFilePath) {
        size_t lastSlash = vendorFilePath.find_last_of('/');
        if (lastSlash != std::string::npos) {
            return vendorFilePath.substr(0, lastSlash);
        }
        return "";
    }
    
    // Get device information
    struct USBDeviceInfo {
        std::string devicePath;
        std::string vendorId;
        std::string productId;
        std::string manufacturer;
        std::string product;
        std::string busNum;
        std::string devNum;
    };
    
    USBDeviceInfo getDeviceInfo(const std::string& devicePath) {
        USBDeviceInfo info;
        info.devicePath = devicePath;
        
        // Read vendor ID
        std::ifstream vendorFile(devicePath + "/idVendor");
        if (vendorFile.is_open()) {
            std::getline(vendorFile, info.vendorId);
            vendorFile.close();
        }
        
        // Read product ID
        std::ifstream productFile(devicePath + "/idProduct");
        if (productFile.is_open()) {
            std::getline(productFile, info.productId);
            productFile.close();
        }
        
        // Read manufacturer
        std::ifstream mfgFile(devicePath + "/manufacturer");
        if (mfgFile.is_open()) {
            std::getline(mfgFile, info.manufacturer);
            mfgFile.close();
        }
        
        // Read product name
        std::ifstream prodNameFile(devicePath + "/product");
        if (prodNameFile.is_open()) {
            std::getline(prodNameFile, info.product);
            prodNameFile.close();
        }
        
        // Read bus number
        std::ifstream busFile(devicePath + "/busnum");
        if (busFile.is_open()) {
            std::getline(busFile, info.busNum);
            busFile.close();
        }
        
        // Read device number
        std::ifstream devFile(devicePath + "/devnum");
        if (devFile.is_open()) {
            std::getline(devFile, info.devNum);
            devFile.close();
        }
        
        return info;
    }
    
    // Reset USB device using authorized method
    bool resetDeviceAuthorized(const std::string& devicePath) {
        std::string authorizedPath = devicePath + "/authorized";
        
        // Disable device
        std::ofstream authFile(authorizedPath);
        if (!authFile.is_open()) {
            std::cerr << "Failed to open authorized file: " << authorizedPath << std::endl;
            return false;
        }
        
        authFile << "0" << std::endl;
        authFile.close();
        
        // Wait a moment
        sleep(2);
        
        // Re-enable device
        authFile.open(authorizedPath);
        if (!authFile.is_open()) {
            std::cerr << "Failed to reopen authorized file: " << authorizedPath << std::endl;
            return false;
        }
        
        authFile << "1" << std::endl;
        authFile.close();
        
        std::cout << "Device reset completed using authorized method" << std::endl;
        return true;
    }
    
    // Remove USB device completely
    bool removeDevice(const std::string& devicePath) {
        std::string removePath = devicePath + "/remove";
        
        std::ofstream removeFile(removePath);
        if (!removeFile.is_open()) {
            std::cerr << "Failed to open remove file: " << removePath << std::endl;
            return false;
        }
        
        removeFile << "1" << std::endl;
        removeFile.close();
        
        std::cout << "Device removed from USB subsystem" << std::endl;
        return true;
    }
    
    // Suspend USB device
    bool suspendDevice(const std::string& devicePath) {
        std::string controlPath = devicePath + "/power/control";
        std::string autosuspendPath = devicePath + "/power/autosuspend_delay_ms";
        
        // Set autosuspend delay to 0
        std::ofstream autosuspendFile(autosuspendPath);
        if (autosuspendFile.is_open()) {
            autosuspendFile << "0" << std::endl;
            autosuspendFile.close();
        }
        
        // Set control to auto
        std::ofstream controlFile(controlPath);
        if (!controlFile.is_open()) {
            std::cerr << "Failed to open power control file: " << controlPath << std::endl;
            return false;
        }
        
        controlFile << "auto" << std::endl;
        controlFile.close();
        
        std::cout << "Device suspended" << std::endl;
        return true;
    }
    
    // Wake up USB device
    bool wakeDevice(const std::string& devicePath) {
        std::string controlPath = devicePath + "/power/control";
        
        std::ofstream controlFile(controlPath);
        if (!controlFile.is_open()) {
            std::cerr << "Failed to open power control file: " << controlPath << std::endl;
            return false;
        }
        
        controlFile << "on" << std::endl;
        controlFile.close();
        
        std::cout << "Device woken up" << std::endl;
        return true;
    }
    
    // Print device information
    void printDeviceInfo(const USBDeviceInfo& info) {
        std::cout << "=== USB Device Information ===" << std::endl;
        std::cout << "Device Path: " << info.devicePath << std::endl;
        std::cout << "Vendor ID: " << info.vendorId << std::endl;
        std::cout << "Product ID: " << info.productId << std::endl;
        std::cout << "Manufacturer: " << info.manufacturer << std::endl;
        std::cout << "Product: " << info.product << std::endl;
        std::cout << "Bus Number: " << info.busNum << std::endl;
        std::cout << "Device Number: " << info.devNum << std::endl;
        std::cout << "==============================" << std::endl;
    }
};

int main(int argc, char* argv[]) {
    if (argc < 2) {
        std::cout << "Usage: " << argv[0] << " <vendor_id> [action]" << std::endl;
        std::cout << "Actions: info, reset, remove, suspend, wake" << std::endl;
        std::cout << "Example: " << argv[0] << " 318d info" << std::endl;
        return 1;
    }
    
    std::string vendorId = argv[1];
    std::string action = (argc > 2) ? argv[2] : "info";
    
    USBDeviceManager manager;
    
    // Find devices with the specified vendor ID
    std::vector<std::string> devices = manager.findUSBDevicesByVendor(vendorId);
    
    if (devices.empty()) {
        std::cout << "No USB devices found with vendor ID: " << vendorId << std::endl;
        return 1;
    }
    
    // Process each found device
    for (const std::string& vendorFile : devices) {
        std::string devicePath = manager.getDevicePathFromVendorFile(vendorFile);
        
        if (action == "info") {
            USBDeviceManager::USBDeviceInfo info = manager.getDeviceInfo(devicePath);
            manager.printDeviceInfo(info);
        }
        else if (action == "reset") {
            manager.resetDeviceAuthorized(devicePath);
        }
        else if (action == "remove") {
            manager.removeDevice(devicePath);
        }
        else if (action == "suspend") {
            manager.suspendDevice(devicePath);
        }
        else if (action == "wake") {
            manager.wakeDevice(devicePath);
        }
        else {
            std::cout << "Unknown action: " << action << std::endl;
            std::cout << "Available actions: info, reset, remove, suspend, wake" << std::endl;
        }
    }
    
    return 0;
}
