#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <dirent.h>
#include <sys/stat.h>
#include <cstring>

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

int main(int argc, char* argv[]) {
    if (argc != 2) {
        std::cerr << "Usage: " << argv[0] << " <vendor_id_to_search_for>" << std::endl;
        return 1;
    }

    std::string targetVendorId = argv[1];
    std::vector<std::string> matchingVendorFiles;
    
    // Start searching from /sys/devices
    findVendorFiles("/sys/devices", matchingVendorFiles, targetVendorId);
    
    // Print all matching vendor files
    std::cout << "\nList of devices with matching vendor ID (" << targetVendorId << "):" << std::endl;
    for (const auto& file : matchingVendorFiles) {
        std::cout << file << std::endl;
    }
    
    std::cout << "Total matching devices found: " << matchingVendorFiles.size() << std::endl;
    
    return 0;
}
