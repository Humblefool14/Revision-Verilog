#include <cstdint>
#include <vector>

class MOV31NTest {
private:
    uint32_t start_address;
    uint32_t end_address;
    uint32_t normal_db;
    uint32_t inverse_db;

    bool verify_read(uint32_t address, uint32_t expected) {
        uint32_t value;
        if (!host_read_memory(address, &value)) {
            return false;
        }
        return value == expected;
    }

    bool write_data(uint32_t address, uint32_t data) {
        return host_write_memory(address, data);
    }

    // Host interface functions
    bool host_read_memory(uint32_t address, uint32_t* data) {
        // Implementation provided by host system
        return true;  // Placeholder
    }

    bool host_write_memory(uint32_t address, uint32_t data) {
        // Implementation provided by host system
        return true;  // Placeholder
    }

public:
    MOV31NTest(uint32_t bist_start_address, uint32_t size, 
               uint32_t normal_background = 0x55555555) 
        : start_address(bist_start_address)
        , end_address(bist_start_address + size - 1)
        , normal_db(normal_background)
        , inverse_db(~normal_background)
    {}

    bool run_test() {
        // Step 1: Write normal DB in decreasing order
        for (uint32_t addr = end_address; addr >= start_address; addr--) {
            if (!write_data(addr, normal_db)) return false;
        }

        // Step 2: Increasing order (rX, wY, rY)
        for (uint32_t addr = start_address; addr <= end_address; addr++) {
            if (!verify_read(addr, normal_db)) return false;
            if (!write_data(addr, inverse_db)) return false;
            if (!verify_read(addr, inverse_db)) return false;
        }

        // Step 3: Increasing order (rY, wX, rX)
        for (uint32_t addr = start_address; addr <= end_address; addr++) {
            if (!verify_read(addr, inverse_db)) return false;
            if (!write_data(addr, normal_db)) return false;
            if (!verify_read(addr, normal_db)) return false;
        }

        // Step 4: Decreasing order (rX, wY, rY)
        for (uint32_t addr = end_address; addr >= start_address; addr--) {
            if (!verify_read(addr, normal_db)) return false;
            if (!write_data(addr, inverse_db)) return false;
            if (!verify_read(addr, inverse_db)) return false;
        }

        // Step 5: Decreasing order (rY, wX, rX)
        for (uint32_t addr = end_address; addr >= start_address; addr--) {
            if (!verify_read(addr, inverse_db)) return false;
            if (!write_data(addr, normal_db)) return false;
            if (!verify_read(addr, normal_db)) return false;
        }

        return true;
    }
};

// Usage example:
void test_memory() {
    uint32_t start_addr = 0;
    uint32_t size = 1024;
    
    MOV31NTest tester(start_addr, size);
    bool result = tester.run_test();
}