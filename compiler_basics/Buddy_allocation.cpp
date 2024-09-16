#include <iostream>
#include <vector>
#include <cmath>

class BuddyAllocator {
private:
    std::vector<std::vector<bool>> free_list;
    size_t total_size;
    size_t min_block_size;
    size_t levels;

public:
    BuddyAllocator(size_t size, size_t min_size) {
        // Ensure size is a power of 2
        total_size = std::pow(2, std::ceil(std::log2(size)));
        min_block_size = min_size;
        levels = std::log2(total_size / min_block_size) + 1;

        free_list.resize(levels);
        for (size_t i = 0; i < levels; ++i) {
            size_t blocks = total_size / (min_block_size * std::pow(2, i));
            free_list[i].resize(blocks, true);
        }
    }

    void* allocate(size_t size) {
        size_t block_size = std::max(min_block_size, 
                                     (size_t)std::pow(2, std::ceil(std::log2(size))));
        int level = std::log2(total_size / block_size);

        if (level >= levels) return nullptr;

        int index = find_free_block(level);
        if (index == -1) return nullptr;

        split_and_mark(level, index);

        size_t offset = index * block_size;
        return (void*)(uintptr_t)offset;
    }

    void deallocate(void* ptr, size_t size) {
        size_t block_size = std::max(min_block_size, 
                                     (size_t)std::pow(2, std::ceil(std::log2(size))));
        int level = std::log2(total_size / block_size);
        size_t index = (size_t)(uintptr_t)ptr / block_size;

        merge_and_free(level, index);
    }

private:
    int find_free_block(int level) {
        for (size_t i = 0; i < free_list[level].size(); ++i) {
            if (free_list[level][i]) return i;
        }
        return -1;
    }

    void split_and_mark(int level, int index) {
        while (level > 0) {
            free_list[level][index] = false;
            --level;
            index *= 2;
        }
        free_list[0][index] = false;
    }

    void merge_and_free(int level, size_t index) {
        while (level < levels - 1) {
            free_list[level][index] = true;
            if (index % 2 == 0) {
                if (!free_list[level][index + 1]) break;
            } else {
                if (!free_list[level][index - 1]) break;
                index--;
            }
            ++level;
            index /= 2;
        }
        free_list[level][index] = true;
    }
};

int main() {
    BuddyAllocator allocator(1024, 16);  // 1024 bytes total, 16 bytes minimum block size

    void* ptr1 = allocator.allocate(16);
    void* ptr2 = allocator.allocate(32);
    void* ptr3 = allocator.allocate(64);

    std::cout << "Allocated 16 bytes at: " << ptr1 << std::endl;
    std::cout << "Allocated 32 bytes at: " << ptr2 << std::endl;
    std::cout << "Allocated 64 bytes at: " << ptr3 << std::endl;

    allocator.deallocate(ptr2, 32);
    allocator.deallocate(ptr1, 16);
    allocator.deallocate(ptr3, 64);

    return 0;
}