#include <iostream>
#include <vector>
#include <algorithm>

class MemoryBlock {
public:
    size_t start;
    size_t size;
    bool free;

    MemoryBlock(size_t start, size_t size, bool free = true)
        : start(start), size(size), free(free) {}
};

class BestFitAllocator {
private:
    std::vector<MemoryBlock> memory;
    size_t totalSize;

public:
    BestFitAllocator(size_t size) : totalSize(size) {
        memory.emplace_back(0, size);
    }

    void* allocate(size_t size) {
        auto bestFit = std::min_element(memory.begin(), memory.end(),
            [size](const MemoryBlock& a, const MemoryBlock& b) {
                if (!a.free) return false;
                if (!b.free) return true;
                if (a.size < size) return false;
                if (b.size < size) return true;
                return a.size < b.size;
            });

        if (bestFit == memory.end() || bestFit->size < size || !bestFit->free) {
            std::cout << "Allocation failed: No suitable block found.\n";
            return nullptr;
        }

        size_t allocStart = bestFit->start;
        size_t remainingSize = bestFit->size - size;

        bestFit->size = size;
        bestFit->free = false;

        if (remainingSize > 0) {
            memory.insert(std::next(bestFit), MemoryBlock(allocStart + size, remainingSize));
        }

        return reinterpret_cast<void*>(allocStart);
    }

    void deallocate(void* ptr) {
        auto it = std::find_if(memory.begin(), memory.end(),
            [ptr](const MemoryBlock& block) {
                return reinterpret_cast<void*>(block.start) == ptr;
            });

        if (it != memory.end() && !it->free) {
            it->free = true;
            mergeFreeBlocks();
        } else {
            std::cout << "Deallocation failed: Invalid pointer.\n";
        }
    }

    void mergeFreeBlocks() {
        auto it = memory.begin();
        while (it != memory.end() && std::next(it) != memory.end()) {
            if (it->free && std::next(it)->free) {
                it->size += std::next(it)->size;
                memory.erase(std::next(it));
            } else {
                ++it;
            }
        }
    }

    void printMemoryMap() {
        for (const auto& block : memory) {
            std::cout << "[" << block.start << " - " << (block.start + block.size - 1)
                      << "] " << block.size << " bytes "
                      << (block.free ? "free" : "allocated") << "\n";
        }
        std::cout << "\n";
    }
};

int main() {
    BestFitAllocator allocator(1024);
    
    std::cout << "Initial memory map:\n";
    allocator.printMemoryMap();

    void* ptr1 = allocator.allocate(200);
    std::cout << "After allocating 200 bytes:\n";
    allocator.printMemoryMap();

    void* ptr2 = allocator.allocate(100);
    std::cout << "After allocating 100 bytes:\n";
    allocator.printMemoryMap();

    allocator.deallocate(ptr1);
    std::cout << "After deallocating 200 bytes:\n";
    allocator.printMemoryMap();

    void* ptr3 = allocator.allocate(150);
    std::cout << "After allocating 150 bytes:\n";
    allocator.printMemoryMap();

    return 0;
}