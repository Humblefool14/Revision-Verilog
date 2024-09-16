#include <vector>
#include <algorithm>
#include <iostream>

struct Interval {
    int start;
    int end;
    int register_id;
};

class LinearScanRegisterAllocation {
private:
    std::vector<Interval> active;
    std::vector<int> free_registers;
    int R; // Maximum number of registers

    void ExpireOldIntervals(const Interval& i) {
        active.erase(
            std::remove_if(active.begin(), active.end(),
                [&](const Interval& j) {
                    //[&] is the capture clause, 
                    //allowing the lambda to access variables from the surrounding scope by reference.
                    if (j.end >= i.start) return false;
                    free_registers.push_back(j.register_id);
                    return true;
                }),
            active.end()
        );
    }

    void SpillAtInterval(Interval& i) {
        Interval spill = active.back();
        // last of the list 
        if (spill.end > i.end) {
            // Removing this register and spill to memory. 
            i.register_id = spill.register_id;
            spill.register_id = -1; // Indicate spilled to stack
            active.pop_back();
            // Here you would allocate a new stack location for 'spill'
            // location[spill] = new_stack_location();
            active.push_back(i);
            std::sort(active.begin(), active.end(),
                      [](const Interval& a, const Interval& b) { return a.end < b.end; });
                      // []: This is the capture clause. 
                      //It's empty here, meaning this lambda doesn't capture any variables from the surrounding scope.
        } else {
            i.register_id = -1; // Indicate spilled to stack
            // Here you would allocate a new stack location for 'i'
            // location[i] = new_stack_location();
        }
    }

public:
    LinearScanRegisterAllocation(int num_registers) : R(num_registers) {
        for (int i = 0; i < R; ++i) {
            free_registers.push_back(i);
        }
    }

    void allocateRegisters(std::vector<Interval>& intervals) {
        std::sort(intervals.begin(), intervals.end(),
                  [](const Interval& a, const Interval& b) { return a.start < b.start; });

        for (auto& i : intervals) {
            ExpireOldIntervals(i);
            // Kill the previous intervals. 
            if (active.size() == R) {
                SpillAtInterval(i);
                // If size more than R, then spill or else just add 
            } else {
                i.register_id = free_registers.back();
                free_registers.pop_back();
                // tracking the free registers from back. 
                active.push_back(i);
                std::sort(active.begin(), active.end(),
                          [](const Interval& a, const Interval& b) { return a.end < b.end; });
            }
        }
    }
};

// Function to generate intervals (simulating another part of the compiler)
std::vector<Interval> generateIntervals() {
    return {
        {0, 5, -1},
        {1, 7, -1},
        {2, 8, -1},
        {3, 9, -1},
        {4, 10, -1}
    };
}

int main() {
    LinearScanRegisterAllocation allocator(4); // Assume we have 4 registers
    
    // Get intervals from another function
    std::vector<Interval> intervals = generateIntervals();
    
    allocator.allocateRegisters(intervals);

    // Print results
    for (const auto& interval : intervals) {
        std::cout << "Interval [" << interval.start << ", " << interval.end 
                  << "] assigned to register " << interval.register_id << std::endl;
    }

    return 0;
}