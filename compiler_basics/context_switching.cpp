#include <iostream>
#include <vector>
#include <queue>
#include <thread>
#include <mutex>
#include <condition_variable>
#include <functional>
#include <chrono>
#include <atomic>
#include <array>

// Simulated CPU registers
struct Registers {
    std::array<int, 8> general_purpose;
    int program_counter;
    int stack_pointer;
};

// Thread Control Block (TCB)
struct TCB {
    int id;
    Registers registers;
    std::function<void()> task;
};

class Scheduler {
private:
    std::vector<TCB> threads;
    std::queue<int> ready_queue;
    std::mutex queue_mutex;
    std::condition_variable cv;
    std::atomic<bool> stop;
    int current_thread;
    Registers cpu_registers;

    void save_context(int thread_id) {
        threads[thread_id].registers = cpu_registers;
        std::cout << "Saved context for thread " << thread_id << std::endl;
    }

    void load_context(int thread_id) {
        cpu_registers = threads[thread_id].registers;
        std::cout << "Loaded context for thread " << thread_id << std::endl;
    }

    void flush_registers() {
        cpu_registers = Registers(); // Reset all registers to default values
        std::cout << "Flushed CPU registers" << std::endl;
    }

    void context_switch() {
        if (current_thread != -1) {
            save_context(current_thread);
            ready_queue.push(current_thread);
        }

        flush_registers();

        std::unique_lock<std::mutex> lock(queue_mutex);
        if (!ready_queue.empty()) {
            current_thread = ready_queue.front();
            ready_queue.pop();
            lock.unlock();

            load_context(current_thread);
            
            std::cout << "Switched to thread " << current_thread << std::endl;
            threads[current_thread].task();
        } else {
            current_thread = -1;
            lock.unlock();
        }
    }

    void scheduler_loop() {
        while (!stop) {
            context_switch();
            std::this_thread::sleep_for(std::chrono::milliseconds(100)); // Time slice
        }
    }

public:
    Scheduler() : stop(false), current_thread(-1) {}

    void add_thread(std::function<void()> task) {
        int id = threads.size();
        threads.push_back({id, Registers(), task});
        ready_queue.push(id);
        std::cout << "Added thread " << id << std::endl;
    }

    void run() {
        std::thread scheduler_thread(&Scheduler::scheduler_loop, this);
        
        // Wait for all threads to complete
        while (!ready_queue.empty() || current_thread != -1) {
            std::this_thread::sleep_for(std::chrono::milliseconds(10));
        }

        stop = true;
        scheduler_thread.join();
    }
};

// Simulated task
void task(int id, int iterations) {
    for (int i = 0; i < iterations; ++i) {
        std::cout << "Task " << id << " iteration " << i << std::endl;
        std::this_thread::sleep_for(std::chrono::milliseconds(50)); // Simulate some work
    }
}

int main() {
    Scheduler scheduler;

    // Add tasks to the scheduler
    for (int i = 0; i < 5; ++i) {
        scheduler.add_thread(std::bind(task, i, 3));
    }

    // Run the scheduler
    scheduler.run();

    std::cout << "All tasks completed." << std::endl;

    return 0;
}