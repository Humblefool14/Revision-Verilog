#include <iostream>
#include <vector>
#include <cmath>
#ifdef _OPENMP
    #include <omp.h>
#endif
// Function to perform upscan (reduce)
void upscan(std::vector<int>& arr) {
    int n = arr.size();
    for (int d = 0; d < std::log2(n); ++d) {
        //for d from 0 to (lgn)−1
        int stride = std::pow(2, d + 1);
        //in parallel for i from 0 to n−1 by 2 power(d+1) 
        #pragma omp parallel for
        for (int i = 0; i < n; i += stride) {
            if (i + stride - 1 < n) {
                arr[i + stride - 1] += arr[i + stride / 2 - 1];
                //a[i+pow(2,d+1) −1]←a[i+pow(2,d) −1]+a[i+pow(2,d+1) −1]
            }
        }
    }
}

// Function to perform downscan (distribute)
void downscan(std::vector<int>& arr) {
    int n = arr.size();
    arr[n - 1] = 0;  // Set identity element

    for (int d = std::log2(n) - 1; d >= 0; --d) {
        // for d from (lgn)−1 downto 0
        int stride = std::pow(2, d + 1);
        #pragma omp parallel for
        for (int i = 0; i < n; i += stride) {
            if (i + stride - 1 < n) {
                int t = arr[i + stride / 2 - 1];
                // t←arr[i+pow(2,d) −1] %Save in temporary
                arr[i + stride / 2 - 1] = arr[i + stride - 1];
                //arr[i+pow(2,d) −1]←a[i+ pow(2,d+1) −1] %Setleftchild
                arr[i + stride - 1] += t;
                // arr[i+pow(2,d+1) −1]←t+arr[i+pow(2,d+1) −1] %Setrightchild
            }
        }
    }
}

// Function to perform the complete prefix sum
void parallel_prefix_sum(std::vector<int>& arr) {
    upscan(arr);
    downscan(arr);
}

int main() {
    std::vector<int> arr = {3, 1, 7, 0, 4, 1, 6, 3};
    int n = arr.size();

    std::cout << "Original array: ";
    for (int num : arr) std::cout << num << " ";
    std::cout << std::endl;

    parallel_prefix_sum(arr);

    std::cout << "Prefix sum array: ";
    for (int num : arr) std::cout << num << " ";
    std::cout << std::endl;

    return 0;
}

//command to run. g++ -fopenmp -O3 -std=c++11 prefix_sum.cpp -o prefix_sum
