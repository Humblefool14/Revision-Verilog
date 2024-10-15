#include <iostream>
#include <vector>
#include <cmath>
#include <omp.h>

void upscan(std::vector<int>& arr) {
    int n = arr.size();
    for (int d = 0; d < std::log2(n); ++d) {
        int stride = std::pow(2, d + 1);
        #pragma omp parallel for
        for (int i = 0; i < n; i += stride) {
            if (i + stride - 1 < n) {
                arr[i + stride - 1] += arr[i + stride / 2 - 1];
            }
        }
    }
}

void downscan(std::vector<int>& arr) {
    int n = arr.size();
    arr[n - 1] = 0;  // Set identity element

    for (int d = std::log2(n) - 1; d >= 0; --d) {
        int stride = std::pow(2, d + 1);
        #pragma omp parallel for
        for (int i = 0; i < n; i += stride) {
            if (i + stride - 1 < n) {
                int t = arr[i + stride / 2 - 1];
                arr[i + stride / 2 - 1] = arr[i + stride - 1];
                arr[i + stride - 1] += t;
            }
        }
    }
}

std::vector<int> parallel_prescan(const std::vector<int>& input) {
    std::vector<int> result = input;
    upscan(result);
    downscan(result);
    return result;
}

std::vector<int> parallel_postscan(const std::vector<int>& input) {
    std::vector<int> result = parallel_prescan(input);
    int n = result.size();
    #pragma omp parallel for
    for (int i = 0; i < n; ++i) {
        result[i] += input[i];
    }
    return result;
}

void print_vector(const std::vector<int>& vec, const std::string& label) {
    std::cout << label << ": ";
    for (int num : vec) std::cout << num << " ";
    std::cout << std::endl;
}

int main() {
    std::vector<int> arr = {3, 1, 7, 0, 4, 1, 6, 3};

    print_vector(arr, "Original array");

    std::vector<int> prescan_result = parallel_prescan(arr);
    print_vector(prescan_result, "Prescan result");

    std::vector<int> postscan_result = parallel_postscan(arr);
    print_vector(postscan_result, "Postscan result");

    return 0;
}