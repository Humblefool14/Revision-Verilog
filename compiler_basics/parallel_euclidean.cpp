#include <cuda_runtime.h>
#include <device_launch_parameters.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#define CHECK(call) \
{ \
    const cudaError_t error = call; \
    if (error != cudaSuccess) \
    { \
        printf("Error: %s:%d, ", __FILE__, __LINE__); \
        printf("code:%d, reason: %s\n", error, cudaGetErrorString(error)); \
        exit(1); \
    } \
}

__global__ void euclidian_distance(float2 *p1, float2 *p2, float *distance, int count) {
    int index = threadIdx.x + (blockIdx.x * blockDim.x);
    
    if (index < count) {
        float2 dp = p2[index] - p1[index];
        float dist = sqrtf(dp.x * dp.x + dp.y * dp.y);
        distance[index] = dist;
    }
}

void verify_results(float2 *h_p1, float2 *h_p2, float *h_distance, int count) {
    for (int i = 0; i < count; i++) {
        float2 dp = {h_p2[i].x - h_p1[i].x, h_p2[i].y - h_p1[i].y};
        float expected_dist = sqrtf(dp.x * dp.x + dp.y * dp.y);
        if (fabs(h_distance[i] - expected_dist) > 1e-5) {
            printf("Mismatch at index %d: GPU = %f, CPU = %f\n", i, h_distance[i], expected_dist);
            return;
        }
    }
    printf("All results match!\n");
}

int main() {
    const int count = 1000000;
    const int bytes = count * sizeof(float2);
    const int bytes_dist = count * sizeof(float);

    // Allocate host memory
    float2 *h_p1 = (float2*)malloc(bytes);
    float2 *h_p2 = (float2*)malloc(bytes);
    float *h_distance = (float*)malloc(bytes_dist);

    // Initialize input data
    for (int i = 0; i < count; i++) {
        h_p1[i] = make_float2(rand() / (float)RAND_MAX, rand() / (float)RAND_MAX);
        h_p2[i] = make_float2(rand() / (float)RAND_MAX, rand() / (float)RAND_MAX);
    }

    // Allocate device memory
    float2 *d_p1, *d_p2;
    float *d_distance;
    CHECK(cudaMalloc(&d_p1, bytes));
    CHECK(cudaMalloc(&d_p2, bytes));
    CHECK(cudaMalloc(&d_distance, bytes_dist));

    // Copy input data to device
    CHECK(cudaMemcpy(d_p1, h_p1, bytes, cudaMemcpyHostToDevice));
    CHECK(cudaMemcpy(d_p2, h_p2, bytes, cudaMemcpyHostToDevice));

    // Launch kernel
    int threadsPerBlock = 256;
    int blocksPerGrid = (count + threadsPerBlock - 1) / threadsPerBlock;
    euclidian_distance<<<blocksPerGrid, threadsPerBlock>>>(d_p1, d_p2, d_distance, count);
    
    // Check for kernel launch errors
    CHECK(cudaGetLastError());

    // Copy result back to host
    CHECK(cudaMemcpy(h_distance, d_distance, bytes_dist, cudaMemcpyDeviceToHost));

    // Verify results
    verify_results(h_p1, h_p2, h_distance, count);

    // Free memory
    free(h_p1);
    free(h_p2);
    free(h_distance);
    CHECK(cudaFree(d_p1));
    CHECK(cudaFree(d_p2));
    CHECK(cudaFree(d_distance));

    return 0;
}