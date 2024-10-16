#include <stdint.h>
#include <stddef.h>

uint64_t fletcher64(const void* data, size_t length) {
    const uint32_t* words = (const uint32_t*)data;
    size_t word_len = length / sizeof(uint32_t);
    uint64_t sum1 = 0xFFFFFFFF, sum2 = 0xFFFFFFFF;
    size_t i;

    // Process all complete 32-bit words
    for (i = 0; i < word_len; ++i) {
        sum1 += words[i];
        sum2 += sum1;
    }

    // Fold 64-bit sums to 32 bits
    sum1 = (sum1 & 0xFFFFFFFF) + (sum1 >> 32);
    sum2 = (sum2 & 0xFFFFFFFF) + (sum2 >> 32);

    // Handle any remaining bytes
    const uint8_t* bytes = (const uint8_t*)data;
    for (i = word_len * sizeof(uint32_t); i < length; ++i) {
        sum1 += bytes[i];
        sum2 += sum1;
    }

    // Second fold to 32 bits
    sum1 = (sum1 & 0xFFFFFFFF) + (sum1 >> 32);
    sum2 = (sum2 & 0xFFFFFFFF) + (sum2 >> 32);

    // Combine the two 32-bit sums into a 64-bit checksum
    return (sum2 << 32) | sum1;
}