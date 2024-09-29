#include <stdlib.h>
#include <string.h>

typedef struct {
    void* objects;
    size_t object_size;
    size_t capacity;
    size_t used;
} ObjectPool;

