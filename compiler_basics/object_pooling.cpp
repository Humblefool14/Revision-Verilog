#include "object_pooling.h"

int pool_expand(ObjectPool* pool) {
    size_t new_capacity = pool->capacity * 2;
    void* new_objects = realloc(pool->objects, new_capacity * pool->object_size);
    if (!new_objects) {
        return -1; // Memory allocation failed
    }
    pool->objects = new_objects;
    pool->capacity = new_capacity;
    return 0; // Success
}

void* pool_allocate(ObjectPool* pool) {
    if (pool->used >= pool->capacity) {
        if (pool_expand(pool) != 0) {
            return NULL; // Memory allocation failed, handle error
        }
    }
    void* obj = (char*)pool->objects + (pool->used * pool->object_size);
    pool->used++;
    return obj;
}

void pool_init(ObjectPool* pool, size_t object_size, size_t initial_capacity) {
    pool->objects = malloc(object_size * initial_capacity);
    if (pool->objects) {
        pool->object_size = object_size;
        pool->capacity = initial_capacity;
        pool->used = 0;
    }
}

void pool_destroy(ObjectPool* pool) {
    free(pool->objects);
    pool->objects = NULL;
    pool->capacity = 0;
    pool->used = 0;
}
