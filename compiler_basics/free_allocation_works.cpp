typedef struct __header_t { int size;
    int magic;
} header_t;

void free(void *ptr) {
header_t *hptr = (void *)ptr - sizeof(header_t);
}

typedef struct __node_t { 
    int size; 
    struct __node_t *next;
} node_t;


// mmap() returns a pointer to a chunk of free space node_t *head = mmap(NULL, 4096, PROT_READ|PROT_WRITE,
MAP_ANON|MAP_PRIVATE, -1, 0); 
head->size = 4096 - sizeof(node_t);
head->next   = NULL;

// first-fit 
block *first_fit(size_t size){
    auto block = heap_start; 

    while(block!=nullptr){
        //or
        // if(block->size > size){
        // return block;
        // } 
        if(block->size < size){
            block = block->next; 
            continue;
        }
        return block; 
    }
    return nullptr; 
}

block *best_fit(size_t size){
    auto block = heap_start; 
    while(block!=nullptr){
        if(block->size > size){
            //track block, difference
            // map <i, block->size -size> 
            block = block->next; 
            continue;
        }

    }
    std::sort(map.begin(), map.end())//key wise checking; 
    if(!map.begin()){
        return nullptr; 
    }
    return map.begin(); 
}