#include "beacon.h"
#include <stdlib.h>

// This function uses malloc and free from msvcrt.dll
void* allocate_buffer(size_t size) {
    void* buffer = malloc(size);
    
    if (buffer) {
        BeaconPrintf(CALLBACK_OUTPUT, "Allocated %d bytes at %p", size, buffer);
    } else {
        BeaconPrintf(CALLBACK_ERROR, "Failed to allocate memory");
    }
    
    return buffer;
}

void free_buffer(void* buffer) {
    if (buffer) {
        BeaconPrintf(CALLBACK_OUTPUT, "Freeing buffer at %p", buffer);
        free(buffer);
    }
}
