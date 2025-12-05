#include "beacon.h"
#include <stdlib.h>

// External functions from other compilation units
extern void* allocate_buffer(size_t size);
extern void free_buffer(void* buffer);
extern void print_message(const char* message);

void go(void) {
    BeaconPrintf(CALLBACK_OUTPUT, "=== MinGW MSVCRT Import Deduplication Demo ===");
    
    print_message("Starting memory allocation test");
    
    // This also uses malloc - boflink should deduplicate this import
    void* temp_buffer = malloc(1024);
    
    if (temp_buffer) {
        BeaconPrintf(CALLBACK_OUTPUT, "Temporary buffer allocated");
        
        // Use the allocator from another file
        void* main_buffer = allocate_buffer(2048);
        
        if (main_buffer) {
            print_message("Both buffers allocated successfully");
            
            // Cleanup
            free_buffer(main_buffer);
        }
        
        free(temp_buffer);
        BeaconPrintf(CALLBACK_OUTPUT, "Temporary buffer freed");
    }
    
    print_message("Demo completed");
    BeaconPrintf(CALLBACK_OUTPUT, "=== End of Demo ===");
}
