#include "beacon.h"
#include <stdio.h>

// This function uses printf from msvcrt.dll
void print_message(const char* message) {
    // Note: In a real BOF, you'd use BeaconPrintf instead of printf
    // This is just to demonstrate import deduplication
    char buffer[256];
    int len = snprintf(buffer, sizeof(buffer), "[INFO] %s\n", message);
    
    if (len > 0 && len < sizeof(buffer)) {
        BeaconOutput(CALLBACK_OUTPUT, buffer, len);
    }
}
