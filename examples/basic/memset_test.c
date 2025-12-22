#include <windows.h>
#include <string.h>
#include "beacon.h"

void go(void) {
    char buffer[64];

    // Use memset - should resolve to __imp_msvcrt$memset
    memset(buffer, 'A', sizeof(buffer) - 1);
    buffer[sizeof(buffer) - 1] = '\0';

    BeaconPrintf(CALLBACK_OUTPUT, "Buffer filled with: %s", buffer);

    DWORD pid = GetCurrentProcessId();
    BeaconPrintf(CALLBACK_OUTPUT, "Current process id is %lu", pid);
}
