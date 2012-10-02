/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    mem_stat.cpp

Abstract:

    Memory usage statistics

Author:

    Leonardo de Moura (leonardo) 2006-11-09.

Revision History:

--*/

#ifdef _WINDOWS
#include<windows.h>
#include<cstdio>
#include<psapi.h>

double get_max_heap_size() {
    DWORD processID = GetCurrentProcessId();
    HANDLE hProcess;
    PROCESS_MEMORY_COUNTERS pmc;
    
    hProcess = OpenProcess(PROCESS_QUERY_INFORMATION |
                           PROCESS_VM_READ,
                           FALSE, processID);
    double result = -1.0;

    if (NULL == hProcess) {
        return -1.0;
    }
    
    if (GetProcessMemoryInfo( hProcess, &pmc, sizeof(pmc))) {
        result = static_cast<double>(pmc.PeakWorkingSetSize) / static_cast<double>(1024*1024);
    }

    CloseHandle( hProcess );

    return result;
}

#else

double get_max_heap_size() {
    // not available in this platform
    return -1.0;
}

#endif

