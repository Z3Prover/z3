#ifdef _WINDOWS
#include <windows.h>
#endif
#include "instruction_count.h"

#ifdef _WINDOWS
typedef BOOL (WINAPI *QTCP)(HANDLE, PULONG64);
static QTCP QTCP_proc;
BOOL WINAPI dummy_qtcp(HANDLE h, PULONG64 u)
{
    *u = 0;
    return 0;
}

inline void check_handler()
{
    if (!QTCP_proc) {
        QTCP_proc = (QTCP) GetProcAddress(GetModuleHandle(TEXT("kernel32.dll")), "QueryThreadCycleTime");
        if (!QTCP_proc)
            QTCP_proc = &dummy_qtcp;
    }
}
#endif

void instruction_count::start() {
    m_count = 0;
#ifdef _WINDOWS
    check_handler();
    QTCP_proc(GetCurrentThread(), &m_count);
#endif
}

double instruction_count::get_num_instructions() {
    unsigned long long current = 0;
#ifdef _WINDOWS
    check_handler();
    QTCP_proc(GetCurrentThread(), &current);
#endif
    return static_cast<double>(current - m_count);
}

