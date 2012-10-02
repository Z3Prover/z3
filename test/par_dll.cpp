#include "z3.h"
#include "windows.h"

class thread_check {

    CRITICAL_SECTION m_cs;

    static DWORD __stdcall do_check(LPVOID _this) {
        thread_check* th = static_cast<thread_check*>(_this);
        Z3_config cfg = Z3_mk_config();
        Z3_set_param_value(cfg,"MODEL","true");
        Z3_context ctx = Z3_mk_context(cfg);
        Z3_parse_smtlib_string(ctx, "(benchmark b :logic QF_UF :extrafuns ((f U U) (x U)) :formula (= (f x) x))", 0, 0, 0, 0, 0, 0);
        Z3_ast f = Z3_get_smtlib_formula(ctx, 0);
        Z3_assert_cnstr(ctx, f);
        Z3_model m = 0;
        Z3_lbool r = Z3_check_and_get_model(ctx,&m);
        EnterCriticalSection(&th->m_cs);
        printf("%d\n", r);
        LeaveCriticalSection(&th->m_cs);
        if (m) {
            Z3_del_model(ctx, m);
        }
        return 0;
    }


public:
    thread_check() {
        InitializeCriticalSection(&m_cs);
    }

    ~thread_check() {
        DeleteCriticalSection(&m_cs);
    }

    void do_checks(unsigned num_threads) {
        HANDLE* handles = new HANDLE[num_threads];
        for (unsigned i = 0; i < num_threads; ++i) {
            HANDLE hThread = CreateThread(NULL, 0, &thread_check::do_check, this, 0, 0);
            handles[i] = hThread;
        }

        WaitForMultipleObjects(num_threads, handles, TRUE, INFINITE);

        for (unsigned i = 0; i < num_threads; ++i) {
            CloseHandle(handles[i]);
        }
        delete[] handles;
    }
};
   
extern "C"
__declspec(dllexport) int ChessTestRun() {
    thread_check tc;
    tc.do_checks(2);
    return 0;
}
