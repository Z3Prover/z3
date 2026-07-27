
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "api/z3.h"
#include "api/z3_private.h"
#include <iostream>
#include "util/util.h"
#include "util/trace.h"

static bool oom = false;
static unsigned oom_handler_calls = 0;
static Z3_error_code oom_handler_last_code = Z3_OK;


static void err_handler(Z3_context c, Z3_error_code e) {
    oom = true;
    throw std::bad_alloc();
}

static void err_handler_noexcept(Z3_context, Z3_error_code e) {
    ++oom_handler_calls;
    oom_handler_last_code = e;
}

static void hit_me(char const* wm) {
    Z3_config cfg;
    Z3_context ctx;

    oom = false;

    cfg = Z3_mk_config();
    if (!cfg) {
        return;
    }
    Z3_global_param_set("MEMORY_MAX_SIZE", wm);
    ctx = Z3_mk_context(cfg);
    if (ctx) {
        Z3_set_error_handler(ctx, &err_handler);
    
        unsigned i;
        for (i = 1; !oom ; ++i) {
            try {
                Z3_mk_bv_sort(ctx,i);      
                
            }
            catch (const std::bad_alloc&) {
                std::cout << "caught\n";
            }
        }
        std::cout << "oom " << i << "\n";
        Z3_del_context(ctx);
    }   
    Z3_del_config(cfg);
}

static void solver_reset_after_oom(char const* wm) {
    Z3_config cfg;
    Z3_context ctx;

    oom_handler_calls = 0;
    oom_handler_last_code = Z3_OK;

    cfg = Z3_mk_config();
    if (!cfg) {
        return;
    }
    Z3_global_param_set("MEMORY_MAX_SIZE", wm);
    ctx = Z3_mk_context(cfg);
    if (ctx) {
        Z3_set_error_handler(ctx, &err_handler_noexcept);
        Z3_solver s = Z3_mk_solver(ctx);
        Z3_symbol p = Z3_mk_string_symbol(ctx, "p");
        Z3_ast b = Z3_mk_const(ctx, p, Z3_mk_bool_sort(ctx));
        Z3_solver_assert(ctx, s, b);
        Z3_solver_check(ctx, s);
        for (unsigned i = 1; oom_handler_last_code != Z3_MEMOUT_FAIL; ++i) {
            Z3_mk_bv_sort(ctx, i);
        }
        VERIFY(oom_handler_last_code == Z3_MEMOUT_FAIL);
        VERIFY(oom_handler_calls > 0);
        Z3_solver_reset(ctx, s);
        Z3_del_context(ctx);
    }
    Z3_del_config(cfg);
}

void tst_memory() {    
    hit_me("10");
    Z3_reset_memory();
    hit_me("20");
    Z3_reset_memory();
    hit_me("30");
    Z3_reset_memory();
    solver_reset_after_oom("30");
    Z3_reset_memory();
    Z3_global_param_set("MEMORY_MAX_SIZE", "0");

}
