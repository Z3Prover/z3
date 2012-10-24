#ifdef _WINDOWS
#include "z3.h"
#include "z3_private.h"
#include <iostream>
#include "util.h"
#include "trace.h"

static bool oom = false;


static void err_handler(Z3_context c, Z3_error_code e) {
    oom = true;
    throw std::bad_alloc();
}

static void hit_me(char const* wm) {
    Z3_config cfg;
    Z3_context ctx;

    oom = false;

    cfg = Z3_mk_config();
    Z3_set_param_value(cfg, "MEMORY_MAX_SIZE", wm);
    ctx = Z3_mk_context(cfg);
    Z3_set_error_handler(ctx, &err_handler);
    
    unsigned i;
    for (i = 1; !oom ; ++i) {
        try {
            Z3_mk_bv_sort(ctx,i);      
			
        }
        catch (std::bad_alloc) {
            std::cout << "caught\n";
        }
    }

    std::cout << "oom " << i << "\n";
}

void tst_memory() {    
    hit_me("1");
    Z3_reset_memory();
    hit_me("2");
    Z3_reset_memory();
    hit_me("3");
    Z3_reset_memory();

}

#else
void tst_memory() {    
}
#endif
