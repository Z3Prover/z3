#include "api/z3.h"
#include "util/util.h"

extern "C" {
    void Z3_API Z3_set_exit_action_to_throw_exception() {
        set_default_exit_action(exit_action::throw_exception);
    }
}