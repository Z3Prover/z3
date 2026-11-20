/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    params.cpp

Abstract:

    Tests for default (flagged) entries of params_ref.

--*/
#include "util/params.h"
#include "params/smt_params_helper.hpp"
#include "util/debug.h"
#include <cstring>

static void tst_set_default() {
    params_ref p;
    p.set_default_bool("som", true);
    ENSURE(p.contains("som") && p.is_default("som"));
    ENSURE(p.get_bool("som", false));

    // a default overwrites a default
    p.set_default_bool("som", false);
    ENSURE(p.is_default("som") && !p.get_bool("som", true));

    // a plain value overwrites a default and clears the flag
    p.set_bool("som", true);
    ENSURE(!p.is_default("som") && p.get_bool("som", false));

    // a default does not overwrite a plain value
    p.set_default_bool("som", false);
    ENSURE(!p.is_default("som") && p.get_bool("som", false));

    p.set_default_uint("max_occs", 2);
    p.set_default_double("ratio", 0.5);
    p.set_default_str("name", "abc");
    p.set_default_sym("mode", symbol("full"));
    ENSURE(p.is_default("max_occs") && p.get_uint("max_occs", 0) == 2);
    ENSURE(p.is_default("ratio") && p.get_double("ratio", 0.0) == 0.5);
    ENSURE(p.is_default("name") && strcmp(p.get_str("name", ""), "abc") == 0);
    ENSURE(p.is_default("mode") && p.get_sym("mode", symbol::null) == symbol("full"));
    ENSURE(!p.is_default("missing"));

    // removing an entry keeps the flags of the others
    p.reset("som");
    ENSURE(p.is_default("max_occs") && p.is_default("mode"));
}

static void tst_append() {
    params_ref user, author;
    user.set_bool("flat", false);
    user.set_default_bool("som", false);
    author.set_default_bool("flat", true);     // must not override the user value
    author.set_default_bool("som", true);      // overrides another default
    author.set_default_bool("hoist_mul", true); // absent: added as a default

    params_ref r = user;
    r.append(author);
    ENSURE(!r.get_bool("flat", true) && !r.is_default("flat"));
    ENSURE(r.get_bool("som", false) && r.is_default("som"));
    ENSURE(r.get_bool("hoist_mul", false) && r.is_default("hoist_mul"));

    // other direction: unflagged entries overwrite as before
    params_ref r2 = author;
    r2.append(user);
    ENSURE(!r2.get_bool("flat", true) && !r2.is_default("flat"));
    ENSURE(!r2.get_bool("som", true) && r2.is_default("som"));
    ENSURE(r2.get_bool("hoist_mul", false) && r2.is_default("hoist_mul"));

    // appending to an empty params_ref shares the entries, flags included
    params_ref r3;
    r3.append(author);
    ENSURE(r3.is_default("flat") && r3.is_default("som"));

    // copy on write keeps the flags
    params_ref r4 = author;
    r4.set_bool("other", true);
    ENSURE(r4.is_default("flat") && !r4.is_default("other"));
    ENSURE(author.is_default("flat") && !author.contains("other"));
}

static void tst_string_solver_default() {
    params_ref p;
    smt_params_helper h(p);
    ENSURE(h.string_solver() == symbol("auto"));
}

static void tst_fallback() {
    params_ref local, global;
    local.set_default_bool("som", true);
    local.set_default_uint("max_occs", 2);
    local.set_bool("flat", true);
    global.set_bool("som", false);
    global.set_bool("flat", false);

    // a default yields to the fallback if the fallback has the key
    ENSURE(!local.get_bool("som", global, true));
    // ... and is used otherwise
    ENSURE(local.get_uint("max_occs", global, 7) == 2);
    // an unflagged entry wins over the fallback, as before
    ENSURE(local.get_bool("flat", global, false));
    // the getters without fallback see the default
    ENSURE(local.get_bool("som", false));
    // a fallback entry of another kind is ignored
    global.set_uint("max_occs", 3);
    ENSURE(local.get_uint("max_occs", global, 7) == 3);
    params_ref wrong_kind;
    wrong_kind.set_bool("max_occs", true);
    ENSURE(local.get_uint("max_occs", wrong_kind, 7) == 2);
}

void tst_params() {
    tst_set_default();
    tst_append();
    tst_fallback();
    tst_string_solver_default();
}
