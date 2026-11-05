/*++
Copyright (c) 2026 Romain Soulat

    Rejected online proof inferences must fail without terminating the caller.
--*/
#include "ast/reg_decl_plugins.h"
#include "sat/smt/euf_proof_checker.h"
#include "util/debug.h"
#include "util/z3_exception.h"

void tst_smt_proof_checker() {
    ast_manager m;
    reg_decl_plugins(m);
    params_ref params;
    euf::smt_proof_checker checker(m, params);
    app_ref hint(m.mk_const("test-unsupported-hint", m.mk_proof_sort()), m);
    expr_ref p(m.mk_const("p", m.mk_bool_sort()), m);
    expr_ref_vector clause(m);
    // Negating this invalid unit temporarily assumes !p in the fallback solver.
    // If that assumption leaks, the next invalid !p unit would appear valid.
    for (unsigned i = 0; i < 3; ++i) {
        clause.reset();
        clause.push_back(i % 2 ? m.mk_not(p) : p.get());
        bool rejected = false;
        try { checker.infer(clause, hint); }
        catch (default_exception const& ex) {
            rejected = std::string(ex.what()) == "SMT proof verification failed";
        }
        ENSURE(rejected);
    }
    clause.reset();
    clause.push_back(p);
    clause.push_back(m.mk_not(p));
    checker.infer(clause, hint);
    // A previous accepted tautology must not authorize the empty clause.
    clause.reset();
    bool rejected = false;
    try { checker.infer(clause, hint); }
    catch (default_exception const&) { rejected = true; }
    ENSURE(rejected);
}
