/*++
Copyright (c) 2026 Romain Soulat

    Theory clause weakening preserves obligations for removed literals.
--*/
#include "ast/reg_decl_plugins.h"
#include "sat/smt/euf_proof_checker.h"
#include "util/debug.h"

void tst_smt_proof_weakening() {
    ast_manager m;
    reg_decl_plugins(m);
    euf::theory_checker checker(m);
    expr_ref p(m.mk_const("p", m.mk_bool_sort()), m);
    expr_ref guard(m.mk_const("guard", m.mk_bool_sort()), m);
    expr_ref not_p(m.mk_not(p), m);
    // The EUF checker certifies the tautology !p or p from p and !p.
    expr* premises[] = {p, not_p};
    app_ref hint(m.mk_app(symbol("euf"), 2, premises, m.mk_proof_sort()), m);
    expr_ref_vector clause(m), units(m);
    clause.push_back(p);
    clause.push_back(not_p);
    clause.push_back(guard);
    ENSURE(checker.check(clause, hint, units) && units.empty());
    clause.reset();
    clause.push_back(p);
    clause.push_back(guard);
    ENSURE(checker.check(clause, hint, units));
    ENSURE(units.size() == 1 && units[0] == p);
    clause.reset();
    clause.push_back(guard);
    ENSURE(checker.check(clause, hint, units) && units.size() == 2);
    ENSURE((units[0] == p && units[1] == not_p) ||
           (units[1] == p && units[0] == not_p));
    // Syntactic double negations do not create spurious unit obligations.
    clause.reset();
    clause.push_back(m.mk_not(m.mk_not(p)));
    clause.push_back(m.mk_not(m.mk_not(not_p)));
    clause.push_back(guard);
    ENSURE(checker.check(clause, hint, units) && units.empty());
    // Clause normalization must not turn a rejected hint into evidence.
    app_ref invalid(m.mk_const("unknown-rule", m.mk_proof_sort()), m);
    ENSURE(!checker.check(clause, invalid, units));
}
