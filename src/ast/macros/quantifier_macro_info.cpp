/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    quantifier_macro_info.cpp

Abstract:

    Macro solving utilities

Author:

    Leonardo de Moura (leonardo) 2010-12-17.

Revision History:

--*/
#include "ast/ast_pp.h"
#include "ast/macros/quantifier_macro_info.h"

quantifier_macro_info::quantifier_macro_info(ast_manager& m, quantifier* q) :
    m(m),
    m_flat_q(q, m),
    m_is_auf(true),
    m_has_x_eq_y(false),
    m_the_one(m) {
    collect_macro_candidates(q);
}

void quantifier_macro_info::collect_macro_candidates(quantifier* q) {
    macro_util mutil(m);
    macro_util::macro_candidates candidates(m);
    quantifier_ref qa(q, m);
    if (is_exists(q))
        qa = m.update_quantifier(q, quantifier_kind::forall_k, m.mk_not(q->get_expr()));
    mutil.collect_macro_candidates(qa, candidates);
    unsigned num_candidates = candidates.size();
    for (unsigned i = 0; i < num_candidates; i++) {
        cond_macro* mc = alloc(cond_macro, m, candidates.get_f(i), candidates.get_def(i), candidates.get_cond(i),
                               candidates.ineq(i), candidates.satisfy_atom(i), candidates.hint(i), q->get_weight());
        insert_macro(mc);
    }
}


bool quantifier_macro_info::unary_function_fragment() const {
    unsigned sz = m_ng_decls.size();
    if (sz > 1)
        return false;
    if (sz == 0)
        return true;
    func_decl* f = *(m_ng_decls.begin());
    return f->get_arity() == 1;
}

std::ostream& quantifier_macro_info::display(std::ostream& out) const {
    out << "info for quantifier:\n" << mk_pp(m_flat_q, m) << "\n";
    out << "IS_AUF: " << m_is_auf << ", has x=y: " << m_has_x_eq_y << "\n";
    out << "unary function fragment: " << unary_function_fragment() << "\n";
    out << "ng decls: ";
    for (func_decl* f : m_ng_decls)
        out << f->get_name() << " ";
    out << "\nmacros:\n";
    for (cond_macro* cm : m_cond_macros)
        cm->display(out << "  ") << "\n";
    return out;
}
