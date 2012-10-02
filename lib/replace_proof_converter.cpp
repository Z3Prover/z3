/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    replace_proof_converter.cpp

Abstract:

    Proof converter that replaces asserted by sub-proof.

Author:

    Nikolaj Bjorner (nbjorner) 2012-9-16

Revision History:

--*/

#include "replace_proof_converter.h"
#include "expr_functors.h"
#include "ast_pp.h"
#include "for_each_expr.h"

/**
   \brief Replace expressions by other expressions.
   
   replace_map is caching, so inserting src |-> dst has no effect if
   src is a sub-expression of something that has already been visited.
   The assumption is that proof replacements are inserted into
   the replace_proof_converter in the order that they are introduced, so 
   there are no such clashes.

   map_proc is used as expr_replacer behaves differently 
   when proof mode is turned on.
*/
class replace_map : public map_proc {
public:
    replace_map(ast_manager& m): map_proc(m) {}

    void insert(expr* src, expr* dst) {
        m_map.insert(src, dst, 0);
    }

    void operator()(var* v) { visit(v); }
    void operator()(app* a) { if (!get_expr(a)) { reconstruct(a); }  }
    void operator()(quantifier* q) { visit(q); }
    
    void apply(expr_ref& e) {
        for_each_expr(*this, e);
        e = get_expr(e);
    }
};


void replace_proof_converter::operator()(ast_manager & m, unsigned num_source, 
                                         proof * const * source, proof_ref & result) {    
    SASSERT(num_source == 1);
    replace_map replace(m);
    proof_ref p(m);
    expr_ref tmp(source[0], m), e(m), f(m);
    
    // apply the substitution to the prefix before inserting it.
    for (unsigned i = 0; i < m_proofs.size(); ++i) {
        p = m_proofs[i].get();
        e = p;
        replace.apply(e);
        f = m.mk_asserted(m.get_fact(p));
        replace.insert(f, e);
        TRACE("proof_converter", tout << f->get_id() << " " << mk_pp(f, m) << 
              "\n|-> " << mk_pp(e, m) << "\n";);
    }    
    replace.apply(tmp);
    TRACE("proof_converter", tout << mk_pp(source[0], m) << "\n";
                             tout << mk_pp(tmp.get(), m) << "\n";);
    result = to_app(tmp);
}

proof_converter * replace_proof_converter::translate(ast_translation & translator) {
    replace_proof_converter* rp = alloc(replace_proof_converter, m);
    for (unsigned i = 0; i < m_proofs.size(); ++i) {
        rp->insert(translator(m_proofs[i].get()));
    }
    return rp;
}

