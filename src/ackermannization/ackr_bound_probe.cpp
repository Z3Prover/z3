/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  ackr_bound_probe.cpp

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
--*/
#include "ast/array_decl_plugin.h"
#include "ast/ast_smt2_pp.h"
#include "ackermannization/ackr_helper.h"
#include "ackermannization/ackr_bound_probe.h"

/*
  For each function f, calculate the number of its occurrences o_f and compute "o_f choose 2".
  The probe then sums up these for all functions.
  This upper bound might be crude because some congruence lemmas trivially simplify to true.
*/
class ackr_bound_probe : public probe {

    struct proc {
        typedef ackr_helper::fun2terms_map fun2terms_map;
        typedef ackr_helper::sel2terms_map sel2terms_map;
        typedef ackr_helper::app_set       app_set;
        ast_manager&                 m;
        fun2terms_map                m_fun2terms; // a map from functions to occurrences
        sel2terms_map                m_sel2terms; // a map from functions to occurrences
        ackr_helper                  m_ackr_helper;
        expr_mark                    m_non_select;

        proc(ast_manager & m) : m(m), m_ackr_helper(m) { }

        ~proc() {
            for (auto & kv : m_fun2terms) {
                dealloc(kv.m_value);
            }
            for (auto & kv : m_sel2terms) {
                dealloc(kv.m_value);
            }
        }

        void prune_non_select() {
            m_ackr_helper.prune_non_select(m_sel2terms, m_non_select);
        }

        void operator()(quantifier *) {}
        void operator()(var *) {}
        void operator()(app * a) { 
            m_ackr_helper.mark_non_select(a, m_non_select);
            m_ackr_helper.insert(m_fun2terms, m_sel2terms, a); 
        }
    };

public:
    ackr_bound_probe() {}

    result operator()(goal const & g) override {
        proc p(g.m());
        unsigned sz = g.size();
        expr_fast_mark1 visited;
        for (unsigned i = 0; i < sz; i++) {
            for_each_expr_core<proc, expr_fast_mark1, true, true>(p, visited, g.form(i));
        }
        p.prune_non_select();
        double total = ackr_helper::calculate_lemma_bound(p.m_fun2terms, p.m_sel2terms);
        TRACE("ackermannize", tout << "total=" << total << std::endl;);
        return result(total);
    }

    inline static unsigned n_choose_2(unsigned n) { return n & 1 ? (n * (n >> 1)) : (n >> 1) * (n - 1); }
};

probe * mk_ackr_bound_probe() {
    return alloc(ackr_bound_probe);
}
