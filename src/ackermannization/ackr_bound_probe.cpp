/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  ackr_bound_probe.cpp

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
--*/
#include"ackr_helper.h"
#include"ackr_bound_probe.h"
#include"ast_smt2_pp.h"

/*
  For each function f, calculate the number of its occurrences o_f and compute "o_f choose 2".
  The probe then sums up these for all functions.
  This upper bound might be crude because some congruence lemmas trivially simplify to true.
*/
class ackr_bound_probe : public probe {
    struct proc {
        typedef ackr_helper::fun2terms_map fun2terms_map;
        typedef ackr_helper::app_set       app_set;
        ast_manager&                 m_m;
        fun2terms_map                m_fun2terms; // a map from functions to occurrences
        ackr_helper                  m_ackr_helper;

        proc(ast_manager & m) : m_m(m), m_ackr_helper(m) { }

        ~proc() {
            fun2terms_map::iterator it = m_fun2terms.begin();
            const fun2terms_map::iterator end = m_fun2terms.end();
            for (; it != end; ++it) dealloc(it->get_value());
        }

        void operator()(quantifier *) {}
        void operator()(var *) {}
        void operator()(app * a) {
            if (a->get_num_args() == 0) return;
            if (!m_ackr_helper.should_ackermannize(a)) return;
            func_decl* const fd = a->get_decl();
            app_set* ts = 0;
            if (!m_fun2terms.find(fd, ts)) {
                ts = alloc(app_set);
                m_fun2terms.insert(fd, ts);
            }
            ts->insert(a);
        }
    };

public:
    ackr_bound_probe() {}

    virtual result operator()(goal const & g) {
        proc p(g.m());
        unsigned sz = g.size();
        expr_fast_mark1 visited;
        for (unsigned i = 0; i < sz; i++) {
            for_each_expr_core<proc, expr_fast_mark1, true, true>(p, visited, g.form(i));
        }
        const double total = ackr_helper::calculate_lemma_bound(p.m_fun2terms);
        TRACE("ackr_bound_probe", tout << "total=" << total << std::endl;);
        return result(total);
    }

    inline static unsigned n_choose_2(unsigned n) { return n & 1 ? (n * (n >> 1)) : (n >> 1) * (n - 1); }
};

probe * mk_ackr_bound_probe() {
    return alloc(ackr_bound_probe);
}
