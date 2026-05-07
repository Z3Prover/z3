/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    nseq_context_solver.h

Abstract:

    context_solver: concrete implementation of seq::simple_solver
    that delegates arithmetic feasibility checks to an smt::kernel
    configured with seq.solver = "seq_len".

    Each call to assert_expr(e, dep) with a non-null dep creates a fresh
    Boolean assumption literal `a` and asserts `a => e` into the kernel.
    The literal-to-dep mapping is maintained across push/pop scopes.
    After check() returns l_false, core() returns the joined dep_tracker
    for all assumption literals that appear in the kernel's UNSAT core.

Author:

    Nikolaj Bjorner (nbjorner) 2026-03-10

--*/
#pragma once

#include "smt/seq/seq_nielsen.h"
#include "smt/smt_kernel.h"
#include "smt/smt_arith_value.h"
#include "params/smt_params.h"
#include "util/map.h"

namespace smt {

    /**
     * Concrete simple_solver that wraps smt::kernel.
     * Initializes the kernel with seq.solver = "seq_len" so that
     * sequence length constraints are handled by theory_seq_len.
     *
     * Assertions with a non-null dep_tracker are converted to assumption-
     * literal form: a fresh bool `a` is introduced, `(or (not a) e)` is
     * asserted, and the mapping a.id -> dep is tracked per push/pop scope.
     * After an UNSAT check(), core() returns the union of the deps for the
     * literals that appear in the kernel's UNSAT core.
     *
     * Assertions with dep == nullptr are asserted directly (always active).
     */
    class context_solver : public seq::simple_solver {
        smt_params      m_params;    // must be declared before m_kernel
        kernel          m_kernel;
        arith_value     m_arith_value;

        // Tracked assumption literals.
        // m_assump_lits[i] and m_frame_bounds together encode a stack of
        // frames, one frame per push().  pop(n) removes the top n frames.
        expr_ref_vector               m_assump_lits;   // live assumption exprs
        svector<unsigned>             m_frame_bounds;  // m_assump_lits.size() at each push()
        u_map<seq::dep_tracker>       m_lid_to_dep;    // literal expr-id -> dep

        // Scratch dep_manager for joining core deps; reset before each check().
        seq::dep_manager              m_core_dep_mgr;
        seq::dep_tracker              m_last_core = nullptr;

        static smt_params make_seq_len_params() {
            smt_params p;
            p.m_string_solver = symbol("seq_len");
            return p;
        }

    public:
        context_solver(ast_manager& m) :
            m_params(make_seq_len_params()),
            m_kernel(m, m_params),
            m_arith_value(m),
            m_assump_lits(m) {
            m_arith_value.init(&m_kernel.get_context());
        }

        lbool check() override {
            m_core_dep_mgr.reset();
            m_last_core = nullptr;
            lbool r;
            if (m_assump_lits.empty()) {
                r = m_kernel.check();
            } else {
                r = m_kernel.check(m_assump_lits.size(), m_assump_lits.data());
                if (r == l_false) {
                    unsigned cnt = m_kernel.get_unsat_core_size();
                    for (unsigned i = 0; i < cnt; ++i) {
                        expr* ce = m_kernel.get_unsat_core_expr(i);
                        seq::dep_tracker d = nullptr;
                        if (m_lid_to_dep.find(ce->get_id(), d))
                            m_last_core = m_core_dep_mgr.mk_join(m_last_core, d);
                    }
                }
            }
            return r;
        }

        void assert_expr(expr* e, seq::dep_tracker dep) override {
            if (!dep) {
                m_kernel.assert_expr(e);
                return;
            }
            ast_manager& m = m_kernel.m();
            expr_ref lit(m.mk_fresh_const("_a", m.mk_bool_sort()), m);
            m_kernel.assert_expr(m.mk_or(m.mk_not(lit), e));
            m_lid_to_dep.insert_if_not_there(lit->get_id(), dep);
            m_assump_lits.push_back(lit);
        }

        void push() override {
            m_kernel.push();
            m_frame_bounds.push_back((unsigned)m_assump_lits.size());
        }

        void pop(unsigned n) override {
            SASSERT(n <= m_frame_bounds.size());
            unsigned target = m_frame_bounds[m_frame_bounds.size() - n];
            while ((unsigned)m_assump_lits.size() > target) {
                m_lid_to_dep.erase(m_assump_lits.back()->get_id());
                m_assump_lits.pop_back();
            }
            for (unsigned i = 0; i < n; ++i)
                m_frame_bounds.pop_back();
            m_kernel.pop(n);
        }

        void get_model(model_ref& mdl) override {
            m_kernel.get_model(mdl);
        }

        seq::dep_tracker core() override { return m_last_core; }

        bool lower_bound(expr* e, rational& lo) const override {
            bool is_strict = true;
            return m_arith_value.get_lo(e, lo, is_strict) && !is_strict && lo.is_int();
        }

        bool upper_bound(expr* e, rational& hi) const override {
            bool is_strict = true;
            return m_arith_value.get_up(e, hi, is_strict) && !is_strict && hi.is_int();
        }

        bool current_value(expr* e, rational& v) const override {
            return m_arith_value.get_value(e, v) && v.is_int();
        }

        void reset() override {
            m_kernel.reset();
            m_arith_value.init(&m_kernel.get_context());
            m_assump_lits.reset();
            m_frame_bounds.reset();
            m_lid_to_dep.reset();
            m_core_dep_mgr.reset();
            m_last_core = nullptr;
        }
    };

}
