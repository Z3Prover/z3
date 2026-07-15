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
    class sub_solver : public seq::sub_solver_i {
        smt_params      m_params;    // must be declared before m_kernel
        kernel          m_kernel;

        // Tracked assumption literals.
        // m_assump_lits[i] and m_frame_bounds together encode a stack of
        // frames, one frame per push().  pop(n) removes the top n frames.
        expr_ref_vector               m_assump_lits;   // assumption exprs; they will be reused, so it only grows
        obj_map<expr, unsigned>       m_assump_lit2id; // the index represented by the assumption expression
        svector<unsigned>             m_frame_bounds;  // m_deps.size() at each push()
        svector<seq::dep_tracker>     m_deps;          // id -> dep

        seq::dep_manager              m_core_dep_mgr;
        seq::dep_tracker              m_last_core = nullptr;

        static smt_params make_seq_len_params() {
            smt_params p;
            p.m_string_solver = symbol("seq_len");
            return p;
        }

    public:
        sub_solver(ast_manager& m) :
            m_params(make_seq_len_params()),
            m_kernel(m, m_params),
            m_assump_lits(m) {
        }

        lbool check() override {
            // do NOT reset m_core_dep_mgr here. Core trees
            // returned by core() outlive this call. It is reset only in reset().
            m_last_core = m_core_dep_mgr.mk_empty();
            lbool r;
            if (m_deps.empty()) {
                r = m_kernel.check();
            } else {
                // Only the first m_deps.size() literals are bound to an active
                // (a => e) assertion; the tail of m_assump_lits holds recycled
                // literals from popped frames.  Passing those as assumptions is
                // pointless and, should one ever surface in a (non-minimal)
                // unsat core, m_deps[id] below would index past m_deps.size().
                r = m_kernel.check(m_deps.size(), m_assump_lits.data());
                if (r == l_false) {
                    const unsigned cnt = m_kernel.get_unsat_core_size();
                    for (unsigned i = 0; i < cnt; ++i) {
                        expr_ref ce(m_kernel.get_unsat_core_expr(i), m_kernel.m());
                        SASSERT(m_assump_lit2id.contains(ce));
                        const unsigned id = m_assump_lit2id[ce];
                        SASSERT(id < m_deps.size());
                        m_last_core = m_core_dep_mgr.mk_join(m_last_core, m_deps[id]);
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
            expr* l;
            if (m_assump_lits.size() <= m_deps.size()) {
                SASSERT(m_assump_lits.size() == m_deps.size());
                l = m.mk_fresh_const("_a", m.mk_bool_sort());
                m_assump_lit2id.insert(l, m_assump_lits.size());
                m_assump_lits.push_back(l);
            }
            else
                l = m_assump_lits.get(m_deps.size());
            m_kernel.assert_expr(m.mk_or(m.mk_not(l), e));
            m_deps.push_back(dep);
        }

        void push() override {
            m_kernel.push();
            m_frame_bounds.push_back(m_deps.size());
        }

        void pop(unsigned n) override {
            SASSERT(n <= m_frame_bounds.size());
            unsigned target = m_frame_bounds[m_frame_bounds.size() - n];
            m_deps.shrink(target);
            for (unsigned i = 0; i < n; i++) 
                m_frame_bounds.pop_back();            
            m_kernel.pop(n);
        }

        void get_model(model_ref& mdl) override {
            m_kernel.get_model(mdl);
        }

        seq::dep_tracker core() override { return m_last_core; }

        void reset() override {
            m_kernel.reset();
            m_assump_lits.reset();
            m_assump_lit2id.reset();
            m_frame_bounds.reset();
            m_deps.reset();
            m_core_dep_mgr.reset();
            m_last_core = nullptr;
        }
    };

    class context_solver : public seq::context_solver_i {
        smt::context &ctx;
        arith_value m_arith_value;
        std::function<void(expr*, expr*)> m_add_diseq_axiom;
    public:
        context_solver(smt::context& ctx, std::function<void(expr*, expr*)> add_diseq_axiom = nullptr): 
            ctx(ctx), 
            m_arith_value(ctx.get_manager()),
            m_add_diseq_axiom(add_diseq_axiom) {
            m_arith_value.init(&ctx);
        }

        void add_diseq_axiom(expr* e1, expr* e2) override {
            if (m_add_diseq_axiom)
                m_add_diseq_axiom(e1, e2);
        }

        bool lower_bound(expr *e, rational &lo, literal_vector &lits, enode_pair_vector &eqs) const override {
            bool is_strict = true;
            return m_arith_value.get_lo(e, lo, is_strict, lits, eqs) && !is_strict && lo.is_int();
        }

        bool upper_bound(expr *e, rational &hi, literal_vector &lits, enode_pair_vector &eqs) const override {
            bool is_strict = true;
            return m_arith_value.get_up(e, hi, is_strict, lits, eqs) && !is_strict && hi.is_int();
        }

        bool current_value(expr *e, rational &v) const override {
            return m_arith_value.get_value(e, v) && v.is_int();
        }

        sat::literal literal_if_false(expr *e) {
            bool is_not = ctx.get_manager().is_not(e, e);
            if (m_should_internalize && !ctx.b_internalized(e)) {
                // it can happen that the element is not internalized, but as soon as we do it, it becomes false.
                // In case we just skip one of those uninternalized expressions,
                // adding the Nielsen assumption later will fail
                // Alternatively, we could just retry Nielsen saturation in case
                // adding the Nielsen assumption yields the assumption being false after internalizing
                ctx.internalize(to_app(e), false);
            }

            if (!ctx.b_internalized(e))
                return sat::null_literal;

            literal lit = ctx.get_literal(e);
            if (is_not)
                lit.neg();
            if (ctx.get_assignment(lit) == l_false) {
                // TRACE(seq, tout << "literal_if_false: " << lit << " " << mk_pp(e, m) << " is assigned false\n");
                return lit;
            }
            // TRACE(seq, tout << "literal_if_false: " << mk_pp(e, m) << " is assigned " << ctx.get_assignment(lit) <<
            // "\n");
            return sat::null_literal;
        }
    };

}
