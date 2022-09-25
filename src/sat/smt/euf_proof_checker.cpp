/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_proof_checker.cpp

Abstract:

    Plugin manager for checking EUF proofs

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/

#include "util/union_find.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "sat/smt/euf_proof_checker.h"
#include "sat/smt/arith_proof_checker.h"

namespace euf {

    /**
     * The equality proof checker checks congruence proofs.
     * A congruence claim comprises
     *   - a set of equality and diseqality literals that are
     *     unsatisfiable modulo equality reasoning.
     *   - a list of congruence claims that are used for equality reasoning.
     *     Congruence claims are expressions of the form
     *     (cc uses_commutativity (= a b))
     *     where uses_commutativity is true or false
     *     If uses commutativity is true, then a, b are (the same) binary functions 
     *     a := f(x,y), b := f(z,u), such that x = u and y = z are consequences from 
     *     the current equalities.
     *     If uses_commtativity is false, then a, b are the same n-ary expressions
     *     each argument position i, a_i == b_i follows from current equalities.
     *     If the arguments are equal according to the current equalities, then the equality
     *     a = b is added as a consequence.
     *
     * The congruence claims can be justified from the equalities in the literals.
     * To be more precise, the congruence claims are justified in the they appear.
     * The congruence closure algorithm (egraph) uses timestamps to record a timestamp
     * when a congruence was inferred. Proof generation ensures that the congruence premises
     * are sorted by the timestamp such that a congruence that depends on an earlier congruence
     * appears later in the sorted order.
     *
     * Equality justifications are checked using union-find. 
     * We use union-find instead of fine-grained equality proofs (symmetry and transitivity
     * of equality) assuming that it is both cheap and simple to establish a certified
     * union-find checker.
     */

    class eq_proof_checker : public proof_checker_plugin {
        ast_manager&     m;
        basic_union_find m_uf;
        svector<std::pair<unsigned, unsigned>> m_expr2id;
        svector<std::pair<expr*,expr*>> m_diseqs;
        unsigned         m_ts = 0;
        
        void merge(expr* x, expr* y) {
            m_uf.merge(expr2id(x), expr2id(y));
            IF_VERBOSE(10, verbose_stream() << "merge " << mk_bounded_pp(x, m) << " == " << mk_bounded_pp(y, m) << "\n");
        }

        bool are_equal(expr* x, expr* y) {
            return m_uf.find(expr2id(x)) == m_uf.find(expr2id(y));
        }

        bool congruence(bool comm, app* x, app* y) {
            if (x->get_decl() != y->get_decl())
                return false;
            if (x->get_num_args() != y->get_num_args())
                return false;
            if (comm) {
                if (x->get_num_args() != 2)
                    return false;
                if (!are_equal(x->get_arg(0), y->get_arg(1)))
                    return false;
                if (!are_equal(y->get_arg(0), x->get_arg(1)))
                    return false;
                merge(x, y);
            }
            else {
                for (unsigned i = 0; i < x->get_num_args(); ++i)
                    if (!are_equal(x->get_arg(i), y->get_arg(i)))
                        return false;
                merge(x, y);
            }
            IF_VERBOSE(10, verbose_stream() << "cc " << mk_bounded_pp(x, m) << " == " << mk_bounded_pp(y, m) << "\n");
            return true;
        }

        void reset() {
            ++m_ts;
            if (m_ts == 0) {
                m_expr2id.reset();
                ++m_ts;
            }
            m_uf.reset();
            m_diseqs.reset();
        }

        unsigned expr2id(expr* e) {
            auto [ts, id] = m_expr2id.get(e->get_id(), {0,0});
            if (ts != m_ts) {
                id = m_uf.mk_var();
                m_expr2id.setx(e->get_id(), {m_ts, id}, {0,0});
            }
            return id;
        }
        

    public:
        eq_proof_checker(ast_manager& m): m(m) {}

        ~eq_proof_checker() override {}

        bool check(expr_ref_vector const& clause, app* jst, expr_ref_vector& units) override {
            IF_VERBOSE(10, verbose_stream() << clause << "\n" << mk_pp(jst, m) << "\n");
            reset();
            expr_mark pos, neg;
            expr* x, *y;
            for (expr* e : clause)
                if (m.is_not(e, e))
                    neg.mark(e, true);
                else
                    pos.mark(e, true);

            for (expr* arg : *jst) {
                if (m.is_bool(arg)) { 
                    bool sign = m.is_not(arg, arg);
                    if (sign && !pos.is_marked(arg))
                        units.push_back(m.mk_not(arg));
                    else if (!sign & !neg.is_marked(arg))
                        units.push_back(arg);
                    if (m.is_eq(arg, x, y)) {
                        if (sign)
                            m_diseqs.push_back({x, y});
                        else 
                            merge(x, y);
                    }
                    else 
                        IF_VERBOSE(0, verbose_stream() << "TODO " << mk_pp(arg, m) << " " << sign << "\n");
                }
                else if (m.is_proof(arg)) {
                    if (!is_app(arg))
                        return false;
                    app* a = to_app(arg);
                    if (a->get_num_args() != 2)
                        return false;
                    if (a->get_name() != symbol("cc"))
                        return false;
                    if (!m.is_eq(a->get_arg(1), x, y))
                        return false;
                    if (!is_app(x) || !is_app(y))
                        return false;
                    if (!congruence(m.is_true(a->get_arg(0)), to_app(x), to_app(y))) {
                        IF_VERBOSE(0, verbose_stream() << "not congruent " << mk_pp(a, m) << "\n");
                        return false;
                    }
                }
                else {
                    IF_VERBOSE(0, verbose_stream() << "unrecognized argument " << mk_pp(arg, m) << "\n");
                    return false;
                }                
            }
            for (auto const& [a, b] : m_diseqs)
                if (are_equal(a, b))
                    return true;            
            return false;
        }

        void register_plugins(proof_checker& pc) override {
            pc.register_plugin(symbol("euf"), this);
        }

    };

    proof_checker::proof_checker(ast_manager& m):
        m(m) {
        arith::proof_checker* apc = alloc(arith::proof_checker, m);
        eq_proof_checker* epc = alloc(eq_proof_checker, m);
        m_plugins.push_back(apc);
        m_plugins.push_back(epc);
        apc->register_plugins(*this);
        epc->register_plugins(*this);
    }

    proof_checker::~proof_checker() {}

    void proof_checker::register_plugin(symbol const& rule, proof_checker_plugin* p) {
        m_map.insert(rule, p);
    }

    bool proof_checker::check(expr_ref_vector const& clause, expr* e, expr_ref_vector& units) {
        if (!e || !is_app(e))
            return false;
        units.reset();
        app* a = to_app(e);
        proof_checker_plugin* p = nullptr;
        if (m_map.find(a->get_decl()->get_name(), p)) 
            return p->check(clause, a, units);
        return false;
    }

}

