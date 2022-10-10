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
#include "ast/ast_util.h"
#include "ast/ast_ll_pp.h"
#include "sat/smt/euf_proof_checker.h"
#include "sat/smt/arith_proof_checker.h"
#include "sat/smt/q_proof_checker.h"
#include "sat/smt/tseitin_proof_checker.h"
#include <iostream>

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
        ptr_vector<expr>                       m_id2expr;
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
                m_id2expr.setx(id, e, nullptr);
            }
            return id;
        }                

    public:
        eq_proof_checker(ast_manager& m): m(m) {}

        ~eq_proof_checker() override {}

        expr_ref_vector clause(app* jst) override {
            expr_ref_vector result(m);
            for (expr* arg : *jst) 
                if (m.is_bool(arg)) 
                    result.push_back(mk_not(m, arg));
            return result;
        }

        bool check(app* jst) override {
            IF_VERBOSE(10, verbose_stream() << mk_pp(jst, m) << "\n");
            reset();

            for (expr* arg : *jst) {
                expr* x, *y;
                bool sign = m.is_not(arg, arg);

                if (m.is_bool(arg)) {
                    if (m.is_eq(arg, x, y)) {
                        if (sign)
                            m_diseqs.push_back({x, y});
                        else 
                            merge(x, y);
                    }
                    merge(arg, sign ? m.mk_false() : m.mk_true());
                }
                else if (m.is_proof(arg)) {
                    if (!is_app(arg))
                        return false;
                    app* a = to_app(arg);
                    if (a->get_num_args() != 1)
                        return false;
                    if (!m.is_eq(a->get_arg(0), x, y))
                        return false;
                    bool is_cc = a->get_name() == symbol("cc");
                    bool is_comm = a->get_name() == symbol("comm");
                    if (!is_cc && !is_comm)
                        return false;
                    if (!is_app(x) || !is_app(y))
                        return false;
                    if (!congruence(!is_cc, to_app(x), to_app(y))) {
                        IF_VERBOSE(0, verbose_stream() << "not congruent " << mk_pp(a, m) << "\n");
                        return false;
                    }
                }
                else {
                    IF_VERBOSE(0, verbose_stream() << "unrecognized argument " << mk_pp(arg, m) << "\n");
                    return false;
                }                
            }
            // check if a disequality is violated.
            for (auto const& [a, b] : m_diseqs)
                if (are_equal(a, b))
                    return true;

            // check if some equivalence class contains two distinct values.            
            for (unsigned v = 0; v < m_uf.get_num_vars(); ++v) {
                if (v != m_uf.find(v))
                    continue;
                unsigned r = v;
                expr* val = nullptr;
                do {
                    expr* e = m_id2expr[v];
                    if (val && m.are_distinct(e, val))
                        return true;
                    if (m.is_value(e))
                        val = e;
                    v = m_uf.next(v);
                }
                while (r != v);
            }
            return false;
        }

        void register_plugins(proof_checker& pc) override {
            pc.register_plugin(symbol("euf"), this);
        }
    };

    /**
       A resolution proof term is of the form
       (res pivot proof1 proof2)
       The pivot occurs with opposite signs in proof1 and proof2
     */

    class res_proof_checker : public proof_checker_plugin {
        ast_manager&   m;
        proof_checker& pc;

    public:
        res_proof_checker(ast_manager& m, proof_checker& pc): m(m), pc(pc) {}
        
        ~res_proof_checker() override {}

        bool check(app* jst) override {
            if (jst->get_num_args() != 3)
                return false;
            auto [pivot, proof1, proof2] = jst->args3();
            if (!m.is_bool(pivot) || !m.is_proof(proof1) || !m.is_proof(proof2))
                return false;
            expr* narg;
            bool found1 = false, found2 = false, found3 = false, found4 = false;
            for (expr* arg : pc.clause(proof1)) {
                found1 |= arg == pivot;
                found2 |= m.is_not(arg, narg) && narg == pivot;
            }
            if (found1 == found2)
                return false;
            
            for (expr* arg : pc.clause(proof2)) {
                found3 |= arg == pivot;
                found4 |= m.is_not(arg, narg) && narg == pivot;
            }
            if (found3 == found4)
                return false;
            if (found3 == found1)
                return false;
            return pc.check(proof1) && pc.check(proof2);            
        }
        
        expr_ref_vector clause(app* jst) override {
            expr_ref_vector result(m);
            auto x = jst->args3();
            auto pivot  = std::get<0>(x);
            auto proof1 = std::get<1>(x);
            auto proof2 = std::get<2>(x);
            expr* narg;
            auto is_pivot = [&](expr* arg) {
                if (arg == pivot)
                    return true;
                return m.is_not(arg, narg) && narg == pivot;                
            };
            for (expr* arg : pc.clause(proof1))
                if (!is_pivot(arg))
                    result.push_back(arg);
            for (expr* arg : pc.clause(proof2))
                if (!is_pivot(arg))
                    result.push_back(arg);            
            return result;
        }

        void register_plugins(proof_checker& pc) override {
            pc.register_plugin(symbol("res"), this);
        }
    };

    proof_checker::proof_checker(ast_manager& m):
        m(m) {
        add_plugin(alloc(arith::proof_checker, m));
        add_plugin(alloc(eq_proof_checker, m));
        add_plugin(alloc(res_proof_checker, m, *this));
        add_plugin(alloc(q::proof_checker, m));
        add_plugin(alloc(smt_proof_checker_plugin, m, symbol("datatype"))); // no-op datatype proof checker
        add_plugin(alloc(tseitin::proof_checker, m));
    }

    proof_checker::~proof_checker() {
        for (auto& [k, v] : m_checked_clauses)
            dealloc(v);
    }

    void proof_checker::add_plugin(proof_checker_plugin* p) {
        m_plugins.push_back(p);
        p->register_plugins(*this);
    }

    void proof_checker::register_plugin(symbol const& rule, proof_checker_plugin* p) {
        m_map.insert(rule, p);
    }

    bool proof_checker::check(expr* e) {
        if (m_checked_clauses.contains(e))
            return true;        
        if (!e || !is_app(e))
            return false;
        app* a = to_app(e);
        proof_checker_plugin* p = nullptr;
        if (!m_map.find(a->get_decl()->get_name(), p))
            return false;
        if (!p->check(a)) 
            return false;        
        return true;
    }

    expr_ref_vector proof_checker::clause(expr* e) {
        expr_ref_vector* rr;
        if (m_checked_clauses.find(e, rr))
            return *rr;
        SASSERT(is_app(e) && m_map.contains(to_app(e)->get_name()));
        expr_ref_vector r = m_map[to_app(e)->get_name()]->clause(to_app(e));
        m_checked_clauses.insert(e, alloc(expr_ref_vector, r));
        return r;
    }

    bool proof_checker::vc(expr* e, expr_ref_vector const& clause, expr_ref_vector& v) {
        SASSERT(is_app(e));
        app* a = to_app(e);
        proof_checker_plugin* p = nullptr;
        if (m_map.find(a->get_name(), p))
            return p->vc(a, clause, v);
        IF_VERBOSE(0, verbose_stream() << "there is no proof plugin for " << mk_pp(e, m) << "\n");
        return false;
    }
   
    bool proof_checker::check(expr_ref_vector const& clause1, expr* e, expr_ref_vector & units) {
        if (!check(e))
            return false;
        units.reset();
        expr_mark literals;
        auto clause2 = clause(e);

        // check that all literals in clause1 are in clause2
        for (expr* arg : clause2)
            literals.mark(arg, true);
        for (expr* arg : clause1)
            if (!literals.is_marked(arg))
                return false;

        // extract negated units for literals in clause2 but not in clause1
        // the literals should be rup
        literals.reset();
        for (expr* arg : clause1)
            literals.mark(arg, true);
        for (expr* arg : clause2)
            if (!literals.is_marked(arg))
                units.push_back(mk_not(m, arg));

        return true;
    }

    expr_ref_vector smt_proof_checker_plugin::clause(app* jst) {
        expr_ref_vector result(m);
        SASSERT(jst->get_name() == m_rule);
        for (expr* arg : *jst) 
            result.push_back(mk_not(m, arg));
        return result;
    }
    
}

