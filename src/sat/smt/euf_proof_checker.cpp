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
#include "ast/arith_decl_plugin.h"
#include "smt/smt_solver.h"
#include "params/sat_params.hpp"
#include "sat/smt/euf_proof_checker.h"
#include "sat/smt/arith_theory_checker.h"
#include "sat/smt/q_theory_checker.h"
#include "sat/smt/bv_theory_checker.h"
#include "sat/smt/distinct_theory_checker.h"
#include "sat/smt/tseitin_theory_checker.h"
#include "params/solver_params.hpp"

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

    class eq_theory_checker : public theory_checker_plugin {
        ast_manager&     m;
        arith_util       m_arith;
        expr_ref_vector  m_trail;
        basic_union_find m_uf;
        svector<std::pair<unsigned, unsigned>> m_expr2id;
        ptr_vector<expr>                       m_id2expr;
        svector<std::pair<expr*,expr*>>        m_diseqs;
        unsigned         m_ts = 0;
        
        void merge(expr* x, expr* y) {
            m_uf.merge(expr2id(x), expr2id(y));
            IF_VERBOSE(10, verbose_stream() << "merge " << mk_bounded_pp(x, m) << " == " << mk_bounded_pp(y, m) << "\n");
            merge_numeral(x);
            merge_numeral(y);
        }

        void merge_numeral(expr* x) {
            rational n;
            expr* y;
            if (m_arith.is_uminus(x, y) && m_arith.is_numeral(y, n)) {
                y = m_arith.mk_numeral(-n, x->get_sort());
                m_trail.push_back(y);
                m_uf.merge(expr2id(x), expr2id(y));
            }
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
        eq_theory_checker(ast_manager& m): m(m), m_arith(m), m_trail(m) {}

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

        void register_plugins(theory_checker& pc) override {
            pc.register_plugin(symbol("euf"), this);
            pc.register_plugin(symbol("smt"), this);
        }
    };

    /**
       A resolution proof term is of the form
       (res pivot proof1 proof2)
       The pivot occurs with opposite signs in proof1 and proof2
     */

    class res_checker : public theory_checker_plugin {
        ast_manager&   m;
        theory_checker& pc;

    public:
        res_checker(ast_manager& m, theory_checker& pc): m(m), pc(pc) {}

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

        void register_plugins(theory_checker& pc) override {
            pc.register_plugin(symbol("res"), this);
        }
    };

    theory_checker::theory_checker(ast_manager& m):
        m(m) {
        add_plugin(alloc(arith::theory_checker, m));
        add_plugin(alloc(eq_theory_checker, m));
        add_plugin(alloc(res_checker, m, *this));
        add_plugin(alloc(q::theory_checker, m));
        add_plugin(alloc(distinct::theory_checker, m));
        add_plugin(alloc(smt_theory_checker_plugin, m)); 
        add_plugin(alloc(tseitin::theory_checker, m));
        add_plugin(alloc(bv::theory_checker, m));
    }

    void theory_checker::add_plugin(theory_checker_plugin* p) {
        m_plugins.push_back(p);
        p->register_plugins(*this);
    }

    void theory_checker::register_plugin(symbol const& rule, theory_checker_plugin* p) {
        m_map.insert(rule, p);
    }

    bool theory_checker::check(expr* e) {
        if (!e || !is_app(e))
            return false;
        app* a = to_app(e);
        theory_checker_plugin* p = nullptr;
        return m_map.find(a->get_decl()->get_name(), p) && p->check(a);
    }

    expr_ref_vector theory_checker::clause(expr* e) {
        SASSERT(is_app(e) && m_map.contains(to_app(e)->get_name()));
        expr_ref_vector r = m_map[to_app(e)->get_name()]->clause(to_app(e));
        return r;
    }

    bool theory_checker::vc(expr* e, expr_ref_vector const& clause, expr_ref_vector& v) {
        SASSERT(is_app(e));
        app* a = to_app(e);
        theory_checker_plugin* p = nullptr;
        if (m_map.find(a->get_name(), p))
            return p->vc(a, clause, v);
        IF_VERBOSE(10, verbose_stream() << "there is no proof plugin for " << mk_pp(e, m) << "\n");
        return false;
    }
   
    bool theory_checker::check(expr_ref_vector const& clause1, expr* e, expr_ref_vector & units) {
        if (!check(e))
            return false;
        units.reset();
        expr_mark literals;
        auto clause2 = clause(e);

        // check that all literals in clause1 are in clause2
        for (expr* arg : clause2)
            literals.mark(arg, true);
        for (expr* arg : clause1)
            if (!literals.is_marked(arg)) {
                if (m.is_not(arg, arg) && m.is_not(arg, arg) && literals.is_marked(arg)) // kludge
                    continue;
                IF_VERBOSE(0, verbose_stream() << mk_bounded_pp(arg, m) << " not in " << clause2 << "\n");
                return false;
            }

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

    expr_ref_vector smt_theory_checker_plugin::clause(app* jst) {
        expr_ref_vector result(m);
        for (expr* arg : *jst) 
            result.push_back(mk_not(m, arg));
        return result;
    }

    void smt_theory_checker_plugin::register_plugins(theory_checker& pc) {
        pc.register_plugin(symbol("datatype"), this);
        pc.register_plugin(symbol("array"), this);
        pc.register_plugin(symbol("quant"), this);
        pc.register_plugin(symbol("fpa"), this);
    }

    smt_proof_checker::smt_proof_checker(ast_manager& m, params_ref const& p):
        m(m),
        m_params(p),
        m_checker(m),
        m_sat_solver(m_params, m.limit()), 
        m_drat(m_sat_solver) 
    {
        m_params.set_bool("drat.check_unsat", true);
        m_params.set_bool("euf", false);
        m_sat_solver.updt_params(m_params);
        m_drat.updt_config();        
        m_rup = symbol("rup");
        solver_params sp(m_params);
        m_check_rup = sp.proof_check_rup();
    }

    void smt_proof_checker::ensure_solver() {
        if (!m_solver)
            m_solver = mk_smt_solver(m, m_params, symbol());
    }


    void smt_proof_checker::log_verified(app* proof_hint, bool success) {
        if (!proof_hint)
            return;

        symbol n = proof_hint->get_name();
        if (success)
            m_hint2hit.insert_if_not_there(n, 0)++;
        else
            m_hint2miss.insert_if_not_there(n, 0)++;
        ++m_num_logs;

        if (m_num_logs < 100 || (m_num_logs % 1000) == 0) {
            std::cout << "(proofs";
            for (auto const& [k, v] : m_hint2hit)
                std::cout << " +" << k << " " << v;
            for (auto const& [k, v] : m_hint2miss)
                std::cout << " -" << k << " " << v;
            std::cout << ")\n";
        }
    }

    bool smt_proof_checker::check_rup(expr_ref_vector const& clause) {
        if (!m_check_rup)
            return true;
        add_units();                          
        mk_clause(clause);
        return m_drat.is_drup(m_clause.size(), m_clause.data(), m_units);
    }

    bool smt_proof_checker::check_rup(expr* u) {
        if (!m_check_rup)
            return true;
        add_units();
        mk_clause(u);
        return m_drat.is_drup(m_clause.size(), m_clause.data(), m_units);
    }

    void smt_proof_checker::infer(expr_ref_vector& clause, app* proof_hint) {
            
        if (is_rup(proof_hint) && check_rup(clause)) {
            if (m_check_rup) {
                log_verified(proof_hint, true);
                add_clause(clause);
            }
            return;
        }
        
        expr_ref_vector units(m);
        if (m_checker.check(clause, proof_hint, units)) {
            bool units_are_rup = true;
            for (expr* u : units) {
                if (!m.is_true(u) && !check_rup(u)) {
                    std::cout << "unit " << mk_bounded_pp(u, m) << " is not rup\n";
                    units_are_rup = false;
                }
            }
            if (units_are_rup) {
                log_verified(proof_hint, true);
                add_clause(clause);
                return;
            }
        }
        
        // extract a simplified verification condition in case proof validation does not work.
        // quantifier instantiation can be validated as follows:
        // If quantifier instantiation claims that (forall x . phi(x)) => psi using instantiation x -> t
        // then check the simplified VC: phi(t) => psi.
        // in case psi is the literal instantiation, then the clause is a propositional tautology.
        // The VC function is a no-op if the proof hint does not have an associated vc generator.
        expr_ref_vector vc(clause);
        if (m_checker.vc(proof_hint, clause, vc)) {
            log_verified(proof_hint, true);
            add_clause(clause);
            return;
        }
        
        log_verified(proof_hint, false);

        ensure_solver();
        m_solver->push();
        for (expr* lit : vc)
            m_solver->assert_expr(m.mk_not(lit));
        lbool is_sat = m_solver->check_sat();
        if (is_sat != l_false) {
            std::cout << "did not verify: " << is_sat << " " << clause << "\n";
            std::cout << "vc:\n" << vc << "\n";
            if (proof_hint) 
                std::cout << "hint: " << mk_bounded_pp(proof_hint, m, 4) << "\n";
            m_solver->display(std::cout);
            if (is_sat == l_true) {
                model_ref mdl;
                m_solver->get_model(mdl);
                mdl->evaluate_constants();
                std::cout << *mdl << "\n";
            }                
            exit(0);
        }
        m_solver->pop(1);
        std::cout << "(verified-smt"; 
        if (proof_hint) std::cout << "\n" << mk_bounded_pp(proof_hint, m, 4);
        for (expr* arg : clause)
            std::cout << "\n " << mk_bounded_pp(arg, m);
        std::cout << ")\n";
        std::cout.flush();

        if (false && is_rup(proof_hint)) 
            diagnose_rup_failure(clause);
            
        add_clause(clause);
    }

    void smt_proof_checker::diagnose_rup_failure(expr_ref_vector const& clause) {
        expr_ref_vector fmls(m), assumptions(m), core(m);
        m_solver->get_assertions(fmls);
        for (unsigned i = 0; i < fmls.size(); ++i) {
            assumptions.push_back(m.mk_fresh_const("a", m.mk_bool_sort()));
            fmls[i] = m.mk_implies(assumptions.back(), fmls.get(i));
        }
            
        ref<::solver> core_solver = mk_smt_solver(m, m_params, symbol());
        // core_solver->assert_expr(fmls);
        core_solver->assert_expr(m.mk_not(mk_or(clause)));
        lbool ch = core_solver->check_sat(assumptions);
        std::cout << "failed to verify\n" << clause << "\n";
        if (ch == l_false) {
            core_solver->get_unsat_core(core);
            std::cout << "core\n";
            for (expr* f : core)
                std::cout << mk_pp(f, m) << "\n";
        }
    }

    void smt_proof_checker::collect_statistics(statistics& st) const {
        if (m_solver)
            m_solver->collect_statistics(st);

    }
    
}

