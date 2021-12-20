/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    musrmr.cpp

Abstract:
   
    MUS extraction with model rotation modulo arithmatic.

Author:

    Jaroslav Bendik, Nikolaj Bjorner (nbjorner) 2021-12-20

--*/

#include "solver/solver.h"
#include "solver/smtmus.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "model/model_evaluator.h"
#include "model/model.h"
#include "ast/arith_decl_plugin.h"


struct smtmus::imp {

    typedef obj_hashtable<expr> expr_set;

    solver& m_solver;
    ast_manager& m;
    arith_util   a;
    obj_map<expr, unsigned>  m_expr2lit;
    model_ref                m_model;
    expr_ref_vector          m_soft;
    vector<expr_ref_vector>  m_soft_clauses;
    obj_map<expr, func_decl_ref_vector*> m_lit2vars;
    obj_map<func_decl, unsigned_vector*> m_occurs;

    unsigned m_rotated = 0;
    unsigned p_max_cores = 30;
    bool     p_crit_ext = false;
    unsigned p_limit = 1;

    imp(solver& s) :
        m_solver(s), m(s.get_manager()), a(m), m_soft(m)
    {}

    ~imp() {
        reset();
    }

    unsigned add_soft(expr* lit) {
        unsigned idx = m_soft.size();
        m_expr2lit.insert(lit, idx);
        m_soft.push_back(lit);
        TRACE("mus", tout << idx << ": " << mk_pp(lit, m) << "\n" << m_soft << "\n";);
        return idx;
    }

    // initialize soft_clauses based on control variables in mus, or if mus already is a clause.
    void init_soft_clauses() {        
        obj_map<expr, unsigned> lit2clause;
        vector<expr_ref_vector> clauses;
        obj_hashtable<expr> softs;
        bool initialized = false;
        auto init_lit2clause = [&]() {
            if (initialized)
                return;
            initialized = true;
            for (expr* s : m_soft)
                softs.insert(s);
            for (auto* f : m_solver.get_assertions()) {
                expr_ref_vector ors(m);
                flatten_or(f, ors);
                unsigned idx = 0;
                for (expr* e : ors) {
                    expr* s = nullptr;
                    if (m.is_not(e, s) && softs.contains(s)) {
                        ors[idx] = ors.back();
                        ors.pop_back();
                        if (lit2clause.find(s, idx)) {
                            expr_ref cl(m.mk_and(mk_or(clauses[idx]), mk_or(ors)), m);
                            ors.reset();
                            ors.push_back(cl);
                            clauses[idx].reset();
                            clauses[idx].append(ors);
                        }
                        else {
                            lit2clause.insert(s, clauses.size());
                            clauses.push_back(ors);
                        }
                        break;
                    }
                    ++idx;
                }
            }
        };
        unsigned cl;
        for (expr* s : m_soft) {
            expr_ref_vector clause(m);
            if (m.is_or(s)) 
                clause.append(to_app(s)->get_num_args(), to_app(s)->get_args());            
            else if (is_uninterp_const(s)) {
                init_lit2clause();
                if (lit2clause.find(s, cl))
                    clause.append(clauses[cl]);
                else
                    clause.push_back(s);
            }
            else 
                clause.push_back(s);
            m_soft_clauses.push_back(clause);
        }

        TRACE("satmus",
            for (expr* s : m_soft)
                tout << "soft " << mk_pp(s, m) << "\n";
            for (auto const& clause : m_soft_clauses)
                tout << "clause " << clause << "\n";);
    }

    void init_occurs() {
        unsigned idx = 0;
        for (auto const& clause : m_soft_clauses) {
            for (auto* lit : clause) {
                auto const& vars = get_vars(lit);
                for (auto* v : vars) {
                    if (!m_occurs.contains(v))
                        m_occurs.insert(v, alloc(unsigned_vector));
                    auto& occ = *m_occurs[v];
                    if (!occ.empty() && occ.back() == idx)
                        continue;
                    occ.push_back(idx);
                }
            }
            ++idx;
        }
    }

    void reset() {
        m_model.reset();
        for (auto& [k, v] : m_lit2vars)
            dealloc(v);
        m_lit2vars.reset();
        for (auto& [k, v] : m_occurs)
            dealloc(v);
        m_occurs.reset();
        m_soft_clauses.reset();        
    }

    void init() {
        init_soft_clauses();
        init_occurs();
    }

    lbool get_mus(expr_ref_vector& mus) {
        mus.reset();
        if (m_soft.size() == 1) {
            mus.push_back(m_soft.back());
            return l_true;
        }
        init();
        
        bool_vector shrunk(m_soft_clauses.size(), true);

        if (!shrink(shrunk))
            return l_undef;

        for (unsigned i = 0; i < shrunk.size(); ++i) 
            if (shrunk[i])
                mus.push_back(m_soft.get(i));
        return l_true;
    }

    bool shrink(bool_vector& shrunk) {
        bool_vector crits(m_soft_clauses.size(), false);

        unsigned max_cores = p_max_cores;
        for (unsigned i = 0; i < m_soft_clauses.size(); ++i) {
            if (!shrunk[i] || crits[i])
                continue;
            unsigned prev_size = count_ones(shrunk);
            shrunk[i] = false;
            switch (solve(shrunk, max_cores > 0, false)) {
            case l_true:
                shrunk[i] = true;
                crits[i] = true;
                rotate(shrunk, crits, i, *m_model, true);
                break;
            case l_false:
                --max_cores;
                break;
            default:
                return false;
            }
        }
        return true;
    }

    unsigned count_ones(bool_vector const& v) {
        unsigned ones = 0;
        for (auto b : v)
            ones += b;
        return ones;
    }

    lbool solve(bool_vector& formula, bool core, bool grow) {
        expr_ref_vector asms(m);
        obj_map<expr, unsigned> soft2idx;
        unsigned idx = 0;
        expr_ref_vector cs(m);
        for (expr* s : m_soft) {
            asms.push_back(formula[idx] ? s : mk_not(m, s));
            soft2idx.insert(s, idx++);
        }

        auto r = m_solver.check_sat(asms);
        switch (r) {
        case l_false:
            if (!core)
                break;
            m_solver.get_unsat_core(cs);
            std::fill(formula.begin(), formula.end(), false);
            for (expr* c : cs) {
                if (soft2idx.find(c, idx))
                    formula[idx] = true;
                break;
            }
            break;
        case l_true:
            m_solver.get_model(m_model);
            if (!grow) // ignored for mus
                break;
            break;
        default:
            break;
        }
        return r;
    }

    void rotate(bool_vector const& formula, bool_vector& crits, unsigned i, model& mdl, bool top_level) {
        expr_ref prev_value(m);
        unsigned falsified;
        for (auto const& lit : m_soft_clauses[i]) {
            auto const& vars = get_vars(lit);
            for (auto v : vars) {
                expr_ref_vector flips = rotate_get_flips(lit, v, mdl, p_limit);
                for (auto& flip : flips) {
                    if (!mdl.eval(v, prev_value))
                        continue;
                    mdl.register_decl(v, flip);
                    if (rotate_get_falsified(formula, mdl, v, falsified) && !crits[falsified]) {
                        mark_critical(formula, crits, falsified);
                        ++m_rotated;
                        rotate(formula, crits, falsified, mdl, false);
                    }
                    mdl.register_decl(v, prev_value);
                }
            }
        }
    }

    // access and update lit2vars on demand.
    func_decl_ref_vector const& get_vars(expr* lit) {
        if (!m_lit2vars.contains(lit)) {
            auto* vars = alloc(func_decl_ref_vector, m);
            extract_vars(lit, *vars);
            m_lit2vars.insert(lit, vars);            
        }
        return *m_lit2vars[lit];
    }

    void extract_vars(expr* e, func_decl_ref_vector& vars) {
        for (expr* t : subterms::ground(expr_ref(e, m))) 
            if (is_uninterp_const(t))
                vars.push_back(to_app(t)->get_decl());              
    }

    expr_ref_vector rotate_get_flips(expr* lit, func_decl* v, model& mdl, unsigned limit) {
        expr_ref_vector result(m);
        if (m.is_bool(v->get_range())) {         
            expr_ref val(m);
            expr* lit2 = lit;
            m.is_not(lit, lit2);

            if (is_app(lit2) && to_app(lit2)->get_decl() == v && mdl.eval(v, val)) {
                result.push_back(m.mk_bool_val(m.is_false(val)));
                return result;
            }
        }

        result = rotate_get_eq_flips(lit, v, mdl, limit);
        if (!result.empty())
            return result;
        result = rotate_get_lia_flips(lit, v, mdl, limit);
        if (!result.empty())
            return result;
        result = rotate_get_lra_flips(lit, v, mdl, limit);
        if (!result.empty())
            return result;
        return rotate_get_flips_agnostic(lit, v, mdl, limit);
    }

    expr_ref_vector rotate_get_eq_flips(expr* lit, func_decl* v, model& mdl, unsigned limit) {
        expr_ref_vector flips(m);
        expr* x, * y;
        expr_ref val(m);
        if (m.is_eq(lit, x, y) || a.is_le(lit, x, y) || a.is_ge(lit, x, y)) {
            if (is_app(x) && to_app(x)->get_decl() == v && mdl.eval_expr(y, val, true))
                flips.push_back(val);
            else if (is_app(y) && to_app(y)->get_decl() == v && mdl.eval_expr(x, val, true))
                flips.push_back(val);
        }
        return flips;
    }

    expr_ref_vector rotate_get_lia_flips(expr* lit, func_decl* v, model& mdl, unsigned limit) {
        expr_ref_vector flips(m);
        return flips;
    }

    expr_ref_vector rotate_get_lra_flips(expr* lit, func_decl* v, model& mdl, unsigned limit) {
        expr_ref_vector flips(m);
        return flips;
    }

    expr_ref_vector rotate_get_flips_agnostic(expr* lit, func_decl* v, model& mdl, unsigned limit) {
        solver_ref s2 = mk_smt2_solver(m, m_solver.get_params());
        s2->assert_expr(lit);
        auto const& vars = get_vars(lit);
        expr_ref val(m);
        expr_ref_vector result(m);
        for (auto& v2 : vars) {
            if (v2 == v)
                continue;
            if (!mdl.eval(v2, val))
                continue;
            s2->assert_expr(m.mk_eq(val, m.mk_const(v2)));
        }
        while (l_true == s2->check_sat() && limit-- > 0) {
            model_ref m2;
            s2->get_model(m2);
            if (!m2->eval(v, val))
                break;
            result.push_back(val);
            s2->assert_expr(m.mk_not(m.mk_eq(val, m.mk_const(v))));
        }
        return result;
    }

    bool rotate_get_falsified(bool_vector const& formula, model& mdl, func_decl* f, unsigned& falsified) {
        falsified = UINT_MAX;
        for (auto i : *m_occurs[f]) {
            if (formula[i] && !is_true(mdl, m_soft_clauses.get(i))) {
                if (falsified != UINT_MAX)
                    return false;
                falsified = i;
            }
        }
        return falsified != UINT_MAX;
    }

    bool is_true(model& mdl, expr_ref_vector const& clause) {        
        for (expr* lit : clause)
            if (m.is_true(lit))
                return true;
        return false;
    }

    void mark_critical(bool_vector const& formula, bool_vector& crits, unsigned i) {
        if (crits[i])
            return;
        crits[i] = true;
        if (p_crit_ext)
            critical_extension(formula, crits, i);
    }

    unsigned critical_extension(bool_vector const& formula, bool_vector& crits, unsigned i) {
        unsigned unused_vars = 0;
        ast_mark checked_vars;
        for (auto* lit : m_soft_clauses[i]) {
            auto const& vars = get_vars(lit);
            for (auto* v : vars) {
                if (checked_vars.is_marked(v))
                    continue;
                checked_vars.mark(v, true);
                unsigned_vector hits;
                for (auto j : *m_occurs[v]) {
                    if (formula[j] && j != i && (are_conflicting(i, j, v) || m.is_bool(v->get_range())))
                        hits.push_back(j);
                }
                if (hits.size() == 1)
                    mark_critical(formula, crits, hits[0]);
                else
                    ++unused_vars;
            }
        }
        return unused_vars;
    }

    bool are_conflicting(unsigned i, unsigned j, func_decl* v) {
        if (!lia_are_conflicting(i, j, v))
            return false;
        if (!lra_are_conflicting(i, j, v))
            return false;
        // TBD: what is the right default value?
        return true;
    }

    bool lia_are_conflicting(unsigned i, unsigned j, func_decl* v) {
        NOT_IMPLEMENTED_YET();
        return true;
    }

    bool lra_are_conflicting(unsigned i, unsigned j, func_decl* v) {
        NOT_IMPLEMENTED_YET();
        return true;
    }
};

smtmus::smtmus(solver& s) {
    m_imp = alloc(imp, s);
}

smtmus::~smtmus() {
    dealloc(m_imp);
}

unsigned smtmus::add_soft(expr* lit) {
    return m_imp->add_soft(lit);
}

 
lbool smtmus::get_mus(expr_ref_vector& mus) {
    return m_imp->get_mus(mus);
}

