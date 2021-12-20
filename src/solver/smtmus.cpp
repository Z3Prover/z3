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
#include "model/model_evaluator.h"
#include "model/model.h"
#include "ast/arith_decl_plugin.h"


struct smtmus::imp {

    typedef obj_hashtable<expr> expr_set;

    solver& m_solver;
    ast_manager& m;
    arith_util   a;
    expr_ref_vector          m_lit2expr;
    obj_map<expr, unsigned>  m_expr2lit;
    model_ref                m_model;
    expr_ref_vector          m_soft;
    vector<expr_ref_vector>  m_soft_clauses;
    obj_map<expr, func_decl_ref_vector*> m_lit2vars;

    unsigned m_rotated = 0;
    unsigned p_max_cores = 30;
    bool     p_crit_ext = false;

    imp(solver& s) :
        m_solver(s), m(s.get_manager()), a(m), m_lit2expr(m), m_soft(m)
    {}

    ~imp() {
        for (auto& [k, v] : m_lit2vars)
            dealloc(v);
    }


    unsigned add_soft(expr* lit) {
        unsigned idx = m_lit2expr.size();
        m_expr2lit.insert(lit, idx);
        m_lit2expr.push_back(lit);
        TRACE("mus", tout << idx << ": " << mk_pp(lit, m) << "\n" << m_lit2expr << "\n";);
        return idx;
    }

    void init() {
        // initialize soft_clauses based on control variables in mus, or if mus already is a clause.
    }


    lbool get_mus(expr_ref_vector& mus) {
        m_model.reset();
        mus.reset();
        if (m_lit2expr.size() == 1) {
            mus.push_back(m_lit2expr.back());
            return l_true;
        }
        return l_undef;
    }

    // extract clauses corresponding to added soft constraints.
    // extract integer, real variables from clauses
    //

    bool_vector shrink() {
        bool_vector crits(m_soft_clauses.size(), false);
        bool_vector shrunk(m_soft_clauses.size(), true);
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
                break;
            }
        }
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
                expr_ref_vector flips = rotate_get_flips(lit, v, mdl, 1);
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
        NOT_IMPLEMENTED_YET();
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
        NOT_IMPLEMENTED_YET();
        return false;
    }

    void mark_critical(bool_vector const& formula, bool_vector& crits, unsigned i) {
        if (crits[i])
            return;
        crits[i] = true;
        if (p_crit_ext)
            critical_extension(formula, crits, i);
    }

    void critical_extension(bool_vector const& formula, bool_vector& crits, unsigned i) {
        NOT_IMPLEMENTED_YET();
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

