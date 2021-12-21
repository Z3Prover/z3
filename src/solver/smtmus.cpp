/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    musrmr.cpp

Abstract:
   
    MUS extraction with model rotation modulo arithmatic.

Author:

    Jaroslav Bendik, Nikolaj Bjorner (nbjorner) 2021-12-20

Notes:

- hard constraints need to be handled.
  - we need an occurs index into hard constraints so that rotations can be checked
    to not violate hard constraints.
- extraction of soft clauses from hard constraints to be revised, made solid.
- soundness of core reduction to be checked.
  - The call to check-sat uses negated soft constraints
  - In other core reduction code I don't minimize cores if there is a dependency on
    negated soft constraints.
- sign of ineq::get_value is probably wrong, 
  - negate it
  - check if it works with strict inequalities.

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

    enum class ineq_kind { EQ, DE, LE, LT };
    enum class bound_type { Lower, Upper, Unknown };
    struct ineq {
        expr_ref m_base;
        obj_map<func_decl, rational> m_coeffs;
        ineq_kind m_kind;
        ineq(ast_manager& m, ineq_kind k) : m_base(m), m_kind(k) {}

        bound_type get_bound_type(func_decl* v) {
            SASSERT(m_coeffs.contains(v));
            auto const& c = m_coeffs[v];
            if (m_kind == ineq_kind::LE || m_kind == ineq_kind::LT) {
                if (c > 0)
                    return bound_type::Lower;
                if (c < 0)
                    return bound_type::Upper;
            }
            return bound_type::Unknown;
        }

        rational get_value(model& mdl, arith_util& a, func_decl* v) {
            rational r;
            VERIFY(a.is_numeral(mdl(m_base), r));
            rational value = r;
            expr_ref val(mdl.get_manager());
            for (auto& [w, coeff] : m_coeffs)
                if (v != w && mdl.eval(w, val) && a.is_numeral(val, r))
                    value += r * coeff;
            adjust_value(a, v, value);
            return value;
        }

        void adjust_value(arith_util& a, func_decl* v, rational& value) {
            bool is_int = a.is_int(v->get_range());
            rational coeff = m_coeffs[v];
            value = value / coeff;
            if (is_int)
                value = floor(value);
            switch (m_kind) {
            case ineq_kind::LE:
                break;
            case ineq_kind::LT:
                if (is_int)
                    value += 1;
                else
                    value += rational(0.00001);
                break;
            default:
                break;
            }
        }
    };

    solver& m_solver;
    solver_ref m_reset_solver;
    solver* m_main_solver;
    ast_manager& m;
    arith_util   a;
    obj_map<expr, unsigned>  m_expr2lit;
    model_ref                m_model;
    expr_ref_vector          m_soft;
    expr_ref_vector          m_hard;
    vector<expr_ref_vector>  m_soft_clauses;
    obj_map<expr, func_decl_ref_vector*> m_lit2vars;
    obj_map<func_decl, unsigned_vector*> m_occurs;
    obj_map<expr, ineq*>                 m_lit2ineq;

    unsigned m_rotated = 0;
    unsigned p_max_cores = 30;
    bool     p_crit_ext = false;
    unsigned p_limit = 1;
    bool     p_model_rotation = true;
    bool     p_use_reset = false;

    imp(solver& s) :
        m_solver(s), m_main_solver(&s), m(s.get_manager()), a(m), m_soft(m), m_hard(m)
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
                bool is_soft = false;
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
                        is_soft = true;
                        break;
                    }
                    ++idx;
                }
                if (!is_soft)
                    m_hard.push_back(f);
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

    void init_lit2ineq() {
        for (auto const& [lit, vars] : m_lit2vars)
            init_lit2ineq(lit);        
    }

    void init_lit2ineq(expr* lit) {
        bool is_not = m.is_not(lit, lit);
        expr* x, * y;
        auto mul = [&](rational const& coeff, expr* t) -> expr* {
            if (coeff == 1)
                return t;
            return a.mk_mul(a.mk_numeral(coeff, a.is_int(t)), t);
        };
        if (a.is_le(lit, x, y) || a.is_lt(lit, x, y) || a.is_ge(lit, y, x) || a.is_gt(lit, y, x)) {
            if (is_not)
                std::swap(x, y);
            bool is_strict = is_not ? (a.is_le(lit) || a.is_ge(lit)) : (a.is_lt(lit) || a.is_gt(lit));
            auto* e = alloc(ineq, m, is_strict ? ineq_kind::LT : ineq_kind::LE);
            expr_ref_vector basis(m);
            rational coeff1;
            vector<std::pair<rational, expr*>> terms;
            terms.push_back(std::make_pair(rational::one(), x));
            terms.push_back(std::make_pair(-rational::one(), y));
            for (unsigned i = 0; i < terms.size(); ++i) {
                auto [coeff, t] = terms[i];
                expr* t1, * t2;
                if (a.is_add(t)) {
                    for (expr* arg : *to_app(t))
                        terms.push_back({ coeff, arg });
                }
                else if (a.is_sub(t, t1, t2)) {
                    terms.push_back({ coeff, t1 });
                    terms.push_back({ -coeff, t2 });
                }
                else if (a.is_mul(t, t1, t2)) {
                    if (a.is_numeral(t1, coeff1))
                        terms.push_back({ coeff * coeff1, t2 });
                    else if (a.is_numeral(t2, coeff1))
                        terms.push_back({ coeff * coeff1, t1 });
                    else
                        basis.push_back(mul(coeff, t));
                }
                else if (is_app(t) && m_occurs.contains(to_app(t)->get_decl())) {
                    func_decl* v = to_app(t)->get_decl();
                    coeff1 = 0;
                    e->m_coeffs.find(v, coeff1);
                    coeff1 += coeff;
                    if (coeff1 == 0)
                        e->m_coeffs.remove(v);
                    else
                        e->m_coeffs.insert(v, coeff1);
                }
                else 
                    basis.push_back(mul(coeff, t));
            }
            if (basis.empty())
                e->m_base = a.mk_numeral(rational::zero(), a.is_int(x));
            else
                e->m_base = a.mk_add(basis);
            m_lit2ineq.insert(lit, e);
        }
        else {
            // literals that don't correspond to inequalities are associated with null.
            m_lit2ineq.insert(lit, nullptr);
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
        for (auto& [k, v] : m_lit2ineq)
            dealloc(v);
        m_lit2ineq.reset();
        m_soft_clauses.reset();     
        m_hard.reset();
    }

    void init() {
        init_soft_clauses();
        init_occurs();
        init_lit2ineq();
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
        unsigned prev_size = count_ones(shrunk);
        for (unsigned i = 0; i < m_soft_clauses.size(); ++i) {
            if (!shrunk[i] || crits[i])
                continue;
            shrunk[i] = false;
            switch (solve(shrunk, max_cores > 0, false)) {
            case l_true:
                shrunk[i] = true;
                crits[i] = true;
                unsigned critical_extension_unused_vars = 1;
                if (p_crit_ext)
                    critical_extension_unused_vars = critical_extension(shrunk, crits, i);
                if (p_model_rotation && critical_extension_unused_vars > 0)
                    rotate(shrunk, crits, i, *m_model, true);                                
                break;
            case l_false:
                --max_cores;
                if (p_use_reset && (count_ones(shrunk) < 0.7 * prev_size)) {
                    reset_solver(shrunk);
                    prev_size = count_ones(shrunk);
                }
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

    void reset_solver(bool_vector const& shrunk) {
        m_reset_solver = mk_smt2_solver(m, m_solver.get_params());
        m_main_solver = m_reset_solver.get();        
        for (unsigned i = 0; i < shrunk.size(); i++)
            if (shrunk[i] && m_soft.get(i) != m_soft_clauses[i].back())
                m_main_solver->assert_expr(m.mk_implies(m_soft.get(i), m.mk_or(m_soft_clauses[i])));
        for (auto* f : m_hard)
            m_main_solver->assert_expr(f);                               
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

        auto r = m_main_solver->check_sat(asms);
        switch (r) {
        case l_false:
            if (!core)
                break;
            m_main_solver->get_unsat_core(cs);
            std::fill(formula.begin(), formula.end(), false);
            for (expr* c : cs) {
                if (soft2idx.find(c, idx))
                    formula[idx] = true;
                break;
            }
            break;
        case l_true:
            m_main_solver->get_model(m_model);
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
        result = rotate_get_ineq_flips(lit, v, mdl, limit);
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

    expr_ref_vector rotate_get_ineq_flips(expr* lit, func_decl* v, model& mdl, unsigned limit) {
        ineq* e = nullptr;
        expr_ref_vector flips(m);
        if (m_lit2ineq.find(lit, e) && e && e->m_coeffs.contains(v)) {
            rational coeff = e->m_coeffs[v];
            rational val = e->get_value(mdl, a, v);
            bool is_int = a.is_int(v->get_range());
            SASSERT(!is_int || val.is_int());
            flips.push_back(a.mk_numeral(val, is_int));
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
        if (!arith_are_conflicting(i, j, v))
            return false;
        return true;
    }

    bool arith_are_conflicting(unsigned i, unsigned j, func_decl* v) {
        auto insert_bounds = [&](vector<bound_type>& bounds, expr_ref_vector const& lits) {
            for (auto* lit : lits) {
                ineq* e = nullptr;
                if (!m_lit2ineq.find(lit, e))
                    return true;
                if (!e)
                    return true;
                if (!a.is_numeral(e->m_base))
                    return true;
                if (!e->m_coeffs.contains(v))
                    continue;
                auto b = e->get_bound_type(v);
                if (b == bound_type::Unknown)
                    return true;
                bounds.insert(b);
            }
            return false;
        };
        auto const& litsI = m_soft_clauses[i];
        auto const& litsJ = m_soft_clauses[j];
        vector<bound_type> iBounds, jBounds;
        if (insert_bounds(iBounds, litsI))
            return true;
        if (insert_bounds(jBounds, litsJ))
            return true;
        for (auto b : iBounds) {
            if (b == bound_type::Lower && jBounds.contains(bound_type::Upper))
                return true;
            if (b == bound_type::Upper && jBounds.contains(bound_type::Lower))
                return true;
        }
        return false;
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

