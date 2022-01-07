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
  - JB: I do not think it is sound to use the core reduction without the dependency check.
    Note that based on my experience, it might be better not to use the negated soft constraints; 
    the solver calls might be a little bit more expensive, however, at least we can always use the unsat cores
- sign of ineq::get_value is probably wrong, 
  - negate it
  - check if it works with strict inequalities.

- m_hard contains clauses that are already excluded from the "original unsat core" when calling get_mus
  - namely, supposing we call ./z3 on 5 clauses, it first checks it for satisfiability, reduces it to 3 clauses, 
  and then calls get_mus. At this point, the two clauses that were alreadu excluded are still in m_hard, and even though 
  they are relaxed by the relaxation variables (assertions' names) and hence does not affect the satisfiability, they might cause troubles
  when checking m_hard during model rotation and critical extension
  -- possible solution: remove the "excluded" clauses from m_hard (replace them by True)
  -- the problematic question: how do we distinguish the hard clauses that come from named assertions and "other" hard clauses, e.g., those defined
  in the Group MUS sense (clauses that should be indeed presented in every MUS)

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
            value.neg();

            adjust_value(a, v, value);
            return value;
        }

        void adjust_value(arith_util& a, func_decl* v, rational& value) {
            bool is_int = a.is_int(v->get_range());
            rational coeff = m_coeffs[v];
            // coeff * v <= value or coeff * v < value
            value = value / coeff;
            // v <= value / v < value or when coeff < 0: v >= value/ v > value
            bool is_rounded = !value.is_int();
            if (is_int && is_rounded)
                value = coeff.is_pos() ? floor(value) : ceil(value);
            switch (m_kind) {
            case ineq_kind::LE:
                break;
            case ineq_kind::LT:
                if (!is_int)
                    value += rational(coeff.is_pos() ? 0.001 : -0.001);
                else if (!is_rounded)
                    value += coeff.is_pos() ? -1 : 1;
                break;
            default:
                break;
            }
        }
    };

    solver&      m_solver;
    solver_ref   m_reset_solver;
    solver*      m_main_solver;
    ast_manager& m;
    arith_util   a;
    model_ref                m_model;                   // latest model, if any.
    expr_ref_vector          m_soft;                    // original soft clauses or indicators
    expr_ref_vector          m_hard;                    // hard clauses, soft clauses removed
    vector<expr_ref_vector>  m_soft_clauses;            // set of soft clauses extracted from indicators
    obj_hashtable<func_decl> m_soft_vars;               // variables used in soft clauses
    obj_map<expr, func_decl_ref_vector*> m_lit2vars;    // map from literals in soft clauses to variables
    obj_map<func_decl, unsigned_vector>  m_soft_occurs; // map from variables to soft clause occurrences
    obj_map<func_decl, unsigned_vector>  m_hard_occurs; // map from variables to hard clause occurrences
    obj_map<expr, ineq*>                 m_lit2ineq;    // map from literals to inequality abstraction
    expr_ref_vector          m_assumptions;             // set of assumptions used.

    unsigned m_rotated = 0;
    unsigned p_max_cores = 30;
    bool     p_crit_ext = true;
    unsigned p_limit = 1;
    bool     p_model_rotation = true;
    bool     p_use_reset = false;

    imp(solver& s) :
        m_solver(s), m_main_solver(&s), m(s.get_manager()), a(m), m_soft(m), m_hard(m), m_assumptions(m)
    {}

    ~imp() {
        reset();
    }

    void add_soft(expr* lit) {
        m_soft.push_back(lit);
    }

    void set_assumptions(expr_ref_vector const& assumptions) {
        m_assumptions.reset();
        m_assumptions.append(assumptions);
    }

    void init_softs(expr_ref_vector const& soft, obj_map<expr, unsigned>& softs) {
        obj_hashtable<expr> dups;
        // collect indicator variable candidates
        unsigned idx = 0;
        for (expr* s : soft) {
            if (is_uninterp_const(s)) {
                if (softs.contains(s))
                    dups.insert(s);
                else
                    softs.insert(s, idx);
            }
            ++idx;
        }
        for (auto* s : dups)
            softs.remove(s);
    }

    void init_soft2hard(obj_map<expr, unsigned>& soft2hard, u_map<expr*>& hard2soft, obj_map<expr, unsigned>const & softs) {
        // find all clauses where soft indicators are used.
        hard2soft.reset();
        soft2hard.reset();
        unsigned idx = 0;
        for (expr* f : m_hard) {
            expr_ref_vector ors(m);
            flatten_or(f, ors);
            for (expr* e : ors) {
                expr* s = nullptr;
                if (m.is_not(e, s) && softs.contains(s)) {
                    soft2hard.insert(s, idx);
                    hard2soft.insert(idx, s);
                    break;
                }
            }
            ++idx;
        }
        // remove hard2soft associations if soft clauses don't occur uniquely.
        idx = 0;
        unsigned_vector to_remove;
        for (expr* f : m_hard) {
            for (expr* v : subterms::all(expr_ref(f, m))) {
                unsigned idx2;
                if (is_uninterp_const(v) && soft2hard.find(v, idx2) && idx != idx2) {
                    to_remove.push_back(idx2);
                    to_remove.push_back(idx);
                }
            }            
            ++idx;
        }
        for (auto i : to_remove)
            hard2soft.remove(i);    
    }

    void simplify_hard(u_map<expr*> const& hard2soft) {
        for (auto const& [i, s] : hard2soft) 
            m_hard[i] = m.mk_true();
    }

    void init_soft_clauses() {
        obj_map<expr, unsigned> soft2hard;
        obj_map<expr, unsigned> softs;
        u_map<expr*> hard2soft;

        // initialize hard clauses
        m_hard.reset();
        m_hard.append(m_solver.get_assertions());
        // initialize soft clauses.
        m_soft_clauses.reset();
        for (expr* s : m_soft) {
            expr_ref_vector ors(m);
            flatten_or(s, ors);
            m_soft_clauses.push_back(ors);
        }

        expr_mark mark;
        expr_ref_vector asms(m);
        for (expr* f : m_soft)
            mark.mark(f);
        for (auto * a : m_assumptions)
            if (!mark.is_marked(a))
                asms.push_back(a);
        init_softs(asms, softs);
        if (!softs.empty()) {
            init_soft2hard(soft2hard, hard2soft, softs);
            simplify_hard(hard2soft);            
        }

        softs.reset();

        init_softs(m_soft, softs);
        if (softs.empty())
            return;

        init_soft2hard(soft2hard, hard2soft, softs);

        //
        // update soft clauses using hard clauses.
        // for soft clause s0 and hard clause ~s0 or lit1 or lit2,
        // replace s0 by (lit1 or lit2), and replace hard clause by true.
        //
        unsigned idx = 0;
        for (auto const& [i, s] : hard2soft) {
            expr* f = m_hard.get(i);
            expr_ref_vector ors(m);
            flatten_or(f, ors);
            idx = 0;
            for (expr* e : ors) {
                unsigned j;
                expr* s2 = nullptr;
                if (m.is_not(e, s2) && softs.find(s2, j)) {
                    ors[idx] = ors.back();
                    ors.pop_back();
                    m_soft_clauses[j].reset();
                    m_soft_clauses[j].append(ors);
                    break;
                }
                ++idx;
            }
            SASSERT(idx <= ors.size());
        }
        simplify_hard(hard2soft);
    
        TRACE("satmus",
              for (expr* s : m_soft)
                  tout << "soft " << mk_pp(s, m) << "\n";
              for (auto const& clause : m_soft_clauses)
                  tout << "clause " << clause << "\n";
              for (expr* h : m_hard)
                  tout << "hard " << mk_pp(h, m) << "\n";
              for (expr* a : m_assumptions)
                  tout << "assumption " << mk_pp(a, m) << "\n";
              );
    }

    void init_occurs(unsigned idx, func_decl* v, obj_map<func_decl, unsigned_vector>& occurs) {
        if (!occurs.contains(v))
            occurs.insert(v, unsigned_vector());
        auto& occ = occurs[v];
        if (!occ.empty() && occ.back() == idx)
            return;
        occ.push_back(idx);
    }

    void init_occurs() {
        m_soft_occurs.reset();
        m_hard_occurs.reset();
        m_soft_vars.reset();
        unsigned idx = 0;
        for (auto const& clause : m_soft_clauses) {
            for (auto* lit : clause) {
                for (auto* v : get_vars(lit)) {
                    init_occurs(idx, v, m_soft_occurs);
                    m_soft_vars.insert(v);
                }
            }
            ++idx;
        }
        idx = 0;
        func_decl_ref_vector vars(m);
        for (auto const& [v, w] : m_soft_occurs)
            m_hard_occurs.insert(v, unsigned_vector());
        for (auto* fml : m_hard) {
            vars.reset();
            extract_vars(fml, vars);
            for (auto* v : vars)
                if (m_soft_vars.contains(v))
                    m_hard_occurs[v].push_back(idx);
            ++idx;
        }
    }

    ineq* lit2ineq(expr* lit) {
        ineq* e = nullptr;
        if (m_lit2ineq.find(lit, e))
            return e;
        return init_lit2ineq(lit);
    }

    ineq* init_lit2ineq(expr* _lit) {
        expr* lit = _lit;
        bool is_not = m.is_not(lit, lit);
        expr* x, * y;
        auto mul = [&](rational const& coeff, expr* t) -> expr* {
            rational coeff2;
            if (coeff == 1)
                return t;
            else if (a.is_numeral(t, coeff2)) 
                return a.mk_numeral(coeff*coeff2, t->get_sort());
            return a.mk_mul(a.mk_numeral(coeff, a.is_int(t)), t);
        };
        if (a.is_le(lit, x, y) || a.is_lt(lit, x, y) || a.is_ge(lit, y, x) || a.is_gt(lit, y, x)) {
            if (is_not)
                std::swap(x, y);
            bool is_strict = is_not ? (a.is_le(lit) || a.is_ge(lit)) : (a.is_lt(lit) || a.is_gt(lit));
            auto* e = alloc(ineq, m, is_strict ? ineq_kind::LT : ineq_kind::LE);
            expr_ref_vector basis(m);
            rational coeff1;
            // encode x - y <= 0 or x - y < 0
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
                else if (is_app(t) && m_soft_occurs.contains(to_app(t)->get_decl())) {
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
            m_lit2ineq.insert(_lit, e);
            return e;
        }
        else {
            // literals that don't correspond to inequalities are associated with null.
            m_lit2ineq.insert(_lit, nullptr);
            return nullptr;
        }
    }

    void reset() {
        m_model.reset();
        for (auto& [k, v] : m_lit2vars)
            dealloc(v);
        m_lit2vars.reset();
        m_soft_vars.reset();
        m_soft_occurs.reset();
        m_hard_occurs.reset();
        for (auto& [k, v] : m_lit2ineq)
            dealloc(v);
        m_lit2ineq.reset();
        m_soft_clauses.reset();     
        m_hard.reset();
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
        unsigned prev_size = count_ones(shrunk);
        for (unsigned i = 0; i < m_soft_clauses.size(); ++i) {
            if (!shrunk[i] || crits[i])
                continue;
            if (is_critical_extension(shrunk, crits, i)){
                mark_critical(shrunk, crits, i);
                continue;
            }
            shrunk[i] = false;
            unsigned critical_extension_unused_vars = 1;
            switch (solve(shrunk, max_cores > 0, false)) {
            case l_true:
                shrunk[i] = true;
                crits[i] = true;
                
                if (p_crit_ext)
                    critical_extension_unused_vars = critical_extension(shrunk, crits, i);
                if (p_model_rotation && critical_extension_unused_vars > 0){
                    m_main_solver->get_model(m_model); //getting the model can be expensive, hence we get it only if we use model rotation
                    rotate(shrunk, crits, i, *m_model, true);               
                }                 
                break;
            case l_false:
                if (max_cores > 0)
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

    lbool solve(bool_vector& formula, bool core, bool grow = false, bool get_model = false) {
        expr_ref_vector asms(m);
        obj_map<expr, unsigned> soft2idx;
        unsigned idx = 0;
        expr_ref_vector cs(m);
        for (expr* s : m_soft) {
            if(formula[idx]) //JB: based on my experience, it is more efficient to set only assumptions for the presented clauses
                asms.push_back(s);
            //asms.push_back(formula[idx] ? s : mk_not(m, s));
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
            //right now, we need the model only if we apply model rotation
            if(get_model)
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
        expr_ref_vector flips(m);
        if (m.is_bool(v->get_range())) {         
            expr_ref val(m);
            expr* lit2 = lit;
            m.is_not(lit, lit2);
            if (is_app(lit2) && to_app(lit2)->get_decl() == v && mdl.eval(v, val)) {
                flips.push_back(m.mk_bool_val(m.is_false(val)));
                return flips;
            }
        }

        flips = rotate_get_eq_flips(lit, v, mdl, limit);
        if (!flips.empty())
            return flips;
        flips = rotate_get_ineq_flips(lit, v, mdl, limit);
        if (!flips.empty())
            return flips;

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
        if ((e = lit2ineq(lit)) && e && e->m_coeffs.contains(v)) {
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
        expr_ref_vector flips(m);
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
            flips.push_back(val);
            s2->assert_expr(m.mk_not(m.mk_eq(val, m.mk_const(v))));
        }
        return flips;
    }

    bool rotate_get_falsified(bool_vector const& formula, model& mdl, func_decl* f, unsigned& falsified) {
        falsified = UINT_MAX;
        for (auto i : m_soft_occurs[f]) {
            if (formula[i] && !is_true(mdl, m_soft_clauses.get(i))) {
                if (falsified != UINT_MAX)
                    return false;
                falsified = i;
            }
        }
        if (falsified == UINT_MAX)
            return false;
        for (auto i : m_hard_occurs[f])
            if (!mdl.is_true(m_hard.get(i)))
                return false;

        return true;
    }

    bool is_true(model& mdl, expr_ref_vector const& clause) {        
        for (expr* lit : clause)
            if (mdl.is_true(lit))
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

    // Note that this function differs from critical_extension. In particular, 
    // critical_extension is used whenever we identify a critical clause and it can possibly identify
    // additional critical clauses. On the other hand, is_critical_extension checks whether a given clause
    // (i-th clause) is critical based on the already identified critical clauses. 
    // Especially, note that is_critical_extension can "reveal" some critical clauses that were not revealed before
    // by calls of critical_extension. Namely, assume that in critical_extension, we get "hits" with two clauses, say p-th and q-th.
    // Therefore, neither of them is marked as critical. However, it could be the case that (W.L.O.G.) q-th clause is critical and p-th clause is not. 
    // If we subsequently remove p-th clause from formula, then the p-th clause can be shown to be critical via is_critical_extension 
    bool is_critical_extension(bool_vector const& formula, bool_vector const& crits, unsigned i) {
        for (auto* lit : m_soft_clauses[i]) {
            auto const& vars = get_vars(lit);
            for (auto* v : vars) {
                unsigned_vector hits;
                //TODO: we have to also assume the hard clauses
                for (auto j : m_soft_occurs[v]) {
                    if (formula[j] && j != i && (are_conflicting(i, j, v) || m.is_bool(v->get_range())))
                        hits.push_back(j);
                }
                if (hits.size() == 1 && crits[hits[0]])
                    return true;
            }
        }
       return false; 
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
                //TODO: we have to also assume the hard clauses
                for (auto j : m_soft_occurs[v]) {
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
                ineq* e = lit2ineq(lit);
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
    return m_imp->add_soft(lit), 0;
}
 
lbool smtmus::get_mus(expr_ref_vector& mus) {
    return m_imp->get_mus(mus);
}

void smtmus::set_assumptions(expr_ref_vector const& assumptions) {
    m_imp->set_assumptions(assumptions);
}
