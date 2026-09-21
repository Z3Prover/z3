/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    goal2nlsat.cpp

Abstract:

    "Compile" a goal into the nonlinear arithmetic engine.
    Non-arithmetic atoms are "abstracted" into boolean variables.
    Non-supported terms are "abstracted" into variables.

    The mappings can be used to convert back the state of the 
    engine into a goal.

Author:

    Leonardo (leonardo) 2012-01-02

Notes:

--*/
#include "nlsat/tactic/goal2nlsat.h"
#include "tactic/goal.h"
#include "tactic/goal_util.h"
#include "nlsat/nlsat_solver.h"
#include "ast/expr2polynomial.h"
#include "ast/expr2var.h"
#include "ast/arith_decl_plugin.h"
#include "tactic/tactic.h"
#include "ast/ast_pp.h"
#include "math/polynomial/polynomial.h"
#include "math/polynomial/algebraic_numbers.h"

struct goal2nlsat::imp {
    struct nlsat_expr2polynomial : public expr2polynomial {
        nlsat::solver & m_solver;
        nlsat_expr2polynomial(nlsat::solver & s, ast_manager & m, polynomial::manager & pm, expr2var * e2v):
            expr2polynomial(m, pm, e2v),
            m_solver(s) {
        }

        bool is_int(polynomial::var x) const override {
            return m_solver.is_int(x);
        }

        polynomial::var mk_var(bool is_int) override {
            return m_solver.mk_var(is_int);
        }
    };
    
    ast_manager &             m;
    nlsat::solver &           m_solver;
    polynomial::manager &     m_pm;
    unsynch_mpq_manager &     m_qm;
    arith_util                m_util;
    expr2var &                m_a2b;
    expr2var &                m_t2x;
    nlsat_expr2polynomial     m_expr2poly;
    polynomial::factor_params m_fparams;
    nlsat::assumption         m_assumption;

    unsigned long long        m_max_memory;
    bool                      m_factor;
    params_ref                m_params;


    imp(ast_manager & _m, params_ref const & p, nlsat::solver & s, expr2var & a2b, expr2var & t2x, nlsat::assumption a):
        m(_m),
        m_solver(s),
        m_pm(s.pm()),
        m_qm(s.qm()),
        m_util(m),
        m_a2b(a2b),
        m_t2x(t2x),
        m_expr2poly(m_solver, m, m_solver.pm(), &m_t2x),
        m_assumption(a) {
        updt_params(p);
    }

    void updt_params(params_ref const & p) {
        m_params.copy(p);
        m_max_memory   = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
        m_factor       = p.get_bool("factor", true);  
        m_fparams.updt_params(p);
    }

    nlsat::atom::kind flip(nlsat::atom::kind k) {
        switch (k) {
        case nlsat::atom::EQ: return k;
        case nlsat::atom::LT: return nlsat::atom::GT;
        case nlsat::atom::GT: return nlsat::atom::LT;
        default:
            UNREACHABLE();
            return k;
        }
    }

    nlsat::bool_var factor_atom(polynomial::polynomial * p, nlsat::atom::kind k) {
        sbuffer<bool> is_even;
        ptr_buffer<polynomial::polynomial> ps;
        polynomial::factors fs(m_pm);
        m_pm.factor(p, fs, m_fparams);
        TRACE(goal2nlsat_bug, tout << "factors:\n" << fs << "\n";); 
        SASSERT(fs.distinct_factors() > 0);
        for (unsigned i = 0; i < fs.distinct_factors(); ++i) {
            ps.push_back(fs[i]);
            is_even.push_back(fs.get_degree(i) % 2 == 0);
        }
        if (m_qm.is_neg(fs.get_constant()))             
            k = flip(k);            
        return m_solver.mk_ineq_atom(k, ps.size(), ps.data(), is_even.data());
    }

    nlsat::literal process_atom(app * f, nlsat::atom::kind k) {
        SASSERT(f->get_num_args() == 2);
        expr * lhs = f->get_arg(0);
        expr * rhs = f->get_arg(1);
        polynomial_ref p1(m_pm);
        polynomial_ref p2(m_pm);
        scoped_mpz d1(m_qm);
        scoped_mpz d2(m_qm);
        m_expr2poly.to_polynomial(lhs, p1, d1);
        m_expr2poly.to_polynomial(rhs, p2, d2);
        scoped_mpz lcm(m_qm);
        m_qm.lcm(d1, d2, lcm);
        m_qm.div(lcm, d1, d1);
        m_qm.div(lcm, d2, d2);
        m_qm.neg(d2);
        polynomial_ref p(m_pm);
        p = m_pm.addmul(d1, m_pm.mk_unit(), p1, d2, m_pm.mk_unit(), p2);
        TRACE(goal2nlsat_bug, tout << mk_pp(f, m) << " p: " << p << "\nk: " << k << "\n";);
        if (is_const(p)) {
            int sign;
            if (is_zero(p))
                sign = 0;
            else
                sign = m_qm.is_pos(m_pm.coeff(p, 0)) ? 1 : -1;
            switch (k) {
            case nlsat::atom::EQ: return sign == 0 ? nlsat::true_literal : nlsat::false_literal;
            case nlsat::atom::LT: return sign <  0 ? nlsat::true_literal : nlsat::false_literal;
            case nlsat::atom::GT: return sign >  0 ? nlsat::true_literal : nlsat::false_literal;
            default:
                UNREACHABLE();
                return nlsat::true_literal;
            }
        }
        if (m_factor) {
            return nlsat::literal(factor_atom(p, k), false);
        }
        else {
            bool is_even = false;
            polynomial::polynomial * _p = p.get();
            return nlsat::literal(m_solver.mk_ineq_atom(k, 1, &_p, &is_even), false);
        }
    }

    nlsat::literal process_eq(app * f) {
        return process_atom(f, nlsat::atom::EQ);
    }

    nlsat::literal process_le(app * f) {
        return ~process_atom(f, nlsat::atom::GT);
    }

    nlsat::literal process_ge(app * f) {
        return ~process_atom(f, nlsat::atom::LT);
    }

    // everything else is compiled as a boolean variable
    nlsat::bool_var process_bvar(expr * f) {
        if (m_a2b.is_var(f)) {
            return static_cast<nlsat::bool_var>(m_a2b.to_var(f));
        }
        else {
            nlsat::bool_var b = m_solver.mk_bool_var();
            m_a2b.insert(f, b);
            return b;
        }
    }

    nlsat::literal process_atom(expr * f) {
        if (m.is_eq(f)) {
            if (m_util.is_int_real(to_app(f)->get_arg(0)))
                return process_eq(to_app(f));
            else
                return nlsat::literal(process_bvar(f), false);                
        }
        else if (m_util.is_le(f)) {
            return process_le(to_app(f));
        }
        else if (m_util.is_ge(f)) {
            return process_ge(to_app(f));
        }
        else if (is_app(f)) {
            if (to_app(f)->get_family_id() == m.get_basic_family_id()) {
                switch (to_app(f)->get_decl_kind()) {
                case OP_TRUE:
                case OP_FALSE:
                    TRACE(goal2nlsat, tout << "f: " << mk_pp(f, m) << "\n";);
                    throw tactic_exception("apply simplify before applying nlsat");
                case OP_AND:
                case OP_OR:
                case OP_XOR:
                case OP_NOT:
                case OP_IMPLIES:
                case OP_ITE:
                    throw tactic_exception("convert goal into cnf before applying nlsat");
                case OP_DISTINCT:
                    throw tactic_exception("eliminate distinct operator (use tactic '(using-params simplify :blast-distinct true)') before applying nlsat");
                default:
                    UNREACHABLE();
                    return nlsat::literal(nlsat::null_bool_var, false);
                }
            }
            else if (to_app(f)->get_family_id() == m_util.get_family_id()) {
                throw tactic_exception("apply purify-arith before applying nlsat");
            }
            else {
                return nlsat::literal(process_bvar(f), false);
            }
        }
        else {
            SASSERT(is_quantifier(f));
            return nlsat::literal(process_bvar(f), false);
        }
    }
    
    nlsat::literal process_literal(expr * f) {
        bool neg = false;
        while (m.is_not(f, f))
            neg = !neg;
        nlsat::literal l = process_atom(f);
        if (neg)
            l.neg();
        return l;
    }

    void process(expr * f, expr_dependency * dep) {
        unsigned num_lits;
        expr * const * lits;
        if (m.is_or(f)) {
            num_lits = to_app(f)->get_num_args();
            lits = to_app(f)->get_args();
        }
        else {
            num_lits = 1;
            lits = &f;
        }
        sbuffer<nlsat::literal> ls;
        for (unsigned i = 0; i < num_lits; ++i) {
            ls.push_back(process_literal(lits[i]));
        }
        m_solver.mk_clause(ls.size(), ls.data(), m_assumption ? m_assumption : dep);
    }

    // Maps a unary arith-family transcendental application's decl_kind to
    // nlsat's own transcendental_op_kind, when supported by nlsat's engine
    // (nlsat_transcendentals.*); atan2/pi have a different arity/arg-shape
    // and are detected and registered separately in register_transcendentals.
    static bool get_transcendental_op(app * t, nlsat::transcendental_op_kind & op) {
        if (t->get_num_args() != 1)
            return false;
        switch (t->get_decl_kind()) {
        case OP_SIN:   op = nlsat::transcendental_op_kind::SIN;   return true;
        case OP_COS:   op = nlsat::transcendental_op_kind::COS;   return true;
        case OP_TAN:   op = nlsat::transcendental_op_kind::TAN;   return true;
        case OP_ASIN:  op = nlsat::transcendental_op_kind::ASIN;  return true;
        case OP_ACOS:  op = nlsat::transcendental_op_kind::ACOS;  return true;
        case OP_ATAN:  op = nlsat::transcendental_op_kind::ATAN;  return true;
        case OP_SINH:  op = nlsat::transcendental_op_kind::SINH;  return true;
        case OP_COSH:  op = nlsat::transcendental_op_kind::COSH;  return true;
        case OP_TANH:  op = nlsat::transcendental_op_kind::TANH;  return true;
        case OP_ASINH: op = nlsat::transcendental_op_kind::ASINH; return true;
        case OP_ACOSH: op = nlsat::transcendental_op_kind::ACOSH; return true;
        case OP_ATANH: op = nlsat::transcendental_op_kind::ATANH; return true;
        case OP_EXP:   op = nlsat::transcendental_op_kind::EXP;   return true;
        case OP_LOG:   op = nlsat::transcendental_op_kind::LOG;   return true;
        default: return false;
        }
    }

    // Returns the polynomial variable denoting t (a real-valued expr):
    // reuses the existing var directly when to_polynomial(t) reduces to a
    // bare "1*x" (the common case: t is itself an uninterpreted constant or
    // an already-registered term), otherwise allocates a fresh auxiliary
    // variable v and asserts the permanent equality axiom d*v - p = 0,
    // where p/d is t's polynomial/denominator - this is exactly what
    // to_polynomial does at every equality atom already, just performed
    // once more explicitly here for a transcendental application's
    // argument, which visit_arith_app otherwise never recurses into (see
    // expr2polynomial::visit_arith_app's default case: it treats the whole
    // application, argument included, as a single opaque variable).
    polynomial::var expr2var_axiom(expr * t) {
        polynomial_ref p(m_pm);
        scoped_mpz d(m_qm);
        m_expr2poly.to_polynomial(t, p, d);
        if (m_qm.is_one(d) && polynomial::manager::size(p.get()) == 1 &&
            m_pm.m().is_one(polynomial::manager::coeff(p.get(), 0))) {
            polynomial::var v;
            if (polynomial::manager::is_var(polynomial::manager::get_monomial(p.get(), 0), v))
                return v;
        }
        polynomial::var v = m_solver.mk_var(false);
        polynomial_ref vp(m_pm);
        vp = m_pm.mk_polynomial(v);
        scoped_mpz none(m_qm);
        m_qm.set(none, -1);
        polynomial_ref eq(m_pm);
        eq = m_pm.addmul(d, m_pm.mk_unit(), vp, none, m_pm.mk_unit(), p);
        bool is_even = false;
        polynomial::polynomial * peq = eq.get();
        nlsat::literal lit(m_solver.mk_ineq_atom(nlsat::atom::EQ, 1, &peq, &is_even), false);
        m_solver.mk_clause(1, &lit, nullptr);
        return v;
    }

    // Scans m_t2x (built up while processing the goal's atoms) for
    // transcendental applications abstracted into an opaque variable by
    // expr2polynomial's generic visit_arith_app, and registers each one
    // with nlsat's own transcendental engine (nlsat_transcendentals.*),
    // creating argument variables (with a linking equality axiom, if
    // needed) along the way. Handles the unary ops (get_transcendental_op),
    // the binary atan2(y, x), and the nullary constant pi. Enables the
    // "transcendentals" solver param the moment at least one such
    // application is found, so solver::imp::search_check actually invokes
    // the refinement loop.
    void register_transcendentals() {
        vector<std::pair<expr*, polynomial::var>> found;
        vector<std::pair<app*, polynomial::var>> atan2_found;
        std::pair<expr*, polynomial::var> pi_found{ nullptr, polynomial::null_var };
        for (auto const & kv : m_t2x) {
            expr * e = &kv.get_key();
            if (!is_app(e) || to_app(e)->get_family_id() != m_util.get_family_id())
                continue;
            app * t = to_app(e);
            nlsat::transcendental_op_kind op;
            if (get_transcendental_op(t, op))
                found.push_back({ e, kv.get_value() });
            else if (m_util.is_atan2(e))
                atan2_found.push_back({ t, kv.get_value() });
            else if (m_util.is_pi(e))
                pi_found = { e, kv.get_value() };
        }
        if (found.empty() && atan2_found.empty() && pi_found.first == nullptr)
            return;
        for (auto const & pr : found) {
            app * t = to_app(pr.first);
            nlsat::transcendental_op_kind op;
            get_transcendental_op(t, op);
            polynomial::var arg = expr2var_axiom(t->get_arg(0));
            m_solver.add_transcendental(op, arg, pr.second);
        }
        for (auto const & pr : atan2_found) {
            app * t = pr.first;
            polynomial::var y = expr2var_axiom(t->get_arg(0));
            polynomial::var x = expr2var_axiom(t->get_arg(1));
            m_solver.add_atan2(y, x, pr.second);
        }
        if (pi_found.first != nullptr)
            m_solver.add_pi(pi_found.second);
        params_ref p2;
        p2.copy(m_params);
        p2.set_bool("transcendentals", true);
        m_solver.updt_params(p2);
    }

    void operator()(goal const & g) {
        TRACE(goal2nlsat, g.display(tout););
        if (has_term_ite(g))
            throw tactic_exception("eliminate term-ite before applying nlsat");
        unsigned sz = g.size();
        for (unsigned i = 0; i < sz; ++i) {
            process(g.form(i), g.dep(i));
        }
        register_transcendentals();
    }

};

struct goal2nlsat::scoped_set_imp {
    goal2nlsat & m_owner; 
    scoped_set_imp(goal2nlsat & o, imp & i):m_owner(o) {
        m_owner.m_imp = &i;        
    }
    
    ~scoped_set_imp() {
        m_owner.m_imp = nullptr;
    }
};

goal2nlsat::goal2nlsat() {
    m_imp = nullptr;
}

goal2nlsat::~goal2nlsat() {
    SASSERT(m_imp == 0);
}
    
void goal2nlsat::collect_param_descrs(param_descrs & r) {
    insert_max_memory(r);
    r.insert("factor", CPK_BOOL, "(default: true) factor polynomials.");
    polynomial::factor_params::get_param_descrs(r);
}
    
void goal2nlsat::operator()(goal const & g, params_ref const & p, nlsat::solver & s, expr2var & a2b, expr2var & t2x,
                          nlsat::assumption a) {
    if (a && g.unsat_core_enabled())
        throw tactic_exception("external nlsat assumptions cannot replace goal unsat-core dependencies");
    imp local_imp(g.m(), p, s, a2b, t2x, a);
    scoped_set_imp setter(*this, local_imp);
    local_imp(g);
}

    

struct nlsat2goal::imp {
    ast_manager& m;
    arith_util   a;
    u_map<expr*> const* m_x2t;
public:
    imp(ast_manager& m):m(m),a(m) {}

    expr_ref operator()(nlsat::solver& s, u_map<expr*> const& b2a, u_map<expr*> const& x2t, nlsat::literal l) {
        m_x2t = &x2t;
        expr_ref result(m);
        expr* t;
        if (b2a.find(l.var(), t)) {
            result = t;
        }
        else {
            nlsat::atom const* at = s.bool_var2atom(l.var());
            SASSERT(at != 0);
            if (at->is_ineq_atom()) {
                nlsat::ineq_atom const* ia = to_ineq_atom(at);
                unsigned sz = ia->size();
                expr_ref_vector ps(m);
                bool is_int = true;
                for (unsigned i = 0; is_int && i < sz; ++i) {
                    is_int = poly_is_int(ia->p(i));
                }
                for (unsigned i = 0; i < sz; ++i) {
                    polynomial::polynomial* p = ia->p(i);
                    expr_ref t = poly2expr(s, p, is_int);
                    if (ia->is_even(i)) {
                        t = a.mk_power(t, a.mk_numeral(rational(2), a.is_int(t)));
                    }
                    ps.push_back(t);
                }
                result = a.mk_mul_simplify(ps);
                expr_ref zero(m);
                zero = a.mk_numeral(rational(0), a.is_int(result));
                switch (ia->get_kind()) {
                case nlsat::atom::EQ:
                    result = m.mk_eq(result, zero);
                    break;
                case nlsat::atom::LT:
                    if (l.sign()) {
                        l.neg();
                        result = a.mk_ge(result, zero);
                    }
                    else {
                        result = a.mk_lt(result, zero);
                    }
                    break;
                case nlsat::atom::GT:
                    if (l.sign()) {
                        l.neg();
                        result = a.mk_le(result, zero);
                    }
                    else {
                        result = a.mk_gt(result, zero);
                    }
                    break;
                default:
                    UNREACHABLE();
                }
            }
            else {
                //nlsat::root_atom const* ra = nlsat::to_root_atom(at);
                //ra->i();
                //expr_ref p = poly2expr(s, ra->p());
                //expr*    x = m_x2t->find(ra->x());
                std::ostringstream strm;
                s.display(strm, l.sign()?~l:l);
                result = m.mk_const(symbol(strm.str()), m.mk_bool_sort());
            }
        }

        if (l.sign()) {
            result = m.mk_not(result);
        }
        return result;
    }

    expr_ref poly2expr(nlsat::solver& s, polynomial::polynomial* p, bool is_int) {
        expr_ref result(m);
        unsigned sz = polynomial::manager::size(p);
        expr_ref_vector args(m);
        for (unsigned i = 0; i < sz; ++i) {
            args.push_back(mono2expr(s, 
                                     polynomial::manager::coeff(p, i), 
                                     polynomial::manager::get_monomial(p, i), is_int));
        }
        result = a.mk_add_simplify(args);
        return result;
    }

    expr_ref mono2expr(nlsat::solver& s, polynomial::numeral const& c, polynomial::monomial* mon, bool is_int) {
        expr_ref result(m);
        expr_ref_vector args(m);
        unsigned sz = polynomial::manager::size(mon);
        for (unsigned i = 0; i < sz; ++i) {
            unsigned d = polynomial::manager::degree(mon, i);
            expr* t = m_x2t->find(polynomial::manager::get_var(mon, i));
            SASSERT(d >= 1);
            if (d == 1) {
                args.push_back(t);
            }
            else {
                args.push_back(a.mk_power(t, a.mk_numeral(rational(d), a.is_int(t))));
            }
        }
        if (!s.pm().m().is_one(c)) {
            args.push_back(a.mk_numeral(c, is_int));
        }
        result = a.mk_mul_simplify(args);
        return result;
    }

    bool poly_is_int(polynomial::polynomial* p) {
        bool is_int = true;
        unsigned sz = polynomial::manager::size(p);
        for (unsigned i = 0; is_int && i < sz; ++i) {
            is_int = mono_is_int(polynomial::manager::get_monomial(p, i));
        }
        return is_int;
    }

    bool mono_is_int(polynomial::monomial* mon) {
        bool is_int = true;
        unsigned sz = polynomial::manager::size(mon);
        for (unsigned i = 0; is_int && i < sz; ++i) {
            is_int = a.is_int(m_x2t->find(polynomial::manager::get_var(mon, i)));
        }
        return is_int;
    }
};


nlsat2goal::nlsat2goal(ast_manager& m) {
    m_imp = alloc(imp, m);
}


nlsat2goal::~nlsat2goal() {
    dealloc(m_imp);
}

expr_ref nlsat2goal::operator()(nlsat::solver& s, u_map<expr*> const& b2a, u_map<expr*> const& x2t, nlsat::literal l) {
    return (*m_imp)(s, b2a, x2t, l);
}
