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
#include"goal2nlsat.h"
#include"goal.h"
#include"goal_util.h"
#include"nlsat_solver.h"
#include"expr2polynomial.h"
#include"expr2var.h"
#include"arith_decl_plugin.h"
#include"tactic.h"
#include"ast_smt2_pp.h"

struct goal2nlsat::imp {
    struct nlsat_expr2polynomial : public expr2polynomial {
        nlsat::solver & m_solver;
        nlsat_expr2polynomial(nlsat::solver & s, ast_manager & m, polynomial::manager & pm, expr2var * e2v):
            expr2polynomial(m, pm, e2v),
            m_solver(s) {
        }

        virtual bool is_int(polynomial::var x) const {
            return m_solver.is_int(x);
        }

        virtual polynomial::var mk_var(bool is_int) {
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

    unsigned long long        m_max_memory;
    bool                      m_factor;

    volatile bool             m_cancel;

    imp(ast_manager & _m, params_ref const & p, nlsat::solver & s, expr2var & a2b, expr2var & t2x):
        m(_m),
        m_solver(s),
        m_pm(s.pm()),
        m_qm(s.qm()),
        m_util(m),
        m_a2b(a2b),
        m_t2x(t2x),
        m_expr2poly(m_solver, m, m_solver.pm(), &m_t2x) {
        updt_params(p);
        m_cancel = false;
    }

    void updt_params(params_ref const & p) {
        m_max_memory   = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
        m_factor       = p.get_bool("factor", true);  
        m_fparams.updt_params(p);
    }

    void set_cancel(bool f) {
        m_cancel = f;
        m_pm.set_cancel(f);
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
        TRACE("goal2nlsat_bug", tout << "factors:\n" << fs << "\n";); 
        SASSERT(fs.distinct_factors() > 0);
        for (unsigned i = 0; i < fs.distinct_factors(); i++) {
            ps.push_back(fs[i]);
            is_even.push_back(fs.get_degree(i) % 2 == 0);
        }
        if (m_qm.is_neg(fs.get_constant()))
            k = flip(k);
        return m_solver.mk_ineq_atom(k, ps.size(), ps.c_ptr(), is_even.c_ptr());
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
        TRACE("goal2nlsat_bug", tout << "p: " << p << "\nk: " << k << "\n";);
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
                    TRACE("goal2nlsat", tout << "f: " << mk_ismt2_pp(f, m) << "\n";);
                    throw tactic_exception("apply simplify before applying nlsat");
                case OP_AND:
                case OP_OR:
                case OP_IFF:
                case OP_XOR:
                case OP_NOT:
                case OP_IMPLIES:
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
        for (unsigned i = 0; i < num_lits; i++) {
            ls.push_back(process_literal(lits[i]));
        }
        m_solver.mk_clause(ls.size(), ls.c_ptr(), dep);
    }

    void operator()(goal const & g) {
        if (has_term_ite(g))
            throw tactic_exception("eliminate term-ite before applying nlsat");
        unsigned sz = g.size();
        for (unsigned i = 0; i < sz; i++) {
            process(g.form(i), g.dep(i));
        }
    }
};

struct goal2nlsat::scoped_set_imp {
    goal2nlsat & m_owner; 
    scoped_set_imp(goal2nlsat & o, imp & i):m_owner(o) {
        #pragma omp critical (tactic_cancel)
        {
            m_owner.m_imp = &i;
        }
    }
    
    ~scoped_set_imp() {
        #pragma omp critical (tactic_cancel)
        {
            m_owner.m_imp = 0;
        }
    }
};

goal2nlsat::goal2nlsat() {
    m_imp = 0;
}

goal2nlsat::~goal2nlsat() {
    SASSERT(m_imp == 0);
}
    
void goal2nlsat::collect_param_descrs(param_descrs & r) {
    insert_max_memory(r);
    r.insert("factor", CPK_BOOL, "(default: true) factor polynomials.");
    polynomial::factor_params::get_param_descrs(r);
}
    
void goal2nlsat::operator()(goal const & g, params_ref const & p, nlsat::solver & s, expr2var & a2b, expr2var & t2x) {
    imp local_imp(g.m(), p, s, a2b, t2x);
    scoped_set_imp setter(*this, local_imp);
    local_imp(g);
}
    
void goal2nlsat::set_cancel(bool f) {
    if (m_imp)
        m_imp->set_cancel(f);
}
