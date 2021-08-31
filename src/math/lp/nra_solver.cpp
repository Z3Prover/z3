/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Nikolaj Bjorner, Lev Nachmanson
*/

#include "math/lp/lar_solver.h"
#include "math/lp/nra_solver.h"
#include "nlsat/nlsat_solver.h"
#include "math/polynomial/polynomial.h"
#include "math/polynomial/algebraic_numbers.h"
#include "util/map.h"
#include "math/lp/u_set.h"
#include "math/lp/nla_core.h"


namespace nra {

typedef nla::mon_eq mon_eq;

typedef nla::variable_map_type variable_map_type;
struct solver::imp {
    lp::lar_solver&           s;
    reslimit&                 m_limit;  
    params_ref                m_params; 
    u_map<polynomial::var>    m_lp2nl;  // map from lar_solver variables to nlsat::solver variables        
    lp::u_set                 m_term_set;
    scoped_ptr<nlsat::solver> m_nlsat;
    scoped_ptr<scoped_anum>   m_zero;
    mutable variable_map_type m_variable_values; // current model        
    nla::core&                m_nla_core;    
    imp(lp::lar_solver& s, reslimit& lim, params_ref const& p, nla::core& nla_core): 
        s(s), 
        m_limit(lim),
        m_params(p),
        m_nla_core(nla_core) {}

    bool need_check() {
        return m_nla_core.m_to_refine.size() != 0;
    }


    /**
       \brief one-shot nlsat check.
       A one shot checker is the least functionality that can 
       enable non-linear reasoning. 
       In addition to checking satisfiability we would also need
       to identify equalities in the model that should be assumed
       with the remaining solver.
           
       TBD: use partial model from lra_solver to prime the state of nlsat_solver.
       TBD: explore more incremental ways of applying nlsat (using assumptions)
    */
    lbool check() {        
        SASSERT(need_check());
        m_zero = nullptr;
        m_nlsat = alloc(nlsat::solver, m_limit, m_params, false);
        m_zero = alloc(scoped_anum, am());
        m_term_set.clear();
        m_lp2nl.reset();
        vector<nlsat::assumption, false> core;

        // add linear inequalities from lra_solver
        for (lp::constraint_index ci : s.constraints().indices()) {
            add_constraint(ci);
        }

        // add polynomial definitions.
        for (auto const& m : m_nla_core.emons()) {
             add_monic_eq(m);
        }
        for (unsigned i : m_term_set) {
            add_term(i);
        }
        // TBD: add variable bounds?

        lbool r = l_undef;
        try {
            r = m_nlsat->check(); 
        }
        catch (z3_exception&) {
            if (m_limit.is_canceled()) {
                r = l_undef;
            }
            else {
                throw;
            }
        }
        TRACE("nra", 
              m_nlsat->display(tout << r << "\n");
              display(tout); 
              for (auto kv : m_lp2nl) 
                  tout << "j" << kv.m_key << " := x" << kv.m_value << "\n";
              );
        switch (r) {
        case l_true: 
            m_nla_core.set_use_nra_model(true);
            break;
        case l_false: {
            lp::explanation ex;
            m_nlsat->get_core(core);
            for (auto c : core) {
                unsigned idx = static_cast<unsigned>(static_cast<imp*>(c) - this);
                ex.push_back(idx);
                TRACE("arith", tout << "ex: " << idx << "\n";);
            }
            nla::new_lemma lemma(m_nla_core, __FUNCTION__);
            lemma &= ex;
            m_nla_core.set_use_nra_model(true);
            break;
        }
        case l_undef:
            break;
        }            
        return r;
    }                

    void add_monic_eq(mon_eq const& m) {
        polynomial::manager& pm = m_nlsat->pm();
        svector<polynomial::var> vars;
        for (auto v : m.vars()) {
            vars.push_back(lp2nl(v));
        }
        polynomial::monomial_ref m1(pm.mk_monomial(vars.size(), vars.data()), pm);
        polynomial::monomial_ref m2(pm.mk_monomial(lp2nl(m.var()), 1), pm);
        polynomial::monomial * mls[2] = { m1, m2 };
        polynomial::scoped_numeral_vector coeffs(pm.m());
        coeffs.push_back(mpz(1));
        coeffs.push_back(mpz(-1));
        polynomial::polynomial_ref p(pm.mk_polynomial(2, coeffs.data(), mls),  pm);
        polynomial::polynomial* ps[1] = { p };
        bool even[1] = { false };
        nlsat::literal lit = m_nlsat->mk_ineq_literal(nlsat::atom::kind::EQ, 1, ps, even);
        m_nlsat->mk_clause(1, &lit, nullptr);
    }

    void add_constraint(unsigned idx) {
        auto& c = s.constraints()[idx];
        auto& pm = m_nlsat->pm();
        auto k = c.kind();
        auto rhs = c.rhs();
        auto lhs = c.coeffs();
        auto sz = lhs.size();
        svector<polynomial::var> vars;
        rational den = denominator(rhs);
        for (auto kv : lhs) {
            vars.push_back(lp2nl(kv.second));
            den = lcm(den, denominator(kv.first));
        }
        vector<rational> coeffs;
        for (auto kv : lhs) {
            coeffs.push_back(den * kv.first);
        }
        rhs *= den;
        polynomial::polynomial_ref p(pm.mk_linear(sz, coeffs.data(), vars.data(), -rhs), pm);
        polynomial::polynomial* ps[1] = { p };
        bool is_even[1] = { false };
        nlsat::literal lit;
        nlsat::assumption a = this + idx;
        switch (k) {
        case lp::lconstraint_kind::LE:
            lit = ~m_nlsat->mk_ineq_literal(nlsat::atom::kind::GT, 1, ps, is_even);
            break;
        case lp::lconstraint_kind::GE:
            lit = ~m_nlsat->mk_ineq_literal(nlsat::atom::kind::LT, 1, ps, is_even);
            break;
        case lp::lconstraint_kind::LT:
            lit = m_nlsat->mk_ineq_literal(nlsat::atom::kind::LT, 1, ps, is_even);
            break;
        case lp::lconstraint_kind::GT:
            lit = m_nlsat->mk_ineq_literal(nlsat::atom::kind::GT, 1, ps, is_even);
            break;
        case lp::lconstraint_kind::EQ:
            lit = m_nlsat->mk_ineq_literal(nlsat::atom::kind::EQ, 1, ps, is_even);                
            break;
        default:
            lp_assert(false); // unreachable
        }
        m_nlsat->mk_clause(1, &lit, a);
    }               

    bool is_int(lp::var_index v) {
        return s.var_is_int(v);
    }


    polynomial::var lp2nl(lp::var_index v) {
        polynomial::var r;
        if (!m_lp2nl.find(v, r)) {
            r = m_nlsat->mk_var(is_int(v));
            m_lp2nl.insert(v, r);
            if (!m_term_set.contains(v) && s.column_corresponds_to_term(v)) {
                if (v >= m_term_set.data_size())
                    m_term_set.resize(v + 1);
                m_term_set.insert(v);
            }
        }
        return r;
    }
    //
    void add_term(unsigned term_column) {
        lp::tv ti = lp::tv::raw(s.column_to_reported_index(term_column));
        const lp::lar_term& t = s.get_term(ti); 
        //  code that creates a polynomial equality between the linear coefficients and
        // variable representing the term.
        svector<polynomial::var> vars;
        rational den(1);
        for (lp::lar_term::ival kv : t) {
            vars.push_back(lp2nl(kv.column().index()));
            den = lcm(den, denominator(kv.coeff()));
        }
        vars.push_back(lp2nl(term_column));
        
        vector<rational> coeffs;
        for (auto kv : t) {
            coeffs.push_back(den * kv.coeff());
        }
        coeffs.push_back(-den);
        polynomial::manager& pm = m_nlsat->pm();
        polynomial::polynomial_ref p(pm.mk_linear(coeffs.size(), coeffs.data(), vars.data(), rational(0)), pm);
        polynomial::polynomial* ps[1] = { p };
        bool is_even[1] = { false };
        nlsat::literal lit = m_nlsat->mk_ineq_literal(nlsat::atom::kind::EQ, 1, ps, is_even);                
        m_nlsat->mk_clause(1, &lit, nullptr);
    }

    nlsat::anum const& value(lp::var_index v) const {
        polynomial::var pv;
        if (m_lp2nl.find(v, pv))
            return m_nlsat->value(pv);
        else
            return *m_zero;
    }

    nlsat::anum_manager& am() {
        return m_nlsat->am();
    }

    void updt_params(params_ref& p) {
        m_params.append(p);
    }


    std::ostream& display(std::ostream& out) const {
        for (auto m : m_nla_core.emons()) {
            out << "j" << m.var() << " = ";
            for (auto v : m.vars()) {
                out << "j" << v << " ";
            }
            out << "\n";
        }
        return out;
    }
};

solver::solver(lp::lar_solver& s, reslimit& lim, nla::core & nla_core, params_ref const& p) {
    m_imp = alloc(imp, s, lim, p, nla_core);
}

solver::~solver() {
    dealloc(m_imp);
}


lbool solver::check() {
    return m_imp->check();
}

bool solver::need_check() {
    return m_imp->need_check();
}

std::ostream& solver::display(std::ostream& out) const {
    return m_imp->display(out);
}

nlsat::anum const& solver::value(lp::var_index v) const {
    return m_imp->value(v);
}

nlsat::anum_manager& solver::am() {
    return m_imp->am();
}

void solver::updt_params(params_ref& p) {
    m_imp->updt_params(p);
}

}
