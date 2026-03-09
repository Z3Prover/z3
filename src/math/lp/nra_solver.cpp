/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Nikolaj Bjorner, Lev Nachmanson
*/

#ifndef SINGLE_THREAD
#include <thread>
#endif
#include <fstream>
#include "math/lp/lar_solver.h"
#include "math/lp/nra_solver.h"
#include "math/lp/nla_coi.h"
#include "nlsat/nlsat_solver.h"
#include "math/polynomial/polynomial.h"
#include "math/polynomial/algebraic_numbers.h"
#include "util/map.h"
#include "util/uint_set.h"
#include "math/lp/nla_core.h"
#include "params/smt_params_helper.hpp"


namespace nra {

typedef nla::mon_eq mon_eq;

typedef nla::variable_map_type variable_map_type;

struct solver::imp {

    lp::lar_solver&           lra;
    reslimit&                 m_limit;  
    params_ref                m_params; 
    u_map<polynomial::var>    m_lp2nl;  // map from lar_solver variables to nlsat::solver variables        
    scoped_ptr<nlsat::solver> m_nlsat;
    scoped_ptr<scoped_anum_vector>   m_values; // values provided by LRA solver
    scoped_ptr<scoped_anum> m_tmp1, m_tmp2;
    nla::coi                  m_coi;
    nla::core&                m_nla_core;
    
    imp(lp::lar_solver& s, reslimit& lim, params_ref const& p, nla::core& nla_core): 
        lra(s), 
        m_limit(lim),
        m_params(p),
        m_coi(nla_core),
        m_nla_core(nla_core) {}

    bool need_check() {
        return m_nla_core.m_to_refine.size() != 0;
    }

    void reset() {
        m_values = nullptr;
        m_tmp1 = nullptr; m_tmp2 = nullptr;
        m_nlsat = alloc(nlsat::solver, m_limit, m_params, false);
        m_values = alloc(scoped_anum_vector, am());
        m_lp2nl.reset();
    }

    // Create polynomial definition for variable v used in setup_assignment_solver.
    // Side-effects: updates m_vars2mon when v is a monic variable.
    void mk_definition(unsigned v, polynomial_ref_vector &definitions, vector<rational>& denominators) {
        auto &pm = m_nlsat->pm();
        polynomial::polynomial_ref p(pm);
        rational den(1);
        if (m_nla_core.emons().is_monic_var(v)) {
            auto const &m = m_nla_core.emons()[v];
            for (auto w : m.vars()) {
                den = denominators[w] * den;
                polynomial_ref pw(definitions.get(w), m_nlsat->pm());
                if (!p)
                    p = pw;
                else
                    p = p * pw;
            }
        }
        else if (lra.column_has_term(v)) {
            for (auto const &[w, coeff] : lra.get_term(v)) 
                den = lcm(denominator(coeff / denominators[w]), den);            
            for (auto const &[w, coeff] : lra.get_term(v)) {
                auto coeff1 = den * coeff / denominators[w];
                polynomial_ref pw(definitions.get(w), m_nlsat->pm());
                if (!p)
                    p = constant(coeff1) * pw;
                else
                    p = p + (constant(coeff1) * pw);
            }
        }
        else {
            p = pm.mk_polynomial(lp2nl(v));  // nlsat var index equals v (verified above when created)
        }
        definitions.push_back(p);
        denominators.push_back(den);
    }

    void setup_solver_poly() {
        m_coi.init();
        auto &pm = m_nlsat->pm();
        polynomial_ref_vector definitions(pm);
        vector<rational> denominators;
        for (unsigned v = 0; v < lra.number_of_vars(); ++v) {
            if (m_coi.vars().contains(v)) {
                auto j = m_nlsat->mk_var(lra.var_is_int(v));
                m_lp2nl.insert(v, j);  // we don't really need this. It is going to be the identify map.
                mk_definition(v, definitions, denominators);
            }
            else {
                definitions.push_back(nullptr);
                denominators.push_back(rational(0));
            }
        }

        // we rely on that all information encoded into the tableau is present as a constraint.
        for (auto ci : m_coi.constraints()) {
            auto &c = lra.constraints()[ci];
            auto &pm = m_nlsat->pm();
            auto k = c.kind();
            auto rhs = c.rhs();
            auto lhs = c.coeffs();
            rational den = denominator(rhs);
            //
            // let v := p / denominators[v]
            //           
            // sum(coeff[v] * v) k rhs
            // ==
            // sum(coeff[v] * (p / denominators[v])) k rhs
            // ==
            // sum((coeff[v] / denominators[v]) * p) k rhs
            //


            for (auto [coeff, v] : lhs)
                den = lcm(den, denominator(coeff / denominators[v]));
            polynomial::polynomial_ref p(pm);
            p = pm.mk_const(-den * rhs);

            for (auto [coeff, v] : lhs) {
                polynomial_ref poly(pm);
                poly = definitions.get(v);
                poly = poly * constant(den * coeff / denominators[v]);
                p = p + poly;
            }
            add_constraint(p, ci, k);
            TRACE(nra, tout << "constraint " << ci << ": " << p << " " << k << " 0\n";
            lra.constraints().display(tout, ci) << "\n");
        }
        definitions.reset();
    }

    void setup_solver_terms() {
        m_coi.init();
        // add linear inequalities from lra_solver
        for (auto ci : m_coi.constraints())
            add_constraint(ci);

        // add polynomial definitions.
        for (auto const &m : m_coi.mons())
            add_monic_eq(m_nla_core.emons()[m]);

        // add term definitions.
        for (unsigned i : m_coi.terms())
            add_term(i);
    }



    polynomial::polynomial_ref sub(polynomial::polynomial *a, polynomial::polynomial *b) {
        return polynomial_ref(m_nlsat->pm().sub(a, b), m_nlsat->pm());
    }
    polynomial::polynomial_ref mul(polynomial::polynomial *a, polynomial::polynomial *b) {
        return polynomial_ref(m_nlsat->pm().mul(a, b), m_nlsat->pm());
    }
    polynomial::polynomial_ref var(lp::lpvar v) {
        return polynomial_ref(m_nlsat->pm().mk_polynomial(lp2nl(v)), m_nlsat->pm());
    }
    polynomial::polynomial_ref constant(rational const& r) {
        return polynomial_ref(m_nlsat->pm().mk_const(r), m_nlsat->pm());
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
        reset();
        vector<nlsat::assumption, false> core;        
        
        smt_params_helper p(m_params);

	    setup_solver_poly();

        TRACE(nra, m_nlsat->display(tout));

        if (p.arith_nl_log()) {
            static unsigned id = 0;
            std::stringstream strm;

#ifndef SINGLE_THREAD            
            std::thread::id this_id = std::this_thread::get_id();
            strm << "nla_" << this_id << "." << (++id) << ".smt2";
#else
            strm << "nla_" << (++id) << ".smt2";
#endif
            std::ofstream out(strm.str());
            m_nlsat->display_smt2(out);
            out << "(check-sat)\n";
            out.close();
        }

        lbool r = l_undef;
        statistics& st = m_nla_core.lp_settings().stats().m_st;
        try {
            r = m_nlsat->check();
        }
        catch (z3_exception&) {
            if (m_limit.is_canceled()) {
                r = l_undef;
            }
            else {
                m_nlsat->collect_statistics(st);
                throw;
            }
        }
        m_nlsat->collect_statistics(st);
        TRACE(nra, tout << "nra result " << r << "\n");
        CTRACE(nra, false,
              m_nlsat->display(tout << r << "\n");
              display(tout);
              for (auto [j, x] : m_lp2nl) tout << "j" << j << " := x" << x << "\n";);
        switch (r) {
        case l_true:
            m_nlsat->restore_order();
            m_nla_core.set_use_nra_model(true);
            lra.init_model();
            for (lp::constraint_index ci : lra.constraints().indices())
                if (!check_constraint(ci)) {
                    IF_VERBOSE(0, verbose_stream() << "constraint " << ci << " violated\n";
                               lra.constraints().display(verbose_stream()));
                    UNREACHABLE();
                    return l_undef;
                }
            for (auto const &m : m_nla_core.emons()) {
                if (!check_monic(m)) {
                    IF_VERBOSE(0, verbose_stream() << "monic " << m << " violated\n";
                               lra.constraints().display(verbose_stream()));
                    UNREACHABLE();
                    return l_undef;
                }
            }
            break;
        case l_false: {
            lp::explanation ex;
            m_nlsat->get_core(core);
            nla::lemma_builder lemma(m_nla_core, __FUNCTION__);
            for (auto c : core) {
                unsigned idx = static_cast<unsigned>(static_cast<imp *>(c) - this);
                ex.push_back(idx);
            }

            lemma &= ex;
            m_nla_core.set_use_nra_model(true);
            TRACE(nra, tout << lemma << "\n");
            break;
        }
        case l_undef:
            break;
        }
        return r;
    }   


    void add_monic_eq_bound(mon_eq const& m) {
        if (!lra.column_has_lower_bound(m.var()) && 
            !lra.column_has_upper_bound(m.var()))
            return;
        polynomial::manager& pm = m_nlsat->pm();
        svector<polynomial::var> vars;
        for (auto v : m.vars()) 
            vars.push_back(lp2nl(v));
        auto v = m.var();
        polynomial::monomial_ref m1(pm.mk_monomial(vars.size(), vars.data()), pm);
        polynomial::monomial * mls[1] = { m1 };
        polynomial::scoped_numeral_vector coeffs(pm.m());
        coeffs.push_back(mpz(1));
        polynomial::polynomial_ref p(pm.mk_polynomial(1, coeffs.data(), mls),  pm);
        if (lra.column_has_lower_bound(v)) 
            add_lb_p(lra.get_lower_bound(v), p, lra.get_column_lower_bound_witness(v));
        if (lra.column_has_upper_bound(v)) 
            add_ub_p(lra.get_upper_bound(v), p, lra.get_column_upper_bound_witness(v));
    }

    void add_monic_eq(mon_eq const& m) {
        polynomial::manager& pm = m_nlsat->pm();
        svector<polynomial::var> vars;
        for (auto v : m.vars()) 
            vars.push_back(lp2nl(v));
        polynomial::monomial_ref m1(pm.mk_monomial(vars.size(), vars.data()), pm);
        polynomial::monomial_ref m2(pm.mk_monomial(lp2nl(m.var()), 1), pm);
        polynomial::monomial * mls[2] = { m1, m2 };
        polynomial::scoped_numeral_vector coeffs(pm.m());
        coeffs.push_back(mpz(1));
        coeffs.push_back(mpz(-1));
        polynomial::polynomial_ref p(pm.mk_polynomial(2, coeffs.data(), mls),  pm);
        auto lit = mk_literal(p.get(), lp::lconstraint_kind::EQ);
        m_nlsat->mk_clause(1, &lit, nullptr);
    }

    nlsat::literal mk_literal(polynomial::polynomial *p, lp::lconstraint_kind k) {
        polynomial::polynomial *ps[1] = { p };
        bool is_even[1] = { false };
        switch (k) {
        case lp::lconstraint_kind::LE: return ~m_nlsat->mk_ineq_literal(nlsat::atom::kind::GT, 1, ps, is_even);
        case lp::lconstraint_kind::GE: return ~m_nlsat->mk_ineq_literal(nlsat::atom::kind::LT, 1, ps, is_even);
        case lp::lconstraint_kind::LT: return m_nlsat->mk_ineq_literal(nlsat::atom::kind::LT, 1, ps, is_even);
        case lp::lconstraint_kind::GT: return m_nlsat->mk_ineq_literal(nlsat::atom::kind::GT, 1, ps, is_even);
        case lp::lconstraint_kind::EQ: return m_nlsat->mk_ineq_literal(nlsat::atom::kind::EQ, 1, ps, is_even);
        default: UNREACHABLE();  // unreachable
        }
        throw default_exception("uexpected operator");
    }

    void add_constraint(unsigned idx) {
        auto& c = lra.constraints()[idx];
        auto& pm = m_nlsat->pm();
        auto k = c.kind();
        auto rhs = c.rhs();
        auto lhs = c.coeffs();
        auto sz = lhs.size();
        svector<polynomial::var> vars;
        rational den = denominator(rhs);
        for (auto [coeff, v] : lhs) {
            vars.push_back(lp2nl(v));
            den = lcm(den, denominator(coeff));
        }
        vector<rational> coeffs;
        for (auto kv : lhs) {
            coeffs.push_back(den * kv.first);
        }
        rhs *= den;
        polynomial::polynomial_ref p(pm.mk_linear(sz, coeffs.data(), vars.data(), -rhs), pm);
        nlsat::literal lit = mk_literal(p.get(), k);
        nlsat::assumption a = this + idx;
        m_nlsat->mk_clause(1, &lit, a);
    }

    nlsat::literal add_constraint(polynomial::polynomial *p, unsigned idx, lp::lconstraint_kind k) {
        polynomial::polynomial *ps[1] = {p};
        bool is_even[1] = {false};
        nlsat::literal lit;
        nlsat::assumption a = this + idx;
        switch (k) {
        case lp::lconstraint_kind::LE: lit = ~m_nlsat->mk_ineq_literal(nlsat::atom::kind::GT, 1, ps, is_even); break;
        case lp::lconstraint_kind::GE: lit = ~m_nlsat->mk_ineq_literal(nlsat::atom::kind::LT, 1, ps, is_even); break;
        case lp::lconstraint_kind::LT: lit = m_nlsat->mk_ineq_literal(nlsat::atom::kind::LT, 1, ps, is_even); break;
        case lp::lconstraint_kind::GT: lit = m_nlsat->mk_ineq_literal(nlsat::atom::kind::GT, 1, ps, is_even); break;
        case lp::lconstraint_kind::EQ: lit = m_nlsat->mk_ineq_literal(nlsat::atom::kind::EQ, 1, ps, is_even); break;
        default: UNREACHABLE();  // unreachable
        }
        m_nlsat->mk_clause(1, &lit, a);
        return lit;
    }

    bool check_monic(mon_eq const& m) {
        scoped_anum val1(am()), val2(am());
        am().set(val1, value(m.var()));
        am().set(val2, rational::one().to_mpq());
        for (auto v : m.vars()) 
            am().mul(val2, value(v), val2);
        return am().eq(val1, val2);
    }

    bool check_constraint(unsigned idx) {
        auto& c = lra.constraints()[idx];
        auto k = c.kind();
        auto offset = -c.rhs();
        auto lhs = c.coeffs();
        
        scoped_anum val(am()), mon(am());
        am().set(val, offset.to_mpq());
        for (auto [coeff, v] : lhs) {
            am().set(mon, coeff.to_mpq());
            am().mul(mon, value(v), mon);
            am().add(val, mon, val);
        }
        am().set(mon, rational::zero().to_mpq());
        switch (k) {
        case lp::lconstraint_kind::LE:
            return am().le(val, mon);
        case lp::lconstraint_kind::GE:
            return am().ge(val, mon);
        case lp::lconstraint_kind::LT:
            return am().lt(val, mon);
        case lp::lconstraint_kind::GT:
            return am().gt(val, mon);
        case lp::lconstraint_kind::EQ:
            return am().eq(val, mon);
        default:
            UNREACHABLE();
        }
        return false;
    }

    lbool check(dd::solver::equation_vector const& eqs) {
        reset();
        for (auto const& eq : eqs)
            add_eq(*eq);
        for (auto const& m : m_nla_core.emons())
            if (any_of(m.vars(), [&](lp::lpvar v) { return m_lp2nl.contains(v); }))
                add_monic_eq_bound(m);
        for (unsigned i : m_coi.terms())
            add_term(i);
        for (auto const& [v, w] : m_lp2nl) {
            if (lra.column_has_lower_bound(v))
                add_lb(lra.get_lower_bound(v), w, lra.get_column_lower_bound_witness(v));
            if (lra.column_has_upper_bound(v))
                add_ub(lra.get_upper_bound(v), w, lra.get_column_upper_bound_witness(v));
        }
        
        lbool r = l_undef;
        statistics& st = m_nla_core.lp_settings().stats().m_st;
        try {
            r = m_nlsat->check();
        }
        catch (z3_exception&) {
            if (m_limit.is_canceled()) {
                r = l_undef;
            }
            else {
                m_nlsat->collect_statistics(st);
                throw;
            }
        }
        m_nlsat->collect_statistics(st);
        
        switch (r) {
        case l_true:
            m_nlsat->restore_order();
            m_nla_core.set_use_nra_model(true);
            lra.init_model();
            for (lp::constraint_index ci : lra.constraints().indices())
                if (!check_constraint(ci))
                    return l_undef;
            for (auto const& m : m_nla_core.emons()) 
                if (!check_monic(m))
                    return l_undef;
            break;
        case l_false: {
            lp::explanation ex;
            vector<nlsat::assumption, false> core;
            m_nlsat->get_core(core);
            u_dependency_manager dm;
            vector<unsigned, false> lv;
            for (auto c : core)
                dm.linearize(static_cast<u_dependency*>(c), lv);
            for (auto ci : lv)
                ex.push_back(ci);
            nla::lemma_builder lemma(m_nla_core, __FUNCTION__);
            lemma &= ex;
            TRACE(nra, tout << lemma << "\n");
            break;
        }
        case l_undef:
            break;
        } 
        return r;
    }

    lbool check(vector<dd::pdd> const& eqs) {
        reset();
        for (auto const& eq : eqs)
            add_eq(eq);
        for (auto const& m : m_nla_core.emons())
            add_monic_eq(m);
        for (auto const& [v, w] : m_lp2nl) {
            if (lra.column_has_lower_bound(v))
                add_lb(lra.get_lower_bound(v), w);
            if (lra.column_has_upper_bound(v))
                add_ub(lra.get_upper_bound(v), w);
        }
        
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

        if (r == l_true)
            return r;

        IF_VERBOSE(0, verbose_stream() << "check-nra " << r << "\n";
                   m_nlsat->display(verbose_stream());
                   for (auto const& [v, w] : m_lp2nl) {
                       if (lra.column_has_lower_bound(v))
                           verbose_stream() << "x" << w << " >= " << lra.get_lower_bound(v) << "\n";
                       if (lra.column_has_upper_bound(v))
                           verbose_stream() << "x" << w << " <= " << lra.get_upper_bound(v) << "\n";
                   });
            
        return r;
    }
        
    void add_eq(dd::solver::equation const& eq) {
        add_eq(eq.poly(), eq.dep());
    }
        
    void add_eq(dd::pdd const& eq, nlsat::assumption a = nullptr) {
        dd::pdd normeq = eq;
        rational lc(1);
        for (auto const& [c, m] : eq)
            lc = lcm(denominator(c), lc);
        if (lc != 1)
            normeq *= lc;
        polynomial::manager& pm = m_nlsat->pm();
        polynomial::polynomial_ref p(pdd2polynomial(normeq), pm);
        bool is_even[1] = {false};
        polynomial::polynomial* ps[1] = {p};
        nlsat::literal lit = m_nlsat->mk_ineq_literal(nlsat::atom::kind::EQ, 1, ps, is_even);
        m_nlsat->mk_clause(1, &lit, a);
    }

    void add_lb(lp::impq const& b, unsigned w, nlsat::assumption a = nullptr) {
        polynomial::manager& pm = m_nlsat->pm();
        polynomial::polynomial_ref p(pm.mk_polynomial(w), pm);
        add_lb_p(b, p, a);
    }
        
    void add_ub(lp::impq const& b, unsigned w, nlsat::assumption a = nullptr) {
        polynomial::manager& pm = m_nlsat->pm();
        polynomial::polynomial_ref p(pm.mk_polynomial(w), pm);
        add_ub_p(b, p, a);
    }

    void add_lb_p(lp::impq const& b, polynomial::polynomial* p, nlsat::assumption a = nullptr) {
        add_bound_p(b.x, p, b.y <= 0, b.y > 0 ? nlsat::atom::kind::GT : nlsat::atom::kind::LT, a);
    }

    void add_ub_p(lp::impq const& b, polynomial::polynomial* p, nlsat::assumption a = nullptr) {
        add_bound_p(b.x, p, b.y >= 0, b.y < 0 ? nlsat::atom::kind::LT : nlsat::atom::kind::GT, a);
    }

    // w - bound < 0
    // w - bound > 0

    void add_bound_p(lp::mpq const& bound, polynomial::polynomial* p1, bool neg, nlsat::atom::kind k, nlsat::assumption a = nullptr) {
        polynomial::manager& pm = m_nlsat->pm();
        polynomial::polynomial_ref p2(pm.mk_const(bound), pm);
        polynomial::polynomial_ref p(pm.sub(p1, p2), pm);
        polynomial::polynomial* ps[1] = {p};
        bool is_even[1] = {false};
        nlsat::literal lit = m_nlsat->mk_ineq_literal(k, 1, ps, is_even);
        if (neg)
            lit.neg();
        m_nlsat->mk_clause(1, &lit, a);
    }

    void add_bound(lp::mpq const& bound, unsigned w, bool neg, nlsat::atom::kind k, nlsat::assumption a = nullptr) {
        polynomial::manager& pm = m_nlsat->pm();
        polynomial::polynomial_ref p(pm.mk_polynomial(w), pm);
        add_bound_p(bound, p, neg, k, a);
    }

    polynomial::polynomial* pdd2polynomial(dd::pdd const& p) {
        polynomial::manager& pm = m_nlsat->pm();
        if (p.is_val())
            return pm.mk_const(p.val());
        polynomial::polynomial_ref lo(pdd2polynomial(p.lo()), pm);
        polynomial::polynomial_ref hi(pdd2polynomial(p.hi()), pm);
        unsigned w, v = p.var();
        if (!m_lp2nl.find(v, w)) {
            w = m_nlsat->mk_var(is_int(v));
            m_lp2nl.insert(v, w);
        }
        polynomial::polynomial_ref vp(pm.mk_polynomial(w, 1), pm);
        polynomial::polynomial_ref mp(pm.mul(vp, hi), pm);
        return pm.add(lo, mp);
    }
        
        
        
    bool is_int(lp::lpvar v) {
        return lra.var_is_int(v);
    }

    polynomial::var lp2nl(lp::lpvar v) {
        polynomial::var r;
        if (!m_lp2nl.find(v, r)) {
            r = m_nlsat->mk_var(is_int(v));
            m_lp2nl.insert(v, r);
            if (!m_coi.terms().contains(v) && lra.column_has_term(v)) {
                m_coi.terms().insert(v);
            }
        }
        return r;
    }
    //
    void add_term(unsigned term_column) {
        const lp::lar_term& t = lra.get_term(term_column);
        // code that creates a polynomial equality between the linear coefficients and
        // variable representing the term.
        svector<polynomial::var> vars;
        rational den(1);
        for (lp::lar_term::ival kv : t) {
            vars.push_back(lp2nl(kv.j()));
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
        polynomial::polynomial* ps[1] = {p};
        bool is_even[1] = {false};
        nlsat::literal lit = m_nlsat->mk_ineq_literal(nlsat::atom::kind::EQ, 1, ps, is_even);
        m_nlsat->mk_clause(1, &lit, nullptr);
    }

    nlsat::anum const &value(lp::lpvar v) {
        init_values(v + 1);
        return (*m_values)[v];
    }

    void init_values(unsigned sz) {
        if (m_values->size() >= sz)
            return;
        unsigned w;
        scoped_anum a(am());
        for (unsigned v = m_values->size(); v < sz; ++v) {
            if (m_nla_core.emons().is_monic_var(v)) {                 
                am().set(a, 1);
                auto &m = m_nla_core.emon(v);

                for (auto x : m.vars()) 
                    am().mul(a, (*m_values)[x], a);
                m_values->push_back(a);
            }      
            else if (lra.column_has_term(v)) {
                scoped_anum b(am());
                am().set(a, 0);
                for (auto const &[w, coeff] : lra.get_term(v)) {                    
                    am().set(b, coeff.to_mpq());
                    am().mul(b, (*m_values)[w], b);
                    am().add(a, b, a);
                }
                m_values->push_back(a);
            }
            else if (m_lp2nl.find(v, w)) {
                m_values->push_back(m_nlsat->value(w));
            }
            else {
                am().set(a, m_nla_core.val(v).to_mpq());
                m_values->push_back(a);
            }
        }
    }


    void set_value(lp::lpvar v, rational const& value) {
        if (!m_values)
            m_values = alloc(scoped_anum_vector, am());
        scoped_anum a(am());
        am().set(a, value.to_mpq());
        while (m_values->size() <= v)
            m_values->push_back(a);
        am().set((*m_values)[v], a);
    }

    nlsat::anum_manager& am() {
        return m_nlsat->am();
    }

    scoped_anum& tmp1() {
        if (!m_tmp1) 
            m_tmp1 = alloc(scoped_anum, am());
        return *m_tmp1;
    }

    scoped_anum& tmp2() {
        if (!m_tmp2) 
            m_tmp2 = alloc(scoped_anum, am());
        return *m_tmp2;
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

lbool solver::check(vector<dd::pdd> const& eqs) {
    return m_imp->check(eqs);
}

lbool solver::check(dd::solver::equation_vector const& eqs) {
    return m_imp->check(eqs);
}

bool solver::need_check() {
    return m_imp->need_check();
}

std::ostream& solver::display(std::ostream& out) const {
    return m_imp->display(out);
}

nlsat::anum const& solver::value(lp::lpvar v) {
    return m_imp->value(v);
}

nlsat::anum_manager& solver::am() {
    return m_imp->am();
}

scoped_anum& solver::tmp1() { return m_imp->tmp1(); }

scoped_anum& solver::tmp2() { return m_imp->tmp2(); }
 

void solver::updt_params(params_ref& p) {
    m_imp->updt_params(p);
}

void solver::set_value(lp::lpvar v, rational const& value) {
    m_imp->set_value(v, value);
}

}
