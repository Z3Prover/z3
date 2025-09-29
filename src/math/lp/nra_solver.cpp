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
#include "nlsat/nlsat_solver.h"
#include "nlsat/nlsat_assignment.h"
#include "math/polynomial/polynomial.h"
#include "math/polynomial/algebraic_numbers.h"
#include "util/map.h"
#include "util/uint_set.h"
#include "math/lp/nla_core.h"
#include "math/lp/monic.h"
#include "params/smt_params_helper.hpp"


namespace nra {

typedef nla::mon_eq mon_eq;

typedef nla::variable_map_type variable_map_type;

struct solver::imp {
    lp::lar_solver&           lra;
    reslimit&                 m_limit;  
    params_ref                m_params; 
    u_map<polynomial::var>    m_lp2nl;  // map from lar_solver variables to nlsat::solver variables        
    indexed_uint_set          m_term_set;
    scoped_ptr<nlsat::solver> m_nlsat;
    scoped_ptr<scoped_anum_vector>   m_values; // values provided by LRA solver
    scoped_ptr<scoped_anum> m_tmp1, m_tmp2;
    nla::core&                m_nla_core;
    
    imp(lp::lar_solver& s, reslimit& lim, params_ref const& p, nla::core& nla_core): 
        lra(s), 
        m_limit(lim),
        m_params(p),
        m_nla_core(nla_core) {}

    bool need_check() {
        return m_nla_core.m_to_refine.size() != 0;
    }

    indexed_uint_set m_mon_set, m_constraint_set;

    struct occurs {
        unsigned_vector constraints;
        unsigned_vector monics;
        unsigned_vector terms;
    };

    void init_cone_of_influence() {
        indexed_uint_set visited;
        unsigned_vector todo;
        vector<occurs> var2occurs;
        m_term_set.reset();
        m_mon_set.reset();
        m_constraint_set.reset();

        for (auto ci : lra.constraints().indices()) {
            auto const& c = lra.constraints()[ci];
            if (c.is_auxiliary())
                continue;
            for (auto const& [coeff, v] : c.coeffs()) {
                var2occurs.reserve(v + 1);
                var2occurs[v].constraints.push_back(ci);
            }
        }

        for (auto const& m : m_nla_core.emons()) {
            for (auto v : m.vars()) {
                var2occurs.reserve(v + 1);
                var2occurs[v].monics.push_back(m.var());
            }
        }

        for (const auto *t :  lra.terms() ) {
            for (auto const iv : *t) {
                auto v = iv.j();
                var2occurs.reserve(v + 1);
                var2occurs[v].terms.push_back(t->j());
            }
        }

        for (auto const& m : m_nla_core.m_to_refine)
            todo.push_back(m);

        for (unsigned i = 0; i < todo.size(); ++i) {
            auto v = todo[i];
            if (visited.contains(v))
                continue;
            visited.insert(v);
            var2occurs.reserve(v + 1);
            for (auto ci : var2occurs[v].constraints) {
                m_constraint_set.insert(ci);
                auto const& c = lra.constraints()[ci];
                for (auto const& [coeff, w] : c.coeffs())
                    todo.push_back(w);
            }
            for (auto w : var2occurs[v].monics)
                todo.push_back(w);

            for (auto ti : var2occurs[v].terms) {
                for (auto iv : lra.get_term(ti))
                    todo.push_back(iv.j());
                todo.push_back(ti);
            }

            if (lra.column_has_term(v)) {
                m_term_set.insert(v);
                for (auto kv : lra.get_term(v))
                    todo.push_back(kv.j());
            }            

            if (m_nla_core.is_monic_var(v)) {
                m_mon_set.insert(v);
                for (auto w : m_nla_core.emons()[v])
                    todo.push_back(w);
            }
        }
    }

    void reset() {
        m_values = nullptr;
        m_tmp1 = nullptr; m_tmp2 = nullptr;
        m_nlsat = alloc(nlsat::solver, m_limit, m_params, false);
        m_values = alloc(scoped_anum_vector, am());
        m_term_set.reset();
        m_lp2nl.reset();
    }

    void setup_solver() {
        SASSERT(need_check());
        reset();

        init_cone_of_influence();
        // add linear inequalities from lra_solver
        for (auto ci : m_constraint_set)
            add_constraint(ci);

        // add polynomial definitions.
        for (auto const& m : m_mon_set)
            add_monic_eq(m_nla_core.emons()[m]);

        // add term definitions.
        for (unsigned i : m_term_set)
            add_term(i);

        TRACE(nra, m_nlsat->display(tout));

        smt_params_helper p(m_params);
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
    }

    void validate_constraints() {
        for (lp::constraint_index ci : lra.constraints().indices())
            if (!check_constraint(ci)) {
                IF_VERBOSE(0, verbose_stream() << "constraint " << ci << " violated\n";
                           lra.constraints().display(verbose_stream()));
                UNREACHABLE();
                return;
            }
        for (auto const& m : m_nla_core.emons()) {
            if (!check_monic(m)) {
                IF_VERBOSE(0, verbose_stream() << "monic " << m << " violated\n";
                           lra.constraints().display(verbose_stream()));
                UNREACHABLE();
                return;
            }
        }
    }

    bool check_constraints() {
        for (lp::constraint_index ci : lra.constraints().indices())
            if (!check_constraint(ci))
                return false;
        for (auto const& m : m_nla_core.emons())
            if (!check_monic(m))
                return false;
        return true;
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
        setup_solver();
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
        TRACE(nra,
              m_nlsat->display(tout << r << "\n");
              display(tout);
              for (auto [j, x] : m_lp2nl) tout << "j" << j << " := x" << x << "\n";);
        switch (r) {
        case l_true:
            m_nla_core.set_use_nra_model(true);
            lra.init_model();
            validate_constraints();
            break;
        case l_false: {
            lp::explanation ex;
            constraint_core2ex(ex);
            nla::lemma_builder lemma(m_nla_core, __FUNCTION__);
            lemma &= ex;
            m_nla_core.set_use_nra_model(true);
            break;
        }
        case l_undef:
            break;
        }
        return r;
    }

    void process_polynomial_check_assignment(unsigned num_mon, polynomial::polynomial const* p, rational& bound,                 const u_map<lp::lpvar>& nl2lp, lp::lar_term& t) {
        polynomial::manager& pm = m_nlsat->pm();
        for (unsigned i = 0; i < num_mon; ++i) {
            polynomial::monomial* m = pm.get_monomial(p, i);
            TRACE(nra, tout << "monomial: "; pm.display(tout, m); tout << "\n";);
            auto& coeff = pm.coeff(p, i);
            TRACE(nra, tout << "coeff:";  pm.m().display(tout, coeff);); 
                 
            unsigned num_vars = pm.size(m);
            lp::lpvar v = lp::null_lpvar;
            // add mon * coeff to t;
            switch (num_vars) {                            
            case 0:
                bound -= coeff;
                break;
            case 1: {
                unsigned mon_var = pm.get_var(m, 0);
                auto v = nl2lp[mon_var];
                TRACE(nra, tout << "nl2lp[" << mon_var << "]:" << v << std::endl;);
                rational s;
                SASSERT(v != (unsigned)-1);
                v = m_nla_core.reduce_var_to_rooted(v, s);
                t.add_monomial(s * coeff, v);
            }
                break;
            default: {
                svector<lp::lpvar> vars;
                for (unsigned j = 0; j < num_vars; ++j)
                    vars.push_back(nl2lp[pm.get_var(m, j)]);
                rational s;    
                vars = m_nla_core.reduce_monic_to_rooted(vars, s);
                auto mon = m_nla_core.emons().find_canonical(vars);
                TRACE(nra, tout << "canonical mon: "; if (mon) tout << *mon; else tout << "null"; tout << "\n";);
                
                if (mon) 
                    v = mon->var();                                
                else {
                    NOT_IMPLEMENTED_YET();
                    // this one is for Lev Nachmanson: lar_solver relies on internal variables
                    // to have terms from outside. The solver doesn't get to create
                    // its own monomials. 
                    // v = ...
                    // It is not a use case if the nlsat solver only provides linear
                    // polynomials so punt for now.
                    m_nla_core.add_monic(v, vars.size(), vars.data());
                }
                TRACE(nra,
                      tout << "process_polynomial_check_assignment:"; 
                      tout << " vars="; 
                      for (auto _w : vars) tout << _w << ' '; 
                      tout << " s=" << s
                           << " mon=" << (mon ? static_cast<int>(mon->var()) : -1)
                           << " v=" << v << "\n";);
                t.add_monomial(s * coeff, v);
                break;
            }
            }                      
        }
    }

    u_map<lp::lpvar> reverse_lp2nl() {
        u_map<lp::lpvar> nl2lp;
        for (auto [j, x] : m_lp2nl)
            nl2lp.insert(x, j);
        return nl2lp;
    }
    
    lbool check_assignment() {
        IF_VERBOSE(1, verbose_stream() << "nra::solver::check_assignment\n";);
        setup_solver();
        lbool r = l_undef;
        statistics &st = m_nla_core.lp_settings().stats().m_st;
        nlsat::literal_vector clause;
        polynomial::manager &pm = m_nlsat->pm();
        try {
            nlsat::assignment rvalues(m_nlsat->am());
            for (auto [j, x] : m_lp2nl) {
                scoped_anum a(am());
                am().set(a, m_nla_core.val(j).to_mpq());
                rvalues.set(x, a);
            }
            r = m_nlsat->check(rvalues, clause);
        } 
        catch (z3_exception &) {
            if (m_limit.is_canceled()) {
                r = l_undef;
            } 
            else {
                m_nlsat->collect_statistics(st);
                throw;
            }
        }
        m_nlsat->collect_statistics(st);
        TRACE(nra, m_nlsat->display(tout << r << "\n"); display(tout); tout << "m_lp2nl:\n";
              for (auto [j, x] : m_lp2nl) tout << "j" << j << " := x" << x << "\n";);
        switch (r) {
        case l_true:
            m_nla_core.set_use_nra_model(true);
            lra.init_model();
            validate_constraints();
            m_nla_core.set_use_nra_model(true);
            break;
        case l_false:
            r = add_lemma(clause);
            break;
        default:
            break;
        }
        return r;        
    }

    lbool add_lemma(nlsat::literal_vector const &clause) {
        u_map<lp::lpvar> nl2lp = reverse_lp2nl();
        polynomial::manager &pm = m_nlsat->pm();
        nla::lemma_builder lemma(m_nla_core, __FUNCTION__);
        for (nlsat::literal l : clause) {
            nlsat::atom *a = m_nlsat->bool_var2atom(l.var());
            TRACE(nra, tout << "atom: "; m_nlsat->display(tout, *a); tout << "\n";);
            SASSERT(!a->is_root_atom());
            SASSERT(a->is_ineq_atom());
            auto &ia = *to_ineq_atom(a);
            VERIFY(ia.size() == 1);  // deal with factored polynomials later
            // a is an inequality atom, i.e., p > 0, p < 0, or p = 0.
            polynomial::polynomial const *p = ia.p(0);
            TRACE(nra, tout << "polynomial: "; pm.display(tout, p); tout << "\n";);
            unsigned num_mon = pm.size(p);
            rational bound(0);
            lp::lar_term t;
            process_polynomial_check_assignment(num_mon, p, bound, nl2lp, t);

            // Introduce a single ineq variable and assign it per case; common handling after switch.
            nla::ineq inq(lp::lconstraint_kind::EQ, t, bound);  // initial value overwritten in cases below
            switch (a->get_kind()) {
            case nlsat::atom::EQ:
                inq = nla::ineq(l.sign() ? lp::lconstraint_kind::NE : lp::lconstraint_kind::EQ, t, bound);
                break;
            case nlsat::atom::LT:
                inq = nla::ineq(l.sign() ? lp::lconstraint_kind::GE : lp::lconstraint_kind::LT, t, bound);
                break;
            case nlsat::atom::GT:
                inq = nla::ineq(l.sign() ? lp::lconstraint_kind::LE : lp::lconstraint_kind::GT, t, bound);
                break;
            default:
                UNREACHABLE();
                return l_undef;
            }
            // Ignore a lemma which is satisfied
            if (m_nla_core.ineq_holds(inq))
                return l_undef;
            lemma |= inq;
        }
        IF_VERBOSE(1, verbose_stream() << "linear lemma: " << lemma << "\n");
        return l_false;
    }

    void constraint_core2ex(lp::explanation& ex) {
        vector<nlsat::assumption, false> core;
        m_nlsat->get_core(core);
        for (auto c : core) {
            unsigned idx = static_cast<unsigned>(static_cast<imp*>(c) - this);
            ex.push_back(idx);
            TRACE(nra, lra.display_constraint(tout << "ex: " << idx << ": ", idx) << "\n";);
        }
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
        polynomial::polynomial* ps[1] = { p };
        bool even[1] = { false };
        nlsat::literal lit = m_nlsat->mk_ineq_literal(nlsat::atom::kind::EQ, 1, ps, even);
        m_nlsat->mk_clause(1, &lit, nullptr);
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
            UNREACHABLE(); // unreachable
        }
        m_nlsat->mk_clause(1, &lit, a);
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
        for (unsigned i : m_term_set)
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
            m_nla_core.set_use_nra_model(true);
            lra.init_model();
            if (!check_constraints())
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
            if (!m_term_set.contains(v) && lra.column_has_term(v)) {
                m_term_set.insert(v);
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

    nlsat::anum const& value(lp::lpvar v)  {
        polynomial::var pv;
        if (m_lp2nl.find(v, pv))
            return m_nlsat->value(pv);
        else {
            for (unsigned w = m_values->size(); w <= v; ++w) {
                scoped_anum a(am());
                am().set(a, m_nla_core.val(w).to_mpq());
                m_values->push_back(a);
            }           
            return (*m_values)[v];
        }
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

lbool solver::check_assignment() {
    return m_imp->check_assignment();
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

}
