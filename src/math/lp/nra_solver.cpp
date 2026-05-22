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
#include "nlsat/nlsat_assignment.h"
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
    svector<lp::constraint_index> m_literal2constraint;
    struct eq {
        bool operator()(unsigned_vector const &a, unsigned_vector const &b) const {
            return a == b;
        }
    };
    map<unsigned_vector, unsigned, svector_hash<unsigned_hash>, eq> m_vars2mon;
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

    // Create polynomial definition for variable v used in setup_solver_poly.
    // The definition recursively expands monic and term variables into
    // polynomials in leaf variables, scaled by an integer denominator
    // tracked in `denominators` to keep the coefficients integral.
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

        statistics& st = m_nla_core.lp_settings().stats().m_st;
        lbool r = m_nlsat->check();

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

    // LRA model value with monic and term substitution, mirroring the
    // de-linearized representation that mk_definition builds for NLSAT.
    // For a monic m = v1*...*vk we return product of lra-values of vi
    // (not lra.val(m), which may differ when m is being refined).
    rational substituted_val(lp::lpvar v, u_map<rational>& cache) {
        rational r;
        if (cache.find(v, r))
            return r;
        if (m_nla_core.emons().is_monic_var(v)) {
            r = rational::one();
            for (auto w : m_nla_core.emons()[v].vars())
                r *= substituted_val(w, cache);
        }
        else if (lra.column_has_term(v)) {
            r = rational::zero();
            for (auto const& [w, coeff] : lra.get_term(v))
                r += coeff * substituted_val(w, cache);
        }
        else {
            r = m_nla_core.val(v);
        }
        cache.insert(v, r);
        return r;
    }

    // Evaluate constraint ci at the LRA model after substituting monics
    // and terms. Returns true iff the constraint holds.
    bool lra_holds_substituted(lp::constraint_index ci, u_map<rational>& cache) {
        auto& c = lra.constraints()[ci];
        rational lhs(0);
        for (auto [coeff, v] : c.coeffs())
            lhs += coeff * substituted_val(v, cache);
        rational const& rhs = c.rhs();
        switch (c.kind()) {
        case lp::lconstraint_kind::LE: return lhs <= rhs;
        case lp::lconstraint_kind::GE: return lhs >= rhs;
        case lp::lconstraint_kind::LT: return lhs < rhs;
        case lp::lconstraint_kind::GT: return lhs > rhs;
        case lp::lconstraint_kind::EQ: return lhs == rhs;
        default: UNREACHABLE();
        }
        return true;
    }

    // BFS the set of LRA variables transitively reachable from constraint
    // ci through monic factors and term components. These are exactly the
    // variables that the substituted polynomial of ci will reference.
    void collect_needed_vars(lp::constraint_index ci, indexed_uint_set& needed) {
        svector<unsigned> todo;
        auto& c = lra.constraints()[ci];
        for (auto [coeff, v] : c.coeffs())
            todo.push_back(v);
        for (unsigned i = 0; i < todo.size(); ++i) {
            unsigned v = todo[i];
            if (needed.contains(v))
                continue;
            needed.insert(v);
            if (m_nla_core.emons().is_monic_var(v)) {
                for (auto w : m_nla_core.emons()[v].vars())
                    todo.push_back(w);
            }
            else if (lra.column_has_term(v)) {
                for (auto const& [w, coeff] : lra.get_term(v))
                    todo.push_back(w);
            }
        }
    }

    // Cheap LRA-side proxy for "degree of the substituted polynomial in
    // its max variable". For a leaf the expansion size is 1; for a monic
    // it is the (recursive) sum over factors. For a constraint we take
    // the max over the lhs terms, since the polynomial is a sum of those
    // monomials. Smaller values are preferred to mimic the lowest-degree
    // heuristic in nlsat_solver::check(rvalues, clause).
    unsigned var_expansion_size(lp::lpvar v) {
        if (m_nla_core.emons().is_monic_var(v)) {
            unsigned s = 0;
            for (auto w : m_nla_core.emons()[v].vars())
                s += var_expansion_size(w);
            return s;
        }
        return 1;
    }

    unsigned constraint_expansion_size(lp::constraint_index ci) {
        auto& c = lra.constraints()[ci];
        unsigned best = 1;
        for (auto [coeff, v] : c.coeffs()) {
            unsigned d = var_expansion_size(v);
            if (d > best)
                best = d;
        }
        return best;
    }

    void process_polynomial_check_assignment(polynomial::polynomial const* p, rational& bound, const u_map<lp::lpvar>& nl2lp, lp::lar_term& t) {
        polynomial::manager& pm = m_nlsat->pm();       
        for (unsigned i = 0; i < pm.size(p); ++i) {
            polynomial::monomial* m = pm.get_monomial(p, i);
            auto& coeff = pm.coeff(p, i);
                 
            unsigned num_vars = pm.size(m);
            // add mon * coeff to t;
            switch (num_vars) {                            
            case 0:
                bound -= coeff;
                break;
            case 1: {
                auto v = nl2lp[pm.get_var(m, 0)];
                t.add_monomial(coeff, v);
                break;
            }
            default: {
                svector<lp::lpvar> vars;
                for (unsigned j = 0; j < num_vars; ++j)
                    vars.push_back(nl2lp[pm.get_var(m, j)]);
                std::sort(vars.begin(), vars.end());
                lp::lpvar v;
                if (m_vars2mon.contains(vars)) 
                   v = m_vars2mon[vars];
                else 
                   v = m_nla_core.add_mul_def(vars.size(), vars.data());  
                t.add_monomial(coeff, v);
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
        SASSERT(need_check());
        reset();
        m_literal2constraint.reset();
        m_vars2mon.reset();
        m_coi.init();

        statistics &st = m_nla_core.lp_settings().stats().m_st;

        // Sort COI constraints by ascending substitution-expansion size
        // (a structural, model-independent measure that acts as a cheap
        // LRA-side proxy for the lowest-degree-in-max-var heuristic of
        // nlsat::solver::check(rvalues, clause)). The first falsified
        // constraint we hit therefore has the minimum expansion size
        // among all falsified candidates. Cache the expansion size for
        // each constraint up front so the comparator is O(1).
        svector<lp::constraint_index> coi_constraints;
        for (auto ci : m_coi.constraints())
            coi_constraints.push_back(ci);

        u_map<unsigned> expansion_size_cache;
        for (auto ci : coi_constraints)
            expansion_size_cache.insert(ci, constraint_expansion_size(ci));

        std::stable_sort(coi_constraints.begin(), coi_constraints.end(),
                         [&](lp::constraint_index a, lp::constraint_index b) {
                             return expansion_size_cache[a] < expansion_size_cache[b];
                         });

        u_map<rational> sub_cache;
        lp::constraint_index best = lp::null_ci;
        for (auto ci : coi_constraints) {
            if (!lra_holds_substituted(ci, sub_cache)) {
                best = ci;
                break;
            }
        }

        if (best == lp::null_ci)
            return l_undef;

        // Determine the LRA variables transitively referenced by the
        // chosen constraint, then create only those NLSAT variables and
        // polynomial definitions. No wasted definitions reach NLSAT.
        indexed_uint_set needed;
        collect_needed_vars(best, needed);

        auto &pm = m_nlsat->pm();
        polynomial_ref_vector definitions(pm);
        vector<rational> denominators;

        // Process vars in index order (topological). For needed leaves we
        // allocate an NLSAT variable and let mk_definition push the leaf
        // polynomial; for needed monics/terms mk_definition pushes the
        // expanded form using the already-populated entries of its
        // factors/components. Non-needed slots are filled with placeholders
        // so that definitions[v] / denominators[v] remain index-aligned.
        for (unsigned v = 0; v < lra.number_of_vars(); ++v) {
            if (!needed.contains(v)) {
                definitions.push_back(nullptr);
                denominators.push_back(rational(0));
                continue;
            }
            if (!m_nla_core.emons().is_monic_var(v) && !lra.column_has_term(v)) {
                auto j = m_nlsat->mk_var(lra.var_is_int(v));
                m_lp2nl.insert(v, j);
            }
            mk_definition(v, definitions, denominators);
        }

        // Populate m_vars2mon for every existing monic so that products
        // produced by NLSAT's projection are recognized by add_lemma
        // rather than being recreated through add_mul_def. Storage is
        // negligible compared to the original per-monic clause work.
        for (auto const& m : m_nla_core.emons()) {
            auto vars = m.vars();
            std::sort(vars.begin(), vars.end());
            m_vars2mon.insert(vars, m.var());
        }

        // Build the substituted polynomial for the chosen constraint and
        // register it as the single unit clause in NLSAT. The literal is
        // wired to its source LRA constraint via m_literal2constraint so
        // add_lemma can use the original explanation when it appears in
        // the produced clause.
        auto &c = lra.constraints()[best];
        auto k = c.kind();
        auto rhs = c.rhs();
        auto lhs = c.coeffs();
        rational den = denominator(rhs);
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
        auto lit = add_constraint(p, best, k);
        m_literal2constraint.setx(lit.index(), best, lp::null_ci);
        definitions.reset();

        // Seed the NLSAT assignment for the variables we registered
        // (only leaves transitively reached from the chosen constraint).
        nlsat::assignment rvalues(am());
        for (auto [j, x] : m_lp2nl) {
            scoped_anum a(am());
            am().set(a, m_nla_core.val(j).to_mpq());
            rvalues.set(x, a);
        }

        nlsat::literal_vector clause;
        lbool r = m_nlsat->check(rvalues, clause);
        m_nlsat->collect_statistics(st);

        if (r == l_false)
            return add_lemma(clause);
        // The chosen constraint is falsified in the substituted LRA model,
        // so NLSAT should also report l_false; any other outcome (l_true
        // or l_undef) means we cannot derive a useful lemma here.
        return l_undef;
    }

    lbool add_lemma(nlsat::literal_vector const &clause) {
        u_map<lp::lpvar> nl2lp = reverse_lp2nl();
        lbool result = l_false;
        {
            nla::lemma_builder lemma(m_nla_core, __FUNCTION__);
            for (nlsat::literal l : clause) {
                if (m_literal2constraint.get((~l).index(), lp::null_ci) != lp::null_ci) {
                    auto ci = m_literal2constraint[(~l).index()];
                    lp::explanation ex;
                    ex.push_back(ci);
                    lemma &= ex;
                    continue;
                }
                nlsat::atom *a = m_nlsat->bool_var2atom(l.var());
                if (a->is_root_atom()) {
                    result = l_undef;
                    break;
                }
                SASSERT(a->is_ineq_atom());
                auto &ia = *to_ineq_atom(a);
                if (ia.size() != 1) {
                    result = l_undef; // factored polynomials not handled here
                    break;
                }
                polynomial::polynomial const *p = ia.p(0);
                rational bound(0);
                lp::lar_term t;
                process_polynomial_check_assignment(p, bound, nl2lp, t);

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
                    result = l_undef;
                    break;
                }
                if (result == l_undef)
                    break;
                if (m_nla_core.ineq_holds(inq)) {
                    result = l_undef;
                    break;
                }
                lemma |= inq;
            }
            if (result == l_false)
                this->m_nla_core.m_check_feasible = true;
        } // lemma_builder destructor runs here
        if (result == l_undef)
            m_nla_core.m_lemmas.pop_back(); // discard incomplete lemma
        return result;
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
        
        lbool r = m_nlsat->check();
        statistics &st = m_nla_core.lp_settings().stats().m_st;
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
        
        
        lbool r = m_nlsat->check();

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
    try {
        return m_imp->check();
    } 
    catch (z3_exception &) {
        statistics &st = m_imp->m_nla_core.lp_settings().stats().m_st;
        m_imp->m_nlsat->collect_statistics(st);
        if (m_imp->m_limit.is_canceled()) {
            return l_undef;
        }
        else {
            throw;
        }
    }
}

lbool solver::check(vector<dd::pdd> const& eqs) {
    try {
        return m_imp->check(eqs);
    } 
    catch (z3_exception &) {
        statistics &st = m_imp->m_nla_core.lp_settings().stats().m_st;
        m_imp->m_nlsat->collect_statistics(st);
        if (m_imp->m_limit.is_canceled()) {
            return l_undef;
        }
        else {
            throw;
        }
    }
}

lbool solver::check(dd::solver::equation_vector const& eqs) {
    try {
        return m_imp->check(eqs);
    } 
    catch (z3_exception &) {
        statistics &st = m_imp->m_nla_core.lp_settings().stats().m_st;
        m_imp->m_nlsat->collect_statistics(st);
        if (m_imp->m_limit.is_canceled()) {
            return l_undef;
        }
        else {
            throw;
        }
    }
}

lbool solver::check_assignment() {
    try {
        return m_imp->check_assignment();
    } 
    catch (z3_exception &) {
        statistics &st = m_imp->m_nla_core.lp_settings().stats().m_st;
        m_imp->m_nlsat->collect_statistics(st);
        IF_VERBOSE(0, verbose_stream() << "check-assignment\n");
        if (m_imp->m_limit.is_canceled()) {
            return l_undef;
        }
        else {
            throw;
        }
    }
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
