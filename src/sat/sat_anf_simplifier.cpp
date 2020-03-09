/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_anf_simplifier.cpp

  Abstract:
   
    Simplification based on ANF format.

  Author:

    Nikolaj Bjorner 2020-01-02

  --*/

#include "util/union_find.h"
#include "sat/sat_anf_simplifier.h"
#include "sat/sat_solver.h"
#include "sat/sat_elim_eqs.h"
#include "sat/sat_xor_finder.h"
#include "sat/sat_aig_finder.h"
#include "math/grobner/pdd_solver.h"

namespace sat {

    struct anf_simplifier::report {
        anf_simplifier& s;
        stopwatch       m_watch;
        report(anf_simplifier& s): s(s) { m_watch.start(); }
        ~report() {
            m_watch.stop();
            IF_VERBOSE(2, 
                       verbose_stream() << " (sat.anf.simplifier" 
                       << " :num-units " << s.m_stats.m_num_units 
                       << " :num-eqs " << s.m_stats.m_num_eqs 
                       << " :mb " << mem_stat() 
                       << m_watch << ")\n");
        }
    };
            
    void anf_simplifier::operator()() {
        dd::pdd_manager m(20, dd::pdd_manager::semantics::mod2_e);
        pdd_solver solver(s.rlimit(), m);
        report _report(*this);
        configure_solver(solver);
        clauses2anf(solver);
        TRACE("anf_simplifier", solver.display(tout); s.display(tout););
        solver.simplify();
        TRACE("anf_simplifier", solver.display(tout););
        anf2clauses(solver);
        anf2phase(solver);
        save_statistics(solver);
        IF_VERBOSE(10, m_st.display(verbose_stream() << "(sat.anf.simplifier\n"); verbose_stream() << ")\n");
    }

    /**
       \brief extract learned units and equivalences from processed anf.

       TBD: could learn binary clauses
       TBD: could try simplify equations using BIG subsumption similar to asymm_branch
     */
    void anf_simplifier::anf2clauses(pdd_solver& solver) {

        union_find_default_ctx ctx;
        union_find<> uf(ctx);
        for (unsigned i = 2*s.num_vars(); i--> 0; ) uf.mk_var();
        auto add_eq = [&](literal l1, literal l2) {
            uf.merge(l1.index(), l2.index());
            uf.merge((~l1).index(), (~l2).index());
        };

        unsigned old_num_eqs = m_stats.m_num_eqs;
        for (auto* e : solver.equations()) {
            auto const& p = e->poly();
            if (p.is_one()) {
                s.set_conflict();
                break;
            }
            else if (p.is_unary()) {
                // unit
                SASSERT(!p.is_val() && p.lo().is_val() && p.hi().is_val());
                literal lit(p.var(), p.lo().is_zero());
                s.assign_unit(lit);
                ++m_stats.m_num_units;
                TRACE("anf_simplifier", tout << "unit " << p << " : " << lit << "\n";);
            }
            else if (p.is_binary()) {
                // equivalence
                // x + y + c = 0
                SASSERT(!p.is_val() && p.hi().is_one() && !p.lo().is_val() && p.lo().hi().is_one() && p.lo().lo().is_val());
                literal x(p.var(), false);
                literal y(p.lo().var(), p.lo().lo().is_one());
                add_eq(x, y);
                ++m_stats.m_num_eqs;
                TRACE("anf_simplifier", tout << "equivalence " << p << " : " << x << " == " << y << "\n";);
            }
        }

        if (old_num_eqs < m_stats.m_num_eqs) {
            elim_eqs elim(s);
            elim(uf);
        }
    }

    /**
       \brief update best phase using solved equations
       polynomials that are not satisfied evaluate to true.
       In a satisfying assignment, all polynomials should evaluate to false.
       assume that solutions are provided in reverse order.

       As a simplifying assumption it relies on the property
       that if an equation is of the form v + p, where v does not occur in p,
       then all equations that come after it do not contain p.
       In this way we can flip the assignment to v without 
       invalidating the evaluation cache.
     */
    void anf_simplifier::anf2phase(pdd_solver& solver) {
        if (!m_config.m_anf2phase) 
            return;
        reset_eval();
        auto const& eqs = solver.equations();
        for (unsigned i = eqs.size(); i-- > 0; ) {
            dd::pdd const& p = eqs[i]->poly();
            if (!p.is_val() && p.hi().is_one() && s.m_best_phase[p.var()] != eval(p.lo())) {
                s.m_best_phase[p.var()] = !s.m_best_phase[p.var()];
                ++m_stats.m_num_phase_flips;
            }
        }
    }

    bool anf_simplifier::eval(dd::pdd const& p) {
        if (p.is_one()) return true;
        if (p.is_zero()) return false;
        unsigned index = p.index();
        if (index < m_eval_cache.size()) {
            if (m_eval_cache[index] == m_eval_ts) return false;
            if (m_eval_cache[index] == m_eval_ts + 1) return true;
        }
        SASSERT(!p.is_val());
        bool hi = eval(p.hi());
        bool lo = eval(p.lo());
        bool v = (hi && s.m_best_phase[p.var()]) ^ lo;
        m_eval_cache.reserve(index + 1, 0);
        m_eval_cache[index] = m_eval_ts + v;
        return v;
    }

    void anf_simplifier::reset_eval() {
        if (m_eval_ts + 2 < m_eval_ts) {
            m_eval_cache.reset();
            m_eval_ts = 0;
        }
        m_eval_ts += 2;
    }

    void anf_simplifier::clauses2anf(pdd_solver& solver) {
        svector<solver::bin_clause> bins;
        m_relevant.reset();
        m_relevant.resize(s.num_vars(), false);
        clause_vector clauses(s.clauses());
        s.collect_bin_clauses(bins, false, false);
        collect_clauses(clauses, bins);
        try {
            compile_xors(clauses, solver);
            compile_aigs(clauses, bins, solver);

            for (auto const& b : bins) {
                add_bin(b, solver);
            }                
            for (clause* cp : clauses) {
                add_clause(*cp, solver);
            }
        }
        catch (dd::pdd_manager::mem_out) {
            IF_VERBOSE(1, verbose_stream() << "(sat.anf memout)\n");
        }
    }

    void anf_simplifier::collect_clauses(clause_vector & clauses, svector<solver::bin_clause>& bins) {
        clause_vector oclauses;
        svector<solver::bin_clause> obins;

        unsigned j = 0;
        for (clause* cp : clauses) {
            clause const& c = *cp;
            if (is_too_large(c)) 
                continue;
            else if (is_pre_satisfied(c)) {
                oclauses.push_back(cp);
            }
            else {
                clauses[j++] = cp;
            }
        }
        clauses.shrink(j);

        j = 0;
        for (auto const& b : bins) {
            if (is_pre_satisfied(b)) {
                obins.push_back(b);
            }
            else {
                bins[j++] = b;
            }
        }
        bins.shrink(j);

        unsigned rounds = 0, max_rounds = 3;
        bool added = true;
        while (bins.size() + clauses.size() < m_config.m_max_clauses &&
               (!obins.empty() || !oclauses.empty()) &&
               added &&
               rounds < max_rounds) {

            added = false;
            for (auto const& b : bins) set_relevant(b);
            for (clause* cp : clauses) set_relevant(*cp);
    
            j = 0;
            for (auto const& b : obins) {
                if (has_relevant_var(b)) {
                    added = true;
                    bins.push_back(b);
                }
                else {
                    obins[j++] = b;
                }
            }
            obins.shrink(j);

            if (bins.size() + clauses.size() >= m_config.m_max_clauses) {
                break;
            }
            
            j = 0;
            for (clause* cp : oclauses) {
                if (has_relevant_var(*cp)) {
                    added = true;
                    clauses.push_back(cp);
                }
                else {
                    oclauses[j++] = cp;
                }
            }
            oclauses.shrink(j);
        }

        TRACE("anf_simplifier", 
              tout << "kept:\n";
              for (clause* cp : clauses) tout << *cp << "\n";
              for (auto b : bins) tout << b.first << " " << b.second << "\n";
              tout << "removed:\n";
              for (clause* cp : oclauses) tout << *cp << "\n";
              for (auto b : obins) tout << b.first << " " << b.second << "\n";);
    }

    void anf_simplifier::set_relevant(solver::bin_clause const& b) {
        set_relevant(b.first); 
        set_relevant(b.second);
    }

    void anf_simplifier::set_relevant(clause const& c) {
        for (literal l : c) set_relevant(l);
    }

    bool anf_simplifier::is_pre_satisfied(clause const& c) {
        for (literal l : c) if (phase_is_true(l)) return true;
        return false;
    }

    bool anf_simplifier::is_pre_satisfied(solver::bin_clause const& b) {
        return phase_is_true(b.first) || phase_is_true(b.second);
    }
    
    bool anf_simplifier::phase_is_true(literal l) {
        bool ph = (s.m_best_phase_size > 0) ? s.m_best_phase[l.var()] : s.m_phase[l.var()];
        return l.sign() ? !ph : ph;
    }

    bool anf_simplifier::has_relevant_var(clause const& c) {
        for (literal l : c) if (is_relevant(l)) return true;
        return false;
    }

    bool anf_simplifier::has_relevant_var(solver::bin_clause const& b) {
        return is_relevant(b.first) || is_relevant(b.second);
    }

    /**
       \brief extract xors from all s.clauses() 
       (could be just filtered clauses, or clauses with relevant variables).
       Add the extracted xors to pdd_solver.
       Remove clauses from list that correspond to extracted xors
     */
    void anf_simplifier::compile_xors(clause_vector& clauses, pdd_solver& ps) {
        if (!m_config.m_compile_xor) {
            return;
        }
        std::function<void(literal_vector const&)> f =
            [&,this](literal_vector const& x) { 
            add_xor(x, ps);
            m_stats.m_num_xors++;
        };
        xor_finder xf(s);
        xf.set(f);
        xf(clauses); 
    }

    static solver::bin_clause normalize(solver::bin_clause const& b) {
        if (b.first.index() > b.second.index()) {
            return solver::bin_clause(b.second, b.first);
        }
        else {
            return b;
        }
    }
    /**
       \brief extract AIGs from clauses.
       Add the extracted AIGs to pdd_solver.
       Remove clauses from list that correspond to extracted AIGs
       Remove binary clauses that correspond to extracted AIGs.       
     */
    void anf_simplifier::compile_aigs(clause_vector& clauses, svector<solver::bin_clause>& bins, pdd_solver& ps) {
        if (!m_config.m_compile_aig) {
            return;
        }
        hashtable<solver::bin_clause, solver::bin_clause_hash, default_eq<solver::bin_clause>> seen_bin;

        std::function<void(literal head, literal_vector const& tail)> on_aig =
            [&,this](literal head, literal_vector const& tail) {
            add_aig(head, tail, ps);
            for (literal l : tail) {                
                seen_bin.insert(normalize(solver::bin_clause(~l, head)));
            }
            m_stats.m_num_aigs++;
        };
        std::function<void(literal head, literal c, literal th, literal el)> on_if = 
            [&,this](literal head, literal c, literal th, literal el) {
            add_if(head, c, th, el, ps);
            m_stats.m_num_ifs++;
        };
        aig_finder af(s);
        af.set(on_aig);
        af.set(on_if);
        af(clauses);

        std::function<bool(solver::bin_clause b)> not_seen = 
            [&](solver::bin_clause b) { return !seen_bin.contains(normalize(b)); };
        bins.filter_update(not_seen);
    }

    /**
       assign levels to variables. 
       use variable id as a primary source for the level of a variable.
       secondarily, sort variables randomly (each variable is assigned
       a random, unique, id).
    */
    void anf_simplifier::configure_solver(pdd_solver& ps) {
        unsigned nv = s.num_vars();
        unsigned_vector l2v(nv), var2id(nv), id2var(nv);
        svector<std::pair<unsigned, unsigned>> vl(nv);

        for (unsigned i = 0; i < nv; ++i) var2id[i] = i;
        shuffle(var2id.size(), var2id.c_ptr(), s.rand());
        for (unsigned i = 0; i < nv; ++i) id2var[var2id[i]] = i;
        for (unsigned i = 0; i < nv; ++i) vl[i] = std::make_pair(i, var2id[i]);
        std::sort(vl.begin(), vl.end());
        for (unsigned i = 0; i < nv; ++i) l2v[i] = id2var[vl[i].second];

        ps.get_manager().reset(l2v);

        // set configuration parameters.
        dd::solver::config cfg;
        cfg.m_expr_size_limit = 1000;
        cfg.m_max_steps = 1000;
        cfg.m_random_seed = s.rand()();
        cfg.m_enable_exlin = m_config.m_enable_exlin;

        unsigned max_num_nodes = 1 << 18;
        ps.get_manager().set_max_num_nodes(max_num_nodes);
        ps.set(cfg);
    }

#define lit2pdd(_l_) (_l_.sign() ? ~m.mk_var(_l_.var()) : m.mk_var(_l_.var()))

    void anf_simplifier::add_bin(solver::bin_clause const& b, pdd_solver& ps) {
        auto& m = ps.get_manager();
        dd::pdd p = (lit2pdd(b.first) | lit2pdd(b.second)) ^ true;
        ps.add(p);
        TRACE("anf_simplifier", tout << "bin: " << b.first << " " << b.second << " : " << p << "\n";);
    }

    void anf_simplifier::add_clause(clause const& c, pdd_solver& ps) {
        if (c.size() > m_config.m_max_clause_size) return;
        auto& m = ps.get_manager();
        dd::pdd p = m.zero();
        for (literal l : c) p |= lit2pdd(l);
        p = p ^ true;
        ps.add(p);
        TRACE("anf_simplifier", tout << "clause: " << c << " : " << p << "\n";);
    }

    void anf_simplifier::add_xor(literal_vector const& x, pdd_solver& ps) {
        auto& m = ps.get_manager();
        dd::pdd p = m.one();
        for (literal l : x) p ^= lit2pdd(l);
        ps.add(p);
        TRACE("anf_simplifier", tout << "xor: " << x << " : " << p << "\n";);
    }

    void anf_simplifier::add_aig(literal head, literal_vector const& ands, pdd_solver& ps) {
        auto& m = ps.get_manager();
        dd::pdd q = m.one();
        for (literal l : ands) q &= lit2pdd(l);
        dd::pdd p = lit2pdd(head) ^ q;
        ps.add(p);
        TRACE("anf_simplifier", tout << "aig: " << head << " == " << ands << " poly : " << p << "\n";);
    }

    void anf_simplifier::add_if(literal head, literal c, literal th, literal el, pdd_solver& ps) {
        auto& m = ps.get_manager();
        dd::pdd cond = lit2pdd(c);
        dd::pdd p = lit2pdd(head) ^ (cond & lit2pdd(th)) ^ (~cond & lit2pdd(el));        
        ps.add(p);
        TRACE("anf_simplifier", tout << "ite: " << head << " == " << c << "?" << th << ":" << el << " poly : " << p << "\n";);
    }

    void anf_simplifier::save_statistics(pdd_solver& solver) {
        solver.collect_statistics(m_st);
        m_st.update("sat-anf.units", m_stats.m_num_units);
        m_st.update("sat-anf.eqs",   m_stats.m_num_eqs);
        m_st.update("sat-anf.ands",  m_stats.m_num_aigs);
        m_st.update("sat-anf.ites",  m_stats.m_num_ifs);
        m_st.update("sat-anf.xors",  m_stats.m_num_xors);
        m_st.update("sat-anf.phase_flips", m_stats.m_num_phase_flips);
    }

}
