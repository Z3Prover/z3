/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_anf_simplifier.cpp

  Abstract:
   
    Simplification based on ANF format.

  Author:

    Nikolaj Bjorner 2020-01-02

  --*/

#include "sat/sat_anf_simplifier.h"
#include "sat/sat_solver.h"
#include "sat/sat_xor_util.h"
#include "math/grobner/pdd_solver.h"

namespace sat {


    class pdd_solver : public dd::solver {
    public:
        pdd_solver(reslimit& lim, dd::pdd_manager& m): dd::solver(lim, m) {}
    };
            
    void anf_simplifier::operator()() {
        
        vector<literal_vector> xors;
        clause_vector clauses;
        svector<solver::bin_clause> bins;
        m_relevant.reset();
        m_relevant.resize(s.num_vars(), false);
        for (clause* cp : s.m_clauses) cp->unmark_used();
        collect_xors(xors);
        collect_clauses(clauses, bins);
        
        dd::pdd_manager m(20, dd::pdd_manager::semantics::mod2_e);
        pdd_solver solver(s.rlimit(), m);
        configure_solver(solver);
        
        try {
            for (literal_vector const& x : xors) {
                add_xor(x, solver);
            }
            for (clause* cp : clauses) {
                add_clause(*cp, solver);
            }
            for (auto const& b : bins) {
                add_bin(b, solver);
            }
        }
        catch (dd::pdd_manager::mem_out) {
            IF_VERBOSE(2, verbose_stream() << "(sat.anf memout)\n");
            return;
        }

        TRACE("anf_simplifier", solver.display(tout););

        solver.simplify();

        TRACE("anf_simplifier", solver.display(tout););

        unsigned num_units = 0, num_eq = 0;

        for (auto* e : solver.equations()) {
            auto const& p = e->poly();
            if (p.is_zero()) {
                continue;
            }
            else if (p.is_val()) {
                s.set_conflict();
                break;
            }
            else if (p.is_unary()) {
                // unit
                literal lit(p.var(), p.lo().val().is_zero());
                s.assign_unit(lit);
                ++num_units;
            }
            else if (p.is_binary()) {
                // equivalence
                // x + y + c = 0
                literal x(p.var(), false);
                literal y(p.lo().var(), p.lo().lo().val().is_zero());
                s.mk_clause(x, y, true);
                s.mk_clause(~x, ~y, true);
                ++num_eq;
            }
            // TBD: could learn binary clauses
            // TBD: could try simplify equations using BIG subsumption similar to asymm_branch
        }

        IF_VERBOSE(10, solver.display_statistics(verbose_stream() << "(sat.anf\n" ) 
                   << "\n"
                   << " :num-unit " << num_units 
                   << " :num-eq "   << num_eq 
                   << " :num-xor "  << xors.size() 
                   << " :num-cls "  << clauses.size() 
                   << " :num-bin "  << bins.size()
                   << ")\n");
    }

    void anf_simplifier::collect_clauses(clause_vector & clauses, svector<solver::bin_clause>& bins) {
        clause_vector oclauses;
        for (clause* cp : s.clauses()) {
            clause const& c = *cp;
            if (c.was_used() || is_too_large(c)) 
                continue;
            else if (is_pre_satisfied(c)) {
                oclauses.push_back(cp);
            }
            else {
                clauses.push_back(cp);
            }
        }
        svector<solver::bin_clause> obins;
        s.collect_bin_clauses(obins, false, false);
        unsigned j = 0;
        for (auto const& b : obins) {
            if (is_pre_satisfied(b)) {
                obins[j++] = b;
            }
            else {
                bins.push_back(b);
            }
        }
        obins.shrink(j);

        while (bins.size() + clauses.size() < m_config.m_max_clauses) {

            for (auto const& b : bins) set_relevant(b);
            for (clause* cp : clauses) set_relevant(*cp);
    
            j = 0;
            for (auto const& b : obins) {
                if (has_relevant_var(b)) {
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
                clause& c = *cp;
                if (has_relevant_var(c)) {
                    clauses.push_back(cp);
                }
                else {
                    oclauses.push_back(cp);
                }
            }
            oclauses.shrink(j);
        }
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

    void anf_simplifier::collect_xors(vector<literal_vector>& xors) {
        std::function<void(literal_vector const&, bool)> f =
            [&](literal_vector const& l, bool) { xors.push_back(l); };

        xor_util xu(s);
        xu.set(f);
        xu.extract_xors();
        for (clause* cp : s.m_clauses) cp->unmark_used();
        for (clause* cp : s.m_learned) cp->unmark_used();
        for (clause* cp : xu.removed_clauses()) cp->mark_used();
    }

    void anf_simplifier::configure_solver(pdd_solver& ps) {
        // assign levels to variables. 
        // use s.def_level as a primary source for the level of a variable.
        // secondarily, sort variables randomly (each variable is assigned
        // a random, unique, id).
        unsigned nv = s.num_vars();
        unsigned_vector l2v(nv), var2id(nv), id2var(nv);
        svector<std::pair<unsigned, unsigned>> vl(nv);

        for (unsigned i = 0; i < nv; ++i) var2id[i] = i;
        shuffle(var2id.size(), var2id.c_ptr(), s.rand());
        for (unsigned i = 0; i < nv; ++i) id2var[var2id[i]] = i;
        for (unsigned i = 0; i < nv; ++i) vl[i] = std::make_pair(s.def_level(i), var2id[i]);
        std::sort(vl.begin(), vl.end());
        for (unsigned i = 0; i < nv; ++i) l2v[i] = id2var[vl[i].second];

        ps.get_manager().reset(l2v);

        // set configuration parameters.
        dd::solver::config cfg;
        cfg.m_expr_size_limit = 1000;
        cfg.m_max_steps = 1000;
        cfg.m_random_seed = s.rand()();
        cfg.m_enable_exlin = true;

        unsigned max_num_nodes = 1 << 18;
        ps.get_manager().set_max_num_nodes(max_num_nodes);
        ps.set(cfg);
    }

    void anf_simplifier::add_bin(solver::bin_clause const& b, pdd_solver& ps) {
        auto& m = ps.get_manager();
        auto v = m.mk_var(b.first.var());
        auto w = m.mk_var(b.second.var());
        if (b.first.sign()) v = ~v;
        if (b.second.sign()) w = ~w;        
        dd::pdd p = v | w;
        ps.add(p);
    }

    void anf_simplifier::add_clause(clause const& c, pdd_solver& ps) {
        auto& m = ps.get_manager();
        dd::pdd p = m.zero();
        for (literal l : c) {
            auto v = m.mk_var(l.var());
            if (l.sign()) v = ~v;
            p |= v;
        }
        ps.add(p);
    }

    void anf_simplifier::add_xor(literal_vector const& x, pdd_solver& ps) {
        auto& m = ps.get_manager();
        dd::pdd p = m.zero();
        for (literal l : x) {
            auto v = m.mk_var(l.var());
            if (l.sign()) v = ~v;
            p ^= v;
        }
        ps.add(p);
    }

}
