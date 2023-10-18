/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  Revision History:


  --*/
#pragma once

#include "util/dependency.h"
#include "util/obj_hashtable.h"
#include "util/region.h"
#include "util/rlimit.h"
#include "util/statistics.h"
#include "math/dd/dd_pdd.h"
#include <cstring>

namespace dd {

class solver {
    friend class simplifier;
public:
    class stats {
        unsigned m_simplified;
    public:
        double   m_max_expr_size;
        unsigned m_max_expr_degree;
        unsigned m_superposed;
        unsigned m_compute_steps;
        void reset() { memset(this, 0, sizeof(*this)); }
        stats() { reset(); }
        unsigned simplified() const { return m_simplified; }
        void incr_simplified() {
            m_simplified++;
        }
        
    };

    struct config {
        unsigned m_eqs_threshold = UINT_MAX;
        unsigned m_expr_size_limit = UINT_MAX;
        unsigned m_expr_degree_limit = UINT_MAX;
        unsigned m_max_steps = UINT_MAX;
        unsigned m_max_simplified = UINT_MAX;
        unsigned m_random_seed = 0;
        bool     m_enable_exlin = false;
        unsigned m_eqs_growth = 10;
        unsigned m_expr_size_growth = 10;
        unsigned m_expr_degree_growth = 5;
        unsigned m_number_of_conflicts_to_report = 1;
    };

    enum eq_state {
        solved,
        processed,
        to_simplify
    };

    class equation {
        eq_state                   m_state = to_simplify; 
        unsigned                   m_idx = 0;    //!< unique index
        pdd                        m_poly;       //!< polynomial in pdd form
        u_dependency *             m_dep;        //!< justification for the equality
    public:
        equation(pdd const& p, u_dependency* d): 
            m_poly(p),
            m_dep(d) {                  
        }

        const pdd& poly() const { return m_poly; }        
        u_dependency * dep() const { return m_dep; }
        unsigned idx() const { return m_idx; }
        void operator=(pdd const& p) { m_poly = p; }
        void operator=(u_dependency* d) { m_dep = d; }
        eq_state state() const { return m_state; }
        void set_state(eq_state st) { m_state = st; }
        void set_index(unsigned idx) { m_idx = idx; }
    };

    typedef ptr_vector<equation> equation_vector;

    struct scoped_update {
        equation_vector& set;
        unsigned i = 0;
        unsigned j = 0;
        unsigned sz;
        scoped_update(equation_vector& set) :
            set(set), sz(set.size()) {
        }
        ~scoped_update() {
            for (; i < sz; ++i)
                nextj();
            set.shrink(j);
        }
        equation* get() { return set[i]; }

        void nextj() {
            set[j] = set[i];
            set[i]->set_index(j++);
        }
    };

private:


    typedef std::function<void (u_dependency* d, std::ostream& out)> print_dep_t;

    pdd_manager&                                 m;
    reslimit&                                    m_limit;
    u_dependency_manager&                        m_dep_manager;
    stats                                        m_stats;
    config                                       m_config;
    print_dep_t                                  m_print_dep;
    equation_vector                              m_solved; // equations with solved variables, triangular
    equation_vector                              m_processed;
    equation_vector                              m_to_simplify;
    vector<std::tuple<unsigned, pdd, u_dependency*>> m_subst;
    equation_vector                              m_all_eqs;
    equation*                                    m_conflict = nullptr;   
    bool                                         m_too_complex;
public:
    solver(reslimit& lim, u_dependency_manager& dm, pdd_manager& m);
    ~solver();

    pdd_manager& get_manager() { return m; }

    void set(print_dep_t& pd) { m_print_dep = pd; }
    void set(config const& c) { m_config = c; }
    void adjust_cfg();

    void reset();
    void add(pdd const& p) { add(p, nullptr); }
    void add(pdd const& p, u_dependency * dep);

    void simplify(pdd& p, u_dependency*& dep);
    void add_subst(unsigned v, pdd const& p, u_dependency* dep);

    void simplify();
    void saturate();

    equation_vector const& equations();

    void collect_statistics(statistics & st) const;
    std::ostream& display(std::ostream& out, const equation& eq) const;
    std::ostream& display(std::ostream& out) const;
    std::ostream& display_statistics(std::ostream& out) const;
    const stats& get_stats() const { return m_stats; }
    stats& get_stats() { return m_stats; }
    unsigned number_of_conflicts_to_report() const { return m_config.m_number_of_conflicts_to_report; }

private:
    bool step();
    equation* pick_next();
    bool canceled();
    bool done();
    void superpose(equation const& eq1, equation const& eq2);
    void superpose(equation const& eq);
    void simplify_using(equation& eq, equation_vector const& eqs);
    void simplify_using(equation_vector& set, equation const& eq);
    void simplify_using(equation & dst, equation const& src, bool& changed_leading_term);
    void simplify_using(equation_vector& set, std::function<bool(equation&, bool&)>& simplifier);
    bool try_simplify_using(equation& target, equation const& source, bool& changed_leading_term);

    bool is_trivial(equation const& eq) const { return eq.poly().is_zero(); }    
    bool is_simpler(equation const& eq1, equation const& eq2) { return m.lm_lt(eq1.poly(), eq2.poly()); }
    bool is_conflict(equation const* eq) const { return is_conflict(*eq); }
    bool is_conflict(equation const& eq) const { return eq.poly().is_val() && !is_trivial(eq); }
    bool check_conflict(equation& eq) { return is_conflict(eq) && (set_conflict(eq), true); }    
    void set_conflict(equation& eq) { m_conflict = &eq; push_equation(solved, eq); }
    void set_conflict(equation* eq) { m_conflict = eq; push_equation(solved, eq); }
    bool is_too_complex(const equation& eq) const { return is_too_complex(eq.poly()); }
    bool is_too_complex(const pdd& p) const { return p.tree_size() > m_config.m_expr_size_limit
            || p.degree() > m_config.m_expr_degree_limit;  }

    unsigned                m_levelp1;         // index into level+1
    unsigned_vector         m_level2var;       // level -> var
    unsigned_vector         m_var2level;       // var -> level
    void init_saturate();

    void del_equation(equation& eq) { del_equation(&eq); }    
    void del_equation(equation* eq);    
    equation_vector& get_queue(equation const& eq);
    void retire(equation* eq);
    void pop_equation(equation& eq);
    void pop_equation(equation* eq) { pop_equation(*eq); }
    void push_equation(eq_state st, equation& eq);
    void push_equation(eq_state st, equation* eq) { push_equation(st, *eq); }

    void well_formed();
    void invariant() const;
    struct scoped_process {
        solver& g;
        equation* e;
        void done();
        scoped_process(solver& g, equation* e): g(g), e(e) {}
        ~scoped_process();        
    };

    void update_stats_max_degree_and_size(const equation& e);
};

}
