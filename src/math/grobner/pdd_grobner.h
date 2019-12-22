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

namespace dd {

class grobner {
public:
    struct stats {
        unsigned m_simplified;
        double   m_max_expr_size;
        unsigned m_max_expr_degree;
        unsigned m_superposed;
        unsigned m_compute_steps;
        void reset() { memset(this, 0, sizeof(*this)); }
        stats() { reset(); }
    };

    struct config {
        unsigned m_eqs_threshold;
        unsigned m_expr_size_limit;
        enum { basic, tuned } m_algorithm;
        config() :
            m_eqs_threshold(UINT_MAX),
            m_expr_size_limit(UINT_MAX),
            m_algorithm(basic)
        {}
    };

    class equation {
        bool                       m_processed;  //!< state
        unsigned                   m_idx;        //!< unique index
        pdd                        m_poly;       //!< polynomial in pdd form
        u_dependency *             m_dep;        //!< justification for the equality
    public:
        equation(pdd const& p, u_dependency* d, unsigned idx): 
            m_processed(false),
            m_idx(idx),
            m_poly(p),
            m_dep(d)
        {}

        const pdd& poly() const { return m_poly; }        
        u_dependency * dep() const { return m_dep; }
        unsigned idx() const { return m_idx; }
        void operator=(pdd& p) { m_poly = p; }
        void operator=(u_dependency* d) { m_dep = d; }
        bool is_processed() const { return m_processed; }
        void set_processed(bool p) { m_processed = p; }
        void set_index(unsigned idx) { m_idx = idx; }
    };
private:

    typedef ptr_vector<equation> equation_vector;
    typedef std::function<void (u_dependency* d, std::ostream& out)> print_dep_t;

    pdd_manager&                                 m;
    reslimit&                                    m_limit;
    stats                                        m_stats;
    config                                       m_config;
    print_dep_t                                  m_print_dep;
    equation_vector                              m_processed;
    equation_vector                              m_to_simplify;
    mutable u_dependency_manager                 m_dep_manager;
    equation_vector                              m_all_eqs;
    equation const*                              m_conflict;   
public:
    grobner(reslimit& lim, pdd_manager& m);
    ~grobner();

    void operator=(print_dep_t& pd) { m_print_dep = pd; }
    void operator=(config const& c) { m_config = c; }

    void reset();
    void add(pdd const& p) { add(p, nullptr); }
    void add(pdd const& p, u_dependency * dep);

    void saturate();

    equation_vector const& equations();
    u_dependency_manager& dep() const { return m_dep_manager;  }

    void collect_statistics(statistics & st) const;
    std::ostream& display(std::ostream& out, const equation& eq) const;
    std::ostream& display(std::ostream& out) const;

private:
    bool step();
    bool basic_step();
    equation* pick_next();
    bool canceled();
    bool done();
    bool superpose(equation const& eq1, equation const& eq2);
    void superpose(equation const& eq);
    bool simplify_source_target(equation const& source, equation& target, bool& changed_leading_term);
    bool simplify_using(equation_vector& set, equation const& eq);
    bool simplify_using(equation& eq, equation_vector const& eqs);

    bool eliminate(equation& eq) { return is_trivial(eq) && (del_equation(eq), true); }
    bool is_trivial(equation const& eq) const { return eq.poly().is_zero(); }    
    bool is_simpler(equation const& eq1, equation const& eq2) { return eq1.poly() < eq2.poly(); }
    bool check_conflict(equation const& eq) { return eq.poly().is_val() && !is_trivial(eq) && (set_conflict(eq), true); }    
    void set_conflict(equation const& eq) { m_conflict = &eq; }
    bool is_too_complex(const equation& eq) const { return is_too_complex(eq.poly()); }
    bool is_too_complex(const pdd& p) const { return p.tree_size() > m_config.m_expr_size_limit;  }


    // tuned implementation
    vector<equation_vector> m_watch;           // watch list mapping variables to vector of equations where they occur (generally a subset)
    unsigned                m_levelp1;         // index into level+1
    unsigned_vector         m_level2var;       // level -> var
    unsigned_vector         m_var2level;       // var -> level

    bool tuned_step();
    void tuned_init();
    equation* tuned_pick_next();
    bool simplify_to_simplify(equation const& eq);
    void add_to_watch(equation& eq);

    void del_equation(equation& eq);    
    void retire(equation* eq) {
        dealloc(eq);
    }
    void pop_equation(unsigned idx, equation_vector& v);
    void push_equation(equation& eq, equation_vector& v);

    void invariant() const;
    struct scoped_detach {
        grobner& g;
        equation* e;
        scoped_detach(grobner& g, equation* e): g(g), e(e) {}
        ~scoped_detach() {
            if (e) {
                e->set_processed(true);
                e->set_index(g.m_processed.size());
                g.m_processed.push_back(e);
            }
        }
    };

    void update_stats_max_degree_and_size(const equation& e);
    bool is_tuned() const { return m_config.m_algorithm == config::tuned;  }
    bool is_basic() const { return m_config.m_algorithm == config::basic; }
};

}
