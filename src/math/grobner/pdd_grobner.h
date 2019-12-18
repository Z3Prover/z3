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

#include "math/dd/dd_pdd.h"
#include "util/dependency.h"
#include "util/obj_hashtable.h"
#include "util/region.h"
#include "util/rlimit.h"

namespace dd {

class grobner {
public:
    struct stats {
        unsigned m_simplified;
        unsigned m_max_expr_size;
        unsigned m_max_expr_degree;
        unsigned m_superposed;
        unsigned m_compute_steps;
        void reset() { memset(this, 0, sizeof(*this)); }
    };

    struct config {
        unsigned m_eqs_threshold;
    };

private:
    class equation {
        bool                       m_processed;  //!< state
        unsigned                   m_idx;        //!< position at m_equations
        pdd                        m_poly;       //   simplified expressionted monomials
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
        unsigned hash() const { return m_idx; }
        unsigned idx() const { return m_idx; }
        void operator=(pdd& p) { m_poly = p; }
        void operator=(u_dependency* d) { m_dep = d; }
        bool is_processed() const { return m_processed; }
        void set_processed(bool p) { m_processed = p; }
    };

    typedef obj_hashtable<equation> equation_set;
    typedef ptr_vector<equation> equation_vector;
    typedef std::function<void (u_dependency* d, std::ostream& out)> print_dep_t;

    pdd_manager&                                 m;
    reslimit&                                    m_limit;
    stats                                        m_stats;
    config                                       m_config;
    print_dep_t                                  m_print_dep;
    equation_vector                              m_equations;
    equation_set                                 m_processed;
    equation_set                                 m_to_simplify;
    mutable u_dependency_manager                 m_dep_manager;
    equation_set                                 m_all_eqs;
    bool                                         m_conflict;
public:
    grobner(reslimit& lim, pdd_manager& m);
    ~grobner();

    void operator=(print_dep_t& pd) { m_print_dep = pd; }
    void operator=(config const& c) { m_config = c; }

    void reset();
    void compute_basis();
    void add(pdd const&, u_dependency * dep);
    equation_set const& equations();
    u_dependency_manager& dep() const { return m_dep_manager;  }
    std::ostream& display_equation(std::ostream& out, const equation& eq) const;
    std::ostream& display(std::ostream& out) const;

private:
    bool compute_basis_step();
    equation* pick_next();
    bool canceled();
    bool done();
    void superpose(equation const& eq1, equation const& eq2);
    void superpose(equation const& eq);
    bool simplify_source_target(equation const& source, equation& target, bool& changed_leading_term);
    bool simplify_using(equation_set& set, equation const& eq);
    bool simplify_using(equation& eq, equation_set const& eqs);
    void toggle_processed(equation& eq);

    bool eliminate(equation& eq) { return is_trivial(eq) && (del_equation(&eq), true); }
    bool is_trivial(equation const& eq) const { return eq.poly().is_zero(); }    
    bool is_simpler(equation const& eq1, equation const& eq2) { return eq1.poly() < eq2.poly(); }
    bool check_conflict(equation const& eq) { return eq.poly().is_val() && !is_trivial(eq) && (set_conflict(), true); }    
    void set_conflict() { m_conflict = true; }

    void del_equations(unsigned old_size);
    void del_equation(equation* eq);    

    void update_stats_max_degree_and_size(const equation& e);

    std::ostream& print_stats(std::ostream&) const;

};

}
