/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    sat_sls.h

Abstract:
   
    SLS for clauses in SAT solver

Author:

    Nikolaj Bjorner (nbjorner) 2014-12-8

Notes:

--*/
#ifndef SAT_SLS_H_
#define SAT_SLS_H_

#include "util.h"
#include "sat_simplifier.h"

namespace sat {

    class index_set {
        unsigned_vector m_elems;
        unsigned_vector m_index;        
    public:
        unsigned num_elems() const { return m_elems.size(); }       
        unsigned operator[](unsigned idx) const { return m_elems[idx]; }
        void reset() { m_elems.reset(); m_index.reset(); }        
        bool empty() const { return m_elems.empty(); }        
        bool contains(unsigned idx) const;        
        void insert(unsigned idx);        
        void remove(unsigned idx);        
        unsigned choose(random_gen& rnd) const;
    };

    class sls {
    protected:
        solver&    s;
        random_gen m_rand;
        unsigned   m_max_tries;
        unsigned   m_prob_choose_min_var;      // number between 0 and 99.
        unsigned   m_clause_generation;
        ptr_vector<clause const>    m_clauses; // vector of all clauses.
        index_set        m_false;              // clauses currently false
        vector<unsigned_vector>  m_use_list;   // use lists for literals
        unsigned_vector  m_num_true;           // per clause, count of # true literals
        svector<literal> m_min_vars;           // literals with smallest break count
        model            m_model;              // current model
        clause_allocator m_alloc;              // clause allocator
        clause_vector    m_bin_clauses;        // binary clauses
        svector<bool>    m_tabu;               // variables that cannot be swapped
        volatile bool    m_cancel;
    public:
        sls(solver& s);
        virtual ~sls();        
        lbool operator()(unsigned sz, literal const* tabu, bool reuse_model);
        void set_cancel(bool f) { m_cancel = f; }
        void set_max_tries(unsigned mx) { m_max_tries = mx; }
        virtual void display(std::ostream& out) const;
    protected:
        void init(unsigned sz, literal const* tabu, bool reuse_model);
        void init_tabu(unsigned sz, literal const* tabu);
        void init_model();
        void init_use();
        void init_clauses();
        unsigned_vector const& get_use(literal lit);        
        void flip(literal lit);
        virtual void check_invariant();
        void check_use_list();
    private:
        bool pick_flip(literal& lit);
        void flip();
        unsigned get_break_count(literal lit, unsigned min_break);
    };

    /**
       \brief sls with weighted soft clauses.
    */
    class wsls : public sls {
        unsigned_vector m_clause_weights;
        svector<int>    m_hscore;
        svector<double> m_sscore;
        literal_vector  m_soft;
        svector<double> m_weights;
        double          m_best_value;
        model           m_best_model;
        index_set       m_H, m_S;
        unsigned        m_smoothing_probability;
    public:
        wsls(solver& s);
        virtual ~wsls();        
        void set_soft(unsigned sz, literal const* lits, double const* weights);        
        bool has_soft() const { return !m_soft.empty(); }
        void opt(unsigned sz, literal const* tabu, bool reuse_model);
        virtual void display(std::ostream& out) const;
        double evaluate_model(model& mdl);
    private:        
        void wflip();
        void wflip(literal lit);
        void update_hard_weights();
        bool pick_wflip(literal & lit);
        virtual void check_invariant();
        void refresh_scores(bool_var v);
        int compute_hscore(bool_var v);
        void recompute_hscores(literal lit);
        void adjust_all_values(literal lit, unsigned cl, int delta);
        void adjust_pivot_value(literal lit, unsigned cl, int delta);
    };

};

#endif
