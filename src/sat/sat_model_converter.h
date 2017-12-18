/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_model_converter.h

Abstract:

    Low level model converter for SAT solver.

Author:

    Leonardo de Moura (leonardo) 2011-05-26.

Revision History:

--*/
#ifndef SAT_MODEL_CONVERTER_H_
#define SAT_MODEL_CONVERTER_H_

#include "sat/sat_types.h"
#include "util/ref_vector.h"

namespace sat {
    /**
       \brief Stores eliminated variables and Blocked clauses.
       It uses these clauses to extend/patch the model produced for the
       simplified CNF formula.

       This information may also be used to support incremental solving.
       If new clauses are asserted into the SAT engine, then we can
       restore the state by re-asserting all clauses in the model
       converter.

       This is a low-level model_converter. Given a mapping from bool_var to expr,
       it can be converted into a general Z3 model_converter
    */

    class solver;

    static unsigned counter = 0;

    class model_converter {
        
    public:
        typedef svector<std::pair<unsigned, literal>> elim_stackv;


        class elim_stack {
            unsigned        m_counter;
            unsigned        m_refcount;
            elim_stackv     m_stack;
            elim_stack(elim_stack const& );
        public:
            elim_stack(elim_stackv const& stack): 
                m_counter(0),
                m_refcount(0), 
                m_stack(stack) {
                m_counter = ++counter;
            }
            ~elim_stack() { }
            void inc_ref() { ++m_refcount; }
            void dec_ref() { if (0 == --m_refcount) { dealloc(this); } }
            elim_stackv const& stack() const { return m_stack; }
            unsigned ref_count() const { return m_refcount; }
        };

        enum kind { ELIM_VAR = 0, BLOCK_LIT, CCE, ACCE };
        class entry {
            friend class model_converter;
            unsigned                m_var:30;
            unsigned                m_kind:2;
            literal_vector          m_clauses; // the different clauses are separated by null_literal
            sref_vector<elim_stack> m_elim_stack;
            entry(kind k, bool_var v): m_var(v), m_kind(k) {}
        public:
            entry(entry const & src):
                m_var(src.m_var),
                m_kind(src.m_kind),
                m_clauses(src.m_clauses) {
                m_elim_stack.append(src.m_elim_stack);
            }
            bool_var var() const { return m_var; }
            kind get_kind() const { return static_cast<kind>(m_kind); }
        };
    private:
        vector<entry>          m_entries;
        solver const*          m_solver;

        void process_stack(model & m, literal_vector const& clause, elim_stackv const& stack) const;

        std::ostream& display(std::ostream & out, entry const& entry) const;

        bool legal_to_flip(bool_var v) const;

    public:
        model_converter();
        ~model_converter();
        void set_solver(solver const* s) { m_solver = s; }
        void operator()(model & m) const;
        model_converter& operator=(model_converter const& other);

        entry & mk(kind k, bool_var v);
        void insert(entry & e, clause const & c);
        void insert(entry & e, literal l1, literal l2);
        void insert(entry & e, clause_wrapper const & c);
        void insert(entry & c, literal_vector const& covered_clause, elim_stackv const& elim_stack);

        bool empty() const { return m_entries.empty(); }

        void reset();
        bool check_invariant(unsigned num_vars) const;
        void display(std::ostream & out) const;
        bool check_model(model const & m) const;
        void copy(model_converter const & src);
        
        /*
          \brief Append entries from src, then remove entries in src.
        */
        void flush(model_converter& src);
        void collect_vars(bool_var_set & s) const;
        unsigned max_var(unsigned min) const;
        /*
         * \brief expand entries to a list of clauses, such that
         *  the first literal in each clause is the literal whose
         *  truth value is updated as follows:
         *  
         *     lit0 := lit0 or (~lit1 & ~lit2 & ... & ~lit_k)
         *  
         */
        void expand(literal_vector& update_stack);
    };

};

#endif
