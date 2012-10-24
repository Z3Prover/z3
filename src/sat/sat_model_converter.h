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
#ifndef _SAT_MODEL_CONVERTER_H_
#define _SAT_MODEL_CONVERTER_H_

#include"sat_types.h"

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
    class model_converter {
    public:
        enum kind { ELIM_VAR = 0, BLOCK_LIT };
        class entry {
            friend class model_converter;
            unsigned           m_var:31;
            unsigned           m_kind:1;
            literal_vector     m_clauses; // the different clauses are separated by null_literal
            entry(kind k, bool_var v):m_var(v), m_kind(k) {}
        public:
            entry(entry const & src):
                m_var(src.m_var),
                m_kind(src.m_kind),
                m_clauses(src.m_clauses) {
            }
            bool_var var() const { return m_var; } 
            kind get_kind() const { return static_cast<kind>(m_kind); }
        };
    private:
        vector<entry>          m_entries;
    public:
        model_converter();
        ~model_converter();
        void operator()(model & m) const;

        entry & mk(kind k, bool_var v);
        void insert(entry & e, clause const & c);
        void insert(entry & e, literal l1, literal l2);
        void insert(entry & e, clause_wrapper const & c);

        bool empty() const { return m_entries.empty(); }

        void reset();
        bool check_invariant(unsigned num_vars) const;
        void display(std::ostream & out) const;
        bool check_model(model const & m) const;

        void copy(model_converter const & src);
        void collect_vars(bool_var_set & s) const;
    };
    
};

#endif
