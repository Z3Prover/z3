/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smtlib.h

Abstract:

    SMT library utilities

Author:

    Nikolaj Bjorner (nbjorner) 2006-09-29

Revision History:

--*/
#ifndef _SMTLIB_H_
#define _SMTLIB_H_

#include "ast.h"
#include "symbol_table.h"
#include "map.h"
#include "arith_decl_plugin.h"

namespace smtlib {    

    class sort_builder {
    public:
        virtual ~sort_builder() {}
        virtual bool apply(unsigned num_params, parameter const* params, sort_ref& result) = 0;
        virtual char const* error_message() { return ""; }
    };

    class basic_sort_builder : public sort_builder {
        sort* m_sort;
    public:
        basic_sort_builder(sort* s) : m_sort(s) {}

        virtual bool apply(unsigned np, parameter const*, sort_ref& result) {
            result = m_sort;
            return m_sort && np != 0;
        }
    };


    class symtable {
        ast_manager& m_manager;
        symbol_table<sort*>  m_sorts1;
        symbol_table<sort_builder*> m_sorts;
        ptr_vector<sort_builder>    m_sorts_trail;
        symbol_table<ptr_vector<func_decl>* > m_ids;

    public:

        symtable(ast_manager& m): m_manager(m) {}

        ~symtable();

        void reset();

        void insert(symbol s, func_decl * d);

        bool find(symbol s, ptr_vector<func_decl> * & decls) {
            return m_ids.find(s, decls);
        }

        bool find1(symbol s, func_decl * & d);

        bool find_overload(symbol s, ptr_vector<sort> const & dom, func_decl * & d);

        void insert(symbol s, sort * d) {
            sort * d2;
            if (m_sorts1.find(s, d2)) {
                m_manager.dec_ref(d2);
            }
            m_manager.inc_ref(d);
            m_sorts1.insert(s, d);
        }

        bool find(symbol s, sort * & d) {
            return m_sorts1.find(s, d);
        }
        
        void insert(symbol s, sort_builder* sb);

        bool lookup(symbol s, sort_builder*& sb);

        void push_sort(symbol s, sort*);

        void pop_sorts(unsigned num_sorts);

        void get_func_decls(ptr_vector<func_decl> & result) const;

        void get_sorts(ptr_vector<sort>& result) const;
    };

    class theory {
    public:
        typedef ptr_vector<expr>::const_iterator expr_iterator;
        
        theory(ast_manager & ast_manager, symbol const& name): 
            m_name(name), 
            m_ast_manager(ast_manager), 
            m_symtable(ast_manager),
            m_asts(ast_manager)
        {}

        virtual ~theory() {}

        symtable * get_symtable() { return &m_symtable; }

        void insert(sort * s) { m_symtable.insert(s->get_name(), s); }

        void insert(func_decl * c) { m_symtable.insert(c->get_name(), c); }

        func_decl * declare_func(symbol const & id, sort_ref_buffer & domain, sort * range, 
                                 bool is_assoc, bool is_comm, bool  is_inj);
        
        sort * declare_sort(symbol const & id);

        void add_axiom(expr * axiom) { 
            m_asts.push_back(axiom);
            m_axioms.push_back(axiom); 
        }

        expr_iterator begin_axioms() const { 
            return m_axioms.begin(); 
        }

        unsigned get_num_axioms() const {
            return m_axioms.size();
        }

        expr * const * get_axioms() const {
            return m_axioms.c_ptr();
        }

        expr_iterator end_axioms() const { 
            return m_axioms.end(); 
        }

        void add_assumption(expr * axiom) { 
            m_asts.push_back(axiom);
            m_assumptions.push_back(axiom); 
        }

        unsigned get_num_assumptions() const {
            return m_assumptions.size();
        }

        expr * const * get_assumptions() const {
            return m_assumptions.c_ptr();
        }

        bool get_func_decl(symbol, func_decl*&);

        bool get_sort(symbol, sort*&);

        bool get_const(symbol, expr*&);

        void set_name(symbol const& name) { m_name = name; }

        symbol const get_name() const { return m_name; }
    protected:
        symbol m_name;
        ast_manager&           m_ast_manager;
        ptr_vector<expr>       m_axioms;       
        ptr_vector<expr>       m_assumptions;
        symtable               m_symtable;
        ast_ref_vector         m_asts;

    private:
        theory& operator=(theory const&);

        theory(theory const&);
    };
        
    class benchmark : public theory {        
    public:
        enum status {
            UNKNOWN, 
            SAT, 
            UNSAT
        };

        benchmark(ast_manager & ast_manager, symbol const & name) : 
            theory(ast_manager, name), 
            m_status(UNKNOWN) {}

        virtual ~benchmark() {}

        status get_status() const { return m_status; }
        void   set_status(status status) { m_status = status; }

        symbol get_logic() const { 
            if (m_logic == symbol::null) {
                return symbol("ALL");
            }
            return m_logic; 
        }

        void set_logic(symbol const & s) { m_logic = s; }

        unsigned get_num_formulas() const {
            return m_formulas.size();
        }

        expr_iterator begin_formulas() const { 
            return m_formulas.begin(); 
        }

        expr_iterator end_formulas() const { 
            return m_formulas.end(); 
        }

        void add_formula(expr * formula) { 
            m_asts.push_back(formula);
            m_formulas.push_back(formula); 
        }

        void display_as_smt2(std::ostream & out) const;

    private:
        status           m_status;
        symbol           m_logic;
        ptr_vector<expr> m_formulas;
    };
};

#endif
