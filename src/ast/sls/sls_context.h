/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_context.h

Abstract:

    A Stochastic Local Search (SLS) Context.

Author:

    Nikolaj Bjorner (nbjorner) 2024-06-24
    
--*/
#pragma once

#include "util/sat_literal.h"
#include "util/sat_sls.h"
#include "ast/ast.h"
#include "model/model.h"
#include "util/scoped_ptr_vector.h"
#include "util/obj_hashtable.h"
#include "util/heap.h"

namespace sls {

    class context;
    
    class plugin {
    protected:
        context&  ctx;
        ast_manager& m;
        family_id m_fid;
    public:
        plugin(context& c);
        virtual ~plugin() {}
        virtual family_id fid() { return m_fid; }
        virtual void register_term(expr* e) = 0;
        virtual expr_ref get_value(expr* e) = 0;
        virtual void initialize() = 0;
        virtual bool propagate() = 0;
        virtual void propagate_literal(sat::literal lit) = 0;
        virtual bool repair_down(app* e) = 0;
        virtual void repair_up(app* e) = 0;
        virtual bool is_sat() = 0;
        virtual void on_rescale() {};
        virtual void on_restart() {};
        virtual std::ostream& display(std::ostream& out) const = 0;
        virtual void mk_model(model& mdl) = 0;
        virtual void set_value(expr* e, expr* v) = 0;
    };

    using clause = ptr_iterator<sat::literal>;

    class sat_solver_context {
    public:
        virtual ~sat_solver_context() {}
        virtual vector<sat::clause_info> const& clauses() const = 0;
        virtual sat::clause_info const& get_clause(unsigned idx) const = 0;
        virtual ptr_iterator<unsigned> get_use_list(sat::literal lit) = 0;
        virtual void flip(sat::bool_var v) = 0;
        virtual double reward(sat::bool_var v) = 0;
        virtual double get_weigth(unsigned clause_idx) = 0;
        virtual bool is_true(sat::literal lit) = 0;
        virtual unsigned num_vars() const = 0;
        virtual indexed_uint_set const& unsat() const = 0;
        virtual void on_model(model_ref& mdl) = 0;
        virtual sat::bool_var add_var() = 0;
        virtual void add_clause(unsigned n, sat::literal const* lits) = 0;
    };
    
    class context {
        struct greater_depth {
            context& c;
            greater_depth(context& c) : c(c) {}
            bool operator()(unsigned x, unsigned y) const {
                return get_depth(c.term(x)) > get_depth(c.term(y));
            }
        };

        struct less_depth {
            context& c;
            less_depth(context& c) : c(c) {}
            bool operator()(unsigned x, unsigned y) const {
                return get_depth(c.term(x)) < get_depth(c.term(y));
            }
        };

        ast_manager& m;
        sat_solver_context& s;
        scoped_ptr_vector<plugin> m_plugins;
        indexed_uint_set m_relevant, m_visited;
        expr_ref_vector m_atoms;
        unsigned_vector m_atom2bool_var;
        vector<ptr_vector<expr>> m_parents;
        sat::literal_vector m_root_literals, m_unit_literals;
        random_gen m_rand;
        bool m_initialized = false;
        bool m_new_constraint = false;
        expr_ref_vector m_allterms;
        ptr_vector<expr> m_subterms;
        greater_depth m_gd;
        less_depth m_ld;
        heap<greater_depth> m_repair_down;
        heap<less_depth> m_repair_up;

        void register_plugin(plugin* p);

        void init();
        ptr_vector<expr> m_todo;
        void register_terms(expr* e);
        void register_term(expr* e);
        sat::bool_var mk_atom(expr* e);

        void propagate_boolean_assignment();
        void propagate_literal(sat::literal lit);

        family_id get_fid(expr* e) const;
        
    public:
        context(ast_manager& m, sat_solver_context& s);

        // Between SAT/SMT solver and context.
        void register_atom(sat::bool_var v, expr* e);
        lbool check();       

        // expose sat_solver to plugins
        vector<sat::clause_info> const& clauses() const { return s.clauses(); }
        sat::clause_info const& get_clause(unsigned idx) const { return s.get_clause(idx); }
        ptr_iterator<unsigned> get_use_list(sat::literal lit) { return s.get_use_list(lit); }
        double get_weight(unsigned clause_idx) { return s.get_weigth(clause_idx); }
        unsigned num_bool_vars() const { return s.num_vars(); }
        bool is_true(sat::literal lit) { return s.is_true(lit); }  
        bool is_true(sat::bool_var v) { return s.is_true(sat::literal(v, false)); }
        expr* atom(sat::bool_var v) { return m_atoms.get(v, nullptr); }
        expr* term(unsigned id) const { return m_allterms.get(id); }
        sat::bool_var atom2bool_var(expr* e) const { return m_atom2bool_var.get(e->get_id(), sat::null_bool_var); }
        void flip(sat::bool_var v) { s.flip(v); }
        double reward(sat::bool_var v) { return s.reward(v); }
        indexed_uint_set const& unsat() const { return s.unsat(); }
        unsigned rand() { return m_rand(); }
        unsigned rand(unsigned n) { return m_rand(n); }
        sat::literal_vector const& root_literals() const { return m_root_literals; }
        sat::literal_vector const& unit_literals() const { return m_unit_literals; }

        void reinit_relevant();

        ptr_vector<expr> const& parents(expr* e) { 
            m_parents.reserve(e->get_id() + 1); 
            return m_parents[e->get_id()]; 
        }

        // Between plugin solvers
        expr_ref get_value(expr* e);
        void set_value(expr* e, expr* v);
        void new_value_eh(expr* e);
        bool is_true(expr* e);
        bool is_fixed(expr* e);        
        bool is_relevant(expr* e);  
        void add_constraint(expr* e);
        ptr_vector<expr> const& subterms();        
        ast_manager& get_manager() { return m; }
        std::ostream& display(std::ostream& out) const;

    };
}
