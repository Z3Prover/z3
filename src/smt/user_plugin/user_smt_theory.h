/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    user_smt_theory.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-22.

Revision History:

--*/
#ifndef USER_SMT_THEORY_H_
#define USER_SMT_THEORY_H_

#include"user_decl_plugin.h"
#include"user_simplifier_plugin.h"
#include"smt_theory.h"
#include"union_find.h"
#include"smt_kernel.h"

namespace smt {

    class user_theory;
	typedef int Z3_bool;

    typedef void (*theory_callback_fptr)(user_theory * th);
    typedef Z3_bool (*theory_final_check_callback_fptr)(user_theory * th);
    typedef void (*theory_app_callback_fptr)(user_theory * th, app *);
    typedef void (*theory_app_bool_callback_fptr)(user_theory * th, app *, Z3_bool);
    typedef void (*theory_app_app_callback_fptr)(user_theory * th, app *, app *);
    typedef void * (*theory_mk_fresh_ext_data_fptr)(user_theory * th);

    class user_theory : public theory {
        
        typedef trail_stack<user_theory> th_trail_stack;
        typedef union_find<user_theory>  th_union_find;
        typedef std::pair<theory_var, theory_var> var_pair;

        smt_params const&   m_params;
        void *                    m_ext_context;
        void *                    m_ext_data; 
        std::string               m_name;
        bool                      m_simplify_axioms;
        user_decl_plugin *        m_decl_plugin;
        user_simplifier_plugin *  m_simplifier_plugin;

        th_union_find             m_find;
        th_trail_stack            m_trail_stack;

        svector<var_pair>         m_new_eqs;
        svector<var_pair>         m_new_diseqs;
        svector<bool_var>         m_new_assignments;
        ptr_vector<app>           m_new_relevant_apps;
        obj_hashtable<expr>       m_asserted_axiom_set;
        expr_ref_vector           m_asserted_axioms;
        ptr_vector<app>           m_parents;
        ptr_vector<ptr_vector<app> > m_use_list;

        app_ref_vector            m_persisted_axioms;
        unsigned                  m_persisted_axioms_qhead;

        struct scope {
            unsigned              m_asserted_axioms_old_sz;
            unsigned              m_parents_old_sz;
        };

        svector<scope>            m_scopes;
        
        theory_callback_fptr             m_delete_fptr;
        theory_app_callback_fptr         m_new_app_fptr;
        theory_app_callback_fptr         m_new_elem_fptr;
        theory_callback_fptr             m_init_search_fptr;
        theory_callback_fptr             m_push_fptr;
        theory_callback_fptr             m_pop_fptr;
        theory_callback_fptr             m_restart_fptr;
        theory_callback_fptr             m_reset_fptr;
        theory_final_check_callback_fptr m_final_check_fptr;
        theory_app_app_callback_fptr     m_new_eq_fptr;
        theory_app_app_callback_fptr     m_new_diseq_fptr;
        theory_app_bool_callback_fptr    m_new_assignment_fptr;
        theory_app_callback_fptr         m_new_relevant_fptr;
        theory_mk_fresh_ext_data_fptr    m_mk_fresh_fptr;


        bool              m_delete_invoking;
        bool              m_new_app_invoking;
        bool              m_new_elem_invoking;
        bool              m_init_search_invoking;
        bool              m_push_invoking;
        bool              m_pop_invoking;
        bool              m_restart_invoking;
        bool              m_reset_invoking;
        bool              m_final_check_invoking;
        bool              m_new_eq_invoking;
        bool              m_new_diseq_invoking;
        bool              m_new_assignment_invoking;
        bool              m_new_relevant_invoking;

        struct statistics {
            unsigned          m_num_eq;
            unsigned          m_num_diseq;
            unsigned          m_num_assignment;
            unsigned          m_num_user_axioms;
            statistics() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        statistics        m_stats;

    protected:
        virtual theory_var mk_var(enode * n);

        literal internalize_literal(expr * arg);
        
        void assert_axioms_into_context(unsigned old_sz);

        void assert_axiom_into_context(expr * axiom);

        void reset_propagation_queues();

        void shrink_use_list(unsigned sz);

        ptr_vector<app> * get_non_null_use_list(theory_var v);

        void mark_as_relevant(literal l);

        void assert_axiom_core(app* axiom);

    public:
        user_theory(ast_manager & m, smt_params const& p, void * ext_context, void * ext_data, char const * name, family_id fid, user_decl_plugin * dp, user_simplifier_plugin * sp);
        virtual ~user_theory();

        virtual theory * mk_fresh(context * new_ctx);

        void * get_ext_context() const { 
            return m_ext_context; 
        }

        void * get_ext_data() {
            return m_ext_data;
        }

        sort * mk_sort(symbol const & name) { 
            return m_decl_plugin->mk_sort(name); 
        }

        func_decl * mk_func_decl(symbol const & name, unsigned arity, sort * const * domain, sort * range) {
            return m_decl_plugin->mk_func_decl(name, arity, domain, range);
        }
    
        func_decl * mk_value_decl(symbol const & name, sort * s) {
            return m_decl_plugin->mk_value_decl(name, s);
        }

        void assert_axiom(ast * axiom);
        
        void assume_eq(ast * lhs, ast * rhs);

        void enable_axiom_simplification(bool flag) {
            m_simplify_axioms = flag;
        }

        void set_delete_fptr(theory_callback_fptr ptr) {
            m_delete_fptr = ptr;
        }

        void set_reduce_app_fptr(reduce_app_fptr ptr) {
            m_simplifier_plugin->set_reduce_app_fptr(ptr);
        }
    
        void set_reduce_eq_fptr(reduce_eq_fptr ptr) {
            m_simplifier_plugin->set_reduce_eq_fptr(ptr);
        }

        void set_reduce_distinct_fptr(reduce_distinct_fptr ptr) {
            m_simplifier_plugin->set_reduce_distinct_fptr(ptr); 
        }

        void set_new_app_fptr(theory_app_callback_fptr ptr) {
            m_new_app_fptr = ptr;
        }
        
        void set_new_elem_fptr(theory_app_callback_fptr ptr) {
            m_new_elem_fptr = ptr;
        }

        void set_init_search_fptr(theory_callback_fptr ptr) {
            m_init_search_fptr = ptr;
        }
        
        void set_push_fptr(theory_callback_fptr ptr) {
            m_push_fptr = ptr;
        }
        
        void set_pop_fptr(theory_callback_fptr ptr) {
            m_pop_fptr = ptr;
        }

        void set_restart_fptr(theory_callback_fptr ptr) {
            m_restart_fptr = ptr;
        }

        void set_reset_fptr(theory_callback_fptr ptr) {
            m_reset_fptr = ptr;
        }
        
        void set_final_check_fptr(theory_final_check_callback_fptr ptr) {
            m_final_check_fptr = ptr;
        }

        void set_new_eq_fptr(theory_app_app_callback_fptr ptr) {
            m_new_eq_fptr = ptr;
        }

        void set_new_diseq_fptr(theory_app_app_callback_fptr ptr) {
            m_new_diseq_fptr = ptr;
        }

        void set_new_assignment_fptr(theory_app_bool_callback_fptr ptr) {
            m_new_assignment_fptr = ptr;
        }
        
        void set_new_relevant_fptr(theory_app_callback_fptr ptr) {
            m_new_relevant_fptr = ptr;
        }

        th_trail_stack & get_trail_stack() { return m_trail_stack; }

        theory_var get_var(ast * n) const;

        theory_var mk_var(ast * n);

        ast * get_root(ast * n) const;
        
        ast * get_next(ast * n) const;

        unsigned get_num_parents(ast * n) const;

        ast * get_parent(ast * n, unsigned i) const;

        unsigned get_num_parents() const { return m_parents.size(); }

        ast * get_parent(unsigned i) const { return m_parents[i]; }

        unsigned get_num_apps() const { return get_num_vars(); }
        
        app * get_app(unsigned i) const { return get_enode(i)->get_owner(); }

        unsigned get_num_asts() const { return get_num_apps(); }

        ast * get_ast(unsigned i) const { return get_app(i); }

        static void merge_eh(theory_var, theory_var, theory_var, theory_var) {}

        static void after_merge_eh(theory_var, theory_var, theory_var, theory_var) {}

        virtual void unmerge_eh(theory_var, theory_var) {}

        virtual bool internalize_atom(app * atom, bool gate_ctx);

        virtual bool internalize_term(app * term);

        virtual void apply_sort_cnstr(enode * n, sort * s);

        virtual void assign_eh(bool_var v, bool is_true);

        virtual void new_eq_eh(theory_var v1, theory_var v2);

        virtual void new_diseq_eh(theory_var v1, theory_var v2);

        virtual void relevant_eh(app * n);

        virtual void push_scope_eh();

        virtual void pop_scope_eh(unsigned num_scopes);

        virtual void restart_eh();

        virtual void init_search_eh();

        virtual final_check_status final_check_eh();

        virtual bool can_propagate();

        virtual void propagate();

        virtual void flush_eh();

        virtual void reset_eh();

        void reset(bool full_reset);

        virtual void display_statistics(std::ostream & out) const;

        virtual void display_istatistics(std::ostream & out) const;

        virtual bool build_models() const;

        virtual void init_model(model_generator & m);

        virtual void finalize_model(model_generator & m);

        virtual model_value_proc * mk_value(enode * n, model_generator & mg);

        virtual bool get_value(enode * n, expr_ref & r);

        virtual char const * get_name() const;

        virtual void display(std::ostream & out) const;
    };

    user_theory * mk_user_theory(kernel & s, void * ext_context, void * ext_data, char const * name);
};


#endif /* USER_SMT_THEORY_H_ */

