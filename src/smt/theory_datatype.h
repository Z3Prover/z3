/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_datatype.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-10-31.

Revision History:

--*/
#ifndef THEORY_DATATYPE_H_
#define THEORY_DATATYPE_H_

#include "smt/smt_theory.h"
#include "util/union_find.h"
#include "smt/params/theory_datatype_params.h"
#include "ast/datatype_decl_plugin.h"
#include "smt/proto_model/datatype_factory.h"

namespace smt {
    class theory_datatype : public theory {
        typedef trail_stack<theory_datatype> th_trail_stack;
        typedef union_find<theory_datatype>  th_union_find;

        struct var_data {
            ptr_vector<enode> m_recognizers; //!< recognizers of this equivalence class that are being watched.
            enode *           m_constructor; //!< constructor of this equivalence class, 0 if there is no constructor in the eqc.
            var_data():
                m_constructor(nullptr) {
            }
        };

        struct stats {
            unsigned   m_occurs_check, m_splits;
            unsigned   m_assert_cnstr, m_assert_accessor, m_assert_update_field;
            void reset() { memset(this, 0, sizeof(stats)); }
            stats() { reset(); }
        };

        
        theory_datatype_params &  m_params;
        datatype_util             m_util;
        ptr_vector<var_data>      m_var_data;
        th_union_find             m_find;
        th_trail_stack            m_trail_stack;
        datatype_factory *        m_factory;
        stats                     m_stats;

        bool is_constructor(app * f) const { return m_util.is_constructor(f); }
        bool is_recognizer(app * f) const { return m_util.is_recognizer(f); }
        bool is_accessor(app * f) const { return m_util.is_accessor(f); }
        bool is_update_field(app * f) const { return m_util.is_update_field(f); }

        bool is_constructor(enode * n) const { return is_constructor(n->get_owner()); }
        bool is_recognizer(enode * n) const { return is_recognizer(n->get_owner()); }
        bool is_accessor(enode * n) const { return is_accessor(n->get_owner()); }
        bool is_update_field(enode * n) const { return m_util.is_update_field(n->get_owner()); }

        void assert_eq_axiom(enode * lhs, expr * rhs, literal antecedent);
        void assert_is_constructor_axiom(enode * n, func_decl * c, literal antecedent);
        void assert_accessor_axioms(enode * n);
        void assert_update_field_axioms(enode * n);
        void add_recognizer(theory_var v, enode * recognizer);
        void propagate_recognizer(theory_var v, enode * r);
        void sign_recognizer_conflict(enode * c, enode * r);

        typedef enum { ENTER, EXIT } stack_op;
        typedef map<enode*, enode*, obj_ptr_hash<enode>, ptr_eq<enode> > parent_tbl;
        typedef std::pair<stack_op, enode*> stack_entry;

        ptr_vector<enode>     m_to_unmark;
        ptr_vector<enode>     m_to_unmark2;
        enode_pair_vector     m_used_eqs; // conflict, if any
        parent_tbl            m_parent; // parent explanation for occurs_check
        svector<stack_entry>  m_stack; // stack for DFS for occurs_check

        void oc_mark_on_stack(enode * n);
        bool oc_on_stack(enode * n) const { return n->get_root()->is_marked(); }

        void oc_mark_cycle_free(enode * n);
        bool oc_cycle_free(enode * n) const { return n->get_root()->is_marked2(); }

        void oc_push_stack(enode * n);

        // class for managing state of final_check
        class final_check_st {
            theory_datatype * th;
        public:
            final_check_st(theory_datatype * th);
            ~final_check_st();
        };

        enode * oc_get_cstor(enode * n);
        bool occurs_check(enode * n);
        bool occurs_check_enter(enode * n);
        void occurs_check_explain(enode * top, enode * root);

        void mk_split(theory_var v);

        void display_var(std::ostream & out, theory_var v) const;

    protected:
        theory_var mk_var(enode * n) override;
        bool internalize_atom(app * atom, bool gate_ctx) override;
        bool internalize_term(app * term) override;
        void apply_sort_cnstr(enode * n, sort * s) override;
        void new_eq_eh(theory_var v1, theory_var v2) override;
        bool use_diseqs() const override;
        void new_diseq_eh(theory_var v1, theory_var v2) override;
        void assign_eh(bool_var v, bool is_true) override;
        void relevant_eh(app * n) override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        final_check_status final_check_eh() override;
        void reset_eh() override;
        void restart_eh() override { m_util.reset(); }
        bool is_shared(theory_var v) const override;
    public:
        theory_datatype(ast_manager & m, theory_datatype_params & p);
        ~theory_datatype() override;
        theory * mk_fresh(context * new_ctx) override;
        void display(std::ostream & out) const override;
        void collect_statistics(::statistics & st) const override;
        void init_model(model_generator & m) override;
        model_value_proc * mk_value(enode * n, model_generator & m) override;
        th_trail_stack & get_trail_stack() { return m_trail_stack; }
        virtual void merge_eh(theory_var v1, theory_var v2, theory_var, theory_var);
        static void after_merge_eh(theory_var r1, theory_var r2, theory_var v1, theory_var v2) {}
        void unmerge_eh(theory_var v1, theory_var v2);
        char const * get_name() const override { return "datatype"; }
        bool include_func_interp(func_decl* f) override;

    };

};

#endif /* THEORY_DATATYPE_H_ */

