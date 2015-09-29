/*++
Module Name:

    theory_str.h

Abstract:

    String Theory Plugin

Author:

    Murphy Berzish (mtrberzi) 2015-09-03

Revision History:

--*/
#ifndef _THEORY_STR_H_
#define _THEORY_STR_H_

#include"smt_theory.h"
#include"trail.h"
#include"th_rewriter.h"
#include"value_factory.h"
#include"smt_model_generator.h"
#include"arith_decl_plugin.h"
#include<set>

namespace smt {

    class str_value_factory : public value_factory {
        str_util m_util;
    public:
        str_value_factory(ast_manager & m, family_id fid) :
            value_factory(m, fid),
            m_util(m) {}
        virtual ~str_value_factory() {}
        virtual expr * get_some_value(sort * s) {
            return m_util.mk_string("some value");
        }
        virtual bool get_some_values(sort * s, expr_ref & v1, expr_ref & v2) {
            v1 = m_util.mk_string("value 1");
            v2 = m_util.mk_string("value 2");
            return true;
        }
        virtual expr * get_fresh_value(sort * s) { NOT_IMPLEMENTED_YET(); }
        virtual void register_value(expr * n) { /* Ignore */ }
    };

    class theory_str : public theory {
        // TODO
    protected:
        bool search_started;
        arith_util m_autil;
        str_util m_strutil;

        str_value_factory * m_factory;

        ptr_vector<enode> m_basicstr_axiom_todo;
        svector<std::pair<enode*,enode*> > m_str_eq_todo;
        ptr_vector<enode> m_concat_axiom_todo;

        int tmpXorVarCount;
        std::map<std::pair<expr*, expr*>, std::map<int, expr*> > varForBreakConcat;
    protected:
        void assert_axiom(expr * e);
        void assert_implication(expr * premise, expr * conclusion);

        app * mk_strlen(app * e);
        app * mk_concat(app * e1, app * e2);

        app * mk_internal_xor_var();

        bool is_concat(app const * a) const { return a->is_app_of(get_id(), OP_STRCAT); }
        bool is_concat(enode const * n) const { return is_concat(n->get_owner()); }
        bool is_string(app const * a) const { return a->is_app_of(get_id(), OP_STR); }
        bool is_string(enode const * n) const { return is_string(n->get_owner()); }
        void instantiate_concat_axiom(enode * cat);
        void instantiate_basic_string_axioms(enode * str);
        void instantiate_str_eq_length_axiom(enode * lhs, enode * rhs);

        void set_up_axioms(expr * ex);
        void handle_equality(expr * lhs, expr * rhs);

        expr * get_eqc_value(expr * n, bool & hasEqcValue);

        void simplify_concat_equality(expr * lhs, expr * rhs);
        void solve_concat_eq_str(expr * concat, expr * str);

        bool new_eq_check(expr * lhs, expr * rhs);
        void group_terms_by_eqc(expr * n, std::set<expr*> & concats, std::set<expr*> & vars, std::set<expr*> & consts);
    public:
        theory_str(ast_manager & m);
        virtual ~theory_str();
    protected:
        virtual bool internalize_atom(app * atom, bool gate_ctx);
        virtual bool internalize_term(app * term);

        virtual void new_eq_eh(theory_var, theory_var);
        virtual void new_diseq_eh(theory_var, theory_var);

        virtual theory* mk_fresh(context*) { return alloc(theory_str, get_manager()); }
        virtual void init_search_eh();
        virtual void relevant_eh(app * n);
        virtual void assign_eh(bool_var v, bool is_true);
        virtual void push_scope_eh();
        virtual void pop_scope_eh(unsigned num_scopes);
        virtual void reset_eh();

        virtual bool can_propagate();
        virtual void propagate();

        virtual final_check_status final_check_eh();
        void attach_new_th_var(enode * n);

        virtual void init_model(model_generator & m);
        virtual model_value_proc * mk_value(enode * n, model_generator & mg);
        virtual void finalize_model(model_generator & mg);
    };

};

#endif /* _THEORY_STR_H_ */
