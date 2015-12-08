/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    theory_seq.h

Abstract:

    Native theory solver for sequences.

Author:

    Nikolaj Bjorner (nbjorner) 2015-6-12

Revision History:

--*/
#ifndef THEORY_SEQ_H_
#define THEORY_SEQ_H_

#include "smt_theory.h"
#include "seq_decl_plugin.h"
#include "theory_seq_empty.h"
#include "th_rewriter.h"
#include "union_find.h"

namespace smt {

    class theory_seq : public theory {
        typedef union_find<theory_seq> th_union_find;
        typedef trail_stack<theory_seq> th_trail_stack;
        struct stats {
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(stats)); }
            unsigned m_num_splits;
        };
        expr_ref_vector m_rep;        // unification representative.
        vector<expr_array> m_lhs, m_rhs; // persistent sets of equalities.
        unsigned        m_eqs_head;      // index of unprocessed equation.

        expr_ref_vector m_ineqs;      // inequalities to check
        expr_ref_vector m_axioms;     
        unsigned        m_axioms_head;        
        bool            m_used;       // deprecate
        th_rewriter     m_rewrite;
        seq_util        m_util;
        arith_util      m_autil;
        th_trail_stack  m_trail_stack;
        th_union_find   m_find;
        stats           m_stats;

        virtual final_check_status final_check_eh();
        virtual bool internalize_atom(app*, bool);
        virtual bool internalize_term(app*);
        virtual void new_eq_eh(theory_var, theory_var);
        virtual void new_diseq_eh(theory_var, theory_var);
        virtual void assign_eq(bool_var v, bool is_true);
        virtual bool can_propagate();
        virtual void propagate();
        virtual void push_scope_eh();
        virtual void pop_scope_eh(unsigned num_scopes);
        virtual void restart_eh();
        virtual void relevant_eh(app* n);
        virtual theory* mk_fresh(context* new_ctx) { return alloc(theory_seq, new_ctx->get_manager()); }
        virtual char const * get_name() const { return "seq"; }
        virtual theory_var mk_var(enode* n);

        final_check_status check_ineqs();
        bool simplify_eqs();
        final_check_status add_axioms();

        void assert_axiom(expr_ref& e);
        void create_axiom(expr_ref& e);
        expr_ref canonize(expr* e, enode_pair_vector& eqs);
        expr_ref expand(expr* e, enode_pair_vector& eqs);

        void propagate_eq(bool_var v, expr* e1, expr* e2);
        expr_ref mk_skolem(char const* name, expr* e1, expr* e2);
    public:
        theory_seq(ast_manager& m);
        virtual void init_model(model_generator & mg) {
            mg.register_factory(alloc(seq_factory, get_manager(), get_family_id(), mg.get_model()));
        }

        th_trail_stack & get_trail_stack() { return m_trail_stack; }
        virtual void merge_eh(theory_var v1, theory_var v2, theory_var, theory_var);
        static void after_merge_eh(theory_var r1, theory_var r2, theory_var v1, theory_var v2) {}
        void unmerge_eh(theory_var v1, theory_var v2);

    };
};

#endif /* THEORY_SEQ_H_ */

