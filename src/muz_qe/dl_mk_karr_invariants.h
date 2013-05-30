/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_mk_karr_invariants.h

Abstract:

    Extract integer linear invariants.

Author:

    Nikolaj Bjorner (nbjorner) 2013-03-08

Revision History:

--*/
#ifndef _DL_MK_KARR_INVARIANTS_H_
#define _DL_MK_KARR_INVARIANTS_H_

#include"dl_context.h"
#include"dl_rule_set.h"
#include"dl_rule_transformer.h"
#include"arith_decl_plugin.h"
#include"hilbert_basis.h"

namespace datalog {

    /**
       \brief Rule transformer that strengthens bodies with invariants.
    */

    struct matrix {
        vector<vector<rational> > A;
        vector<rational>          b;
        svector<bool>             eq;
        unsigned size() const { return A.size(); }
        void reset() { A.reset(); b.reset(); eq.reset(); }
        matrix& operator=(matrix const& other);
        void append(matrix const& other) { A.append(other.A); b.append(other.b); eq.append(other.eq); }
        void display(std::ostream& out) const;
        static void display_row(
            std::ostream& out, vector<rational> const& row, rational const& b, bool is_eq);
        static void display_ineq(
            std::ostream& out, vector<rational> const& row, rational const& b, bool is_eq);
    };

    class mk_karr_invariants : public rule_transformer::plugin {

        class add_invariant_model_converter;
        
        context&        m_ctx;
        ast_manager&    m;
        rule_manager&   rm;
        context         m_inner_ctx;
        arith_util      a;
        obj_map<func_decl, expr*>      m_fun2inv;
        ast_ref_vector m_pinned;

        void get_invariants(rule_set const& src);

        void update_body(rule_set& result, rule& r);
        rule_set* update_rules(rule_set const& src);
    public:
        mk_karr_invariants(context & ctx, unsigned priority);

        virtual ~mk_karr_invariants();

        virtual void cancel();
        
        rule_set * operator()(rule_set const & source);

    };

    class karr_relation;

    class karr_relation_plugin : public relation_plugin {
        arith_util a;
        hilbert_basis m_hb;

        class join_fn;
        class project_fn;
        class rename_fn;
        class union_fn;
        class filter_equal_fn;
        class filter_identical_fn;
        class filter_interpreted_fn;
        friend class karr_relation;
    public:
        karr_relation_plugin(relation_manager& rm):
            relation_plugin(karr_relation_plugin::get_name(), rm),
            a(get_ast_manager())
        {}            
        
        virtual bool can_handle_signature(const relation_signature & sig) {
            return true;
        }

        static symbol get_name() { return symbol("karr_relation"); }

        virtual void set_cancel(bool f);

        virtual relation_base * mk_empty(const relation_signature & s);

        virtual relation_base * mk_full(func_decl* p, const relation_signature & s);

        static karr_relation& get(relation_base& r);
        static karr_relation const & get(relation_base const& r);   

        virtual relation_join_fn * mk_join_fn(
            const relation_base & t1, const relation_base & t2, 
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2);
        virtual relation_transformer_fn * mk_project_fn(const relation_base & t, unsigned col_cnt, 
            const unsigned * removed_cols);
        virtual relation_transformer_fn * mk_rename_fn(const relation_base & t, unsigned permutation_cycle_len, 
            const unsigned * permutation_cycle);
        virtual relation_union_fn * mk_union_fn(const relation_base & tgt, const relation_base & src, 
            const relation_base * delta);
        virtual relation_mutator_fn * mk_filter_identical_fn(const relation_base & t, unsigned col_cnt, 
            const unsigned * identical_cols);
        virtual relation_mutator_fn * mk_filter_equal_fn(const relation_base & t, const relation_element & value, 
            unsigned col);
        virtual relation_mutator_fn * mk_filter_interpreted_fn(const relation_base & t, app * condition);
    private:
        bool dualizeI(matrix& dst, matrix const& src);
        void dualizeH(matrix& dst, matrix const& src);


    };


};

#endif /* _DL_MK_KARR_INVARIANTS_H_ */

