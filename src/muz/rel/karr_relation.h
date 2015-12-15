/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    karr_relation.h

Abstract:

    Extract integer linear invariants.

Author:

    Nikolaj Bjorner (nbjorner) 2013-03-08

Revision History:

--*/
#ifndef KARR_RELATION_H_
#define KARR_RELATION_H_

#include"dl_mk_karr_invariants.h"
#include"dl_relation_manager.h"

namespace datalog {

    class karr_relation;

    class karr_relation_plugin : public relation_plugin {
        hilbert_basis m_hb;
        arith_util a;

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
            m_hb(get_ast_manager().limit()),
            a(get_ast_manager())
        {}            
        
        virtual bool can_handle_signature(const relation_signature & sig) {
            return get_manager().get_context().karr();
        }

        static symbol get_name() { return symbol("karr_relation"); }

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

#endif /* DL_MK_KARR_INVARIANTS_H_ */

