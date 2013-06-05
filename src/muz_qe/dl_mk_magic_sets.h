/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_mk_magic_sets.h

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-10-4.

Revision History:

--*/
#ifndef _DL_MK_MAGIC_SETS_H_
#define _DL_MK_MAGIC_SETS_H_

#include<utility>

#include"map.h"
#include"obj_pair_hashtable.h"

#include"dl_context.h"
#include"dl_rule_set.h"
#include"dl_rule_transformer.h"

namespace datalog {

    /**
       \brief Implements magic sets rule transformation.

       According to A. Voronkov. Foundations of Deductive Databases. 
       
       The stratified negation is not in the book addressed wrt. magic sets, but it seems 
       that, for the purpose of magic sets, the negated literals should be treated just as 
       if they were non-negated (we are interested only in values of arguments, not in the 
       actual content of relations, at that point).
    */
    class mk_magic_sets : public rule_transformer::plugin {

        enum a_flag {
            AD_FREE,
            AD_BOUND
        };

        struct a_flag_hash {
            typedef a_flag data;
            unsigned operator()(a_flag x) const { return x; }
        };

        struct adornment : public svector<a_flag> {

            void populate(app * lit, const var_idx_set & bound_vars);

            bool operator==(const adornment & o) const {
                return vectors_equal(*this, o);
            }
            std::string to_string() const;
        };

        struct adornment_desc {
            func_decl * m_pred;
            adornment m_adornment;

            adornment_desc() {}
            adornment_desc(func_decl * pred) : m_pred(pred) {}
            adornment_desc(func_decl * pred, const adornment & a) 
                : m_pred(pred), m_adornment(a) {}

            bool operator==(const adornment_desc & o) const {
                //m_tail_adornment value is implied by the rule and the head adornment
                return m_pred==o.m_pred && m_adornment==o.m_adornment;
            }
            unsigned hash() const {
                return m_pred->hash()^svector_hash<a_flag_hash>()(m_adornment);
            }
        };

        struct adorned_rule {
            app * m_head;
            adornment m_head_adornment;
            ptr_vector<app> m_tail;
        };

        typedef hashtable<adornment_desc, obj_hash<adornment_desc>, 
            default_eq<adornment_desc> >  adornment_set;
        typedef map<adornment_desc, func_decl *, obj_hash<adornment_desc>, 
            default_eq<adornment_desc> >  adornment_map;
        typedef obj_map<func_decl, adornment> pred_adornment_map;
        typedef obj_map<func_decl, func_decl *> pred2pred;

        context &	       m_context;
        ast_manager &          m;
        rule_manager&          rm;
        ast_ref_vector         m_pinned;
        /**
           \brief Predicates from the original set that appear in a head of a rule
         */
        func_decl_set          m_extentional;

        //adornment_set m_processed;
        vector<adornment_desc> m_todo;
        adornment_map          m_adorned_preds;
        pred_adornment_map     m_adornments;
        pred2pred              m_magic_preds;
        func_decl_ref          m_goal;
        
        void reset();

        float get_unbound_cost(app * lit, const var_idx_set & bound_vars);

        int pop_bound(unsigned_vector & cont, rule * r, const var_idx_set & bound_vars);
        app * create_magic_literal(app * l);
        void create_magic_rules(app * head, unsigned tail_cnt, app * const * tail, bool const* negated, rule_set& result);
        app * adorn_literal(app * lit, const var_idx_set & bound_vars);
        void transform_rule(const adornment & head_adornment,  rule * r, rule_set& result);
        void create_transfer_rule(const adornment_desc & d, rule_set& result);
    public:
        /**
           \brief Create magic sets rule transformer for \c goal_rule. When applying the transformer,
           the \c goal_rule must be present in the \c rule_set that is being transformed.
         */
        mk_magic_sets(context & ctx, func_decl* goal);
        
        rule_set * operator()(rule_set const & source);
    };

};

#endif /* _DL_MK_MAGIC_SETS_H_ */

