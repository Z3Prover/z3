/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_mk_interp_tail_simplifier.h

Abstract:

    Rule transformer which inlines some of the rules

Author:

    Krystof Hoder (t-khoder) 2011-10-02.

Revision History:

--*/

#ifndef _DL_MK_RULE_INLINER_H_
#define _DL_MK_RULE_INLINER_H_

#include "dl_context.h"
#include "dl_rule_transformer.h"
#include "dl_mk_interp_tail_simplifier.h"
#include "unifier.h"
#include "substitution.h"
#include "substitution_tree.h"

namespace datalog {

    class rule_unifier {
        ast_manager&   m;
        rule_manager&  m_rm;
        context&       m_context;
        /** We use this simplifier after inlining to get nicer intermediate rules */
        mk_interp_tail_simplifier m_interp_simplifier;
        substitution   m_subst;
        unifier        m_unif;
        bool           m_ready;
        bool           m_normalize;
        unsigned       m_deltas[2];
    public:
        rule_unifier(context& ctx)
            : m(ctx.get_manager()), m_rm(ctx.get_rule_manager()), m_context(ctx), 
            m_interp_simplifier(ctx), m_subst(m), m_unif(m), m_ready(false), m_normalize(true) {}
            
        /** Reset subtitution and unify tail tgt_idx of the target rule and the head of the src rule */
        bool unify_rules(rule const& tgt, unsigned tgt_idx, rule const& src);

        /**
           \brief Apply unifier to rules.
           Return false if the resulting rule is a tautology (the interpreted tail is unsat).
        */
        bool apply(rule const& tgt, unsigned tgt_idx, rule const& src, rule_ref& result);

        void display(std::ostream& stm) { m_subst.display(stm, 2, m_deltas); }

        /**
           Retrieve substitutions for src/tgt. (second argument of unify_rules).
        */
        expr_ref_vector get_rule_subst(rule const& r, bool is_tgt);

        /**
           Control if bound variables are normalized after unification.
           The default is 'true': bound variables are re-mapped to an 
           initial segment of de-Bruijn indices.
         */
        void set_normalize(bool n) { m_normalize = n; }

    private:
        void apply(app * a, bool is_tgt, app_ref& res);

        /**
           Apply substitution to a rule tail. Tail with skipped_index is skipped, 
           unless skipped_index is equal to UINT_MAX
        */        
        void apply(rule const& r, bool is_tgt, unsigned skipped_index, app_ref_vector& res, 
                   svector<bool>& res_neg);
        
    };

    class mk_rule_inliner : public rule_transformer::plugin {

        class visitor : public st_visitor {
            context& m_context;
            unsigned_vector m_unifiers;
            svector<bool> m_can_remove, m_can_expand;
            obj_map<expr, unsigned_vector> m_positions;
        public:
            visitor(context& c, substitution & s): st_visitor(s), m_context(c) {}
            virtual bool operator()(expr* e);
            void         reset() { m_unifiers.reset(); }
            void         reset(unsigned sz);
            svector<bool>& can_remove() { return m_can_remove; }
            svector<bool>& can_expand() { return m_can_expand; }
            unsigned_vector const& add_position(expr* e, unsigned j);
            unsigned_vector const& del_position(expr* e, unsigned j);
            unsigned_vector const& get_unifiers() { return m_unifiers; }
        };

        typedef obj_map<func_decl, func_decl *> decl_map;

        ast_manager &   m;
        rule_manager &  m_rm;
        context &       m_context;
        th_rewriter&    m_simp;
        rule_ref_vector m_pinned;
        func_decl_set   m_forbidden_preds;
        func_decl_set   m_preds_with_facts;
        func_decl_set   m_preds_with_neg_occurrence;
        ast_counter     m_head_pred_ctr;
        ast_counter     m_head_pred_non_empty_tails_ctr;
        ast_counter     m_tail_pred_ctr;
        rule_set        m_inlined_rules;
        horn_subsume_model_converter* m_mc;


        //used in try_to_inline_rule and do_eager_inlining
        rule_unifier    m_unifier;

        substitution_tree m_head_index;  // for straight-line relation inlining.
        substitution_tree m_tail_index;
        substitution      m_subst;
        visitor           m_head_visitor;
        visitor           m_tail_visitor;

        bool tail_matches_head(app * tail, app* head);

        bool try_to_inline_rule(rule& tgt, rule& src, unsigned tail_index, rule_ref& res);

        bool inlining_allowed(rule_set const& orig, func_decl * pred);

        void count_pred_occurrences(rule_set const & orig);

        void plan_inlining(rule_set const & orig);

        rule_set * create_allowed_rule_set(rule_set const & orig);

        bool forbid_preds_from_cycles(rule_set const & r);

        /** Ensure we don't inline two multi-head rules that would appear together in some tail */
        bool forbid_multiple_multipliers(const rule_set & orig, rule_set const & proposed_inlined_rules);

        /** Return true if the rule was modified */
        bool transform_rule(rule_set const& orig, rule * r, rule_set& tgt);
        
        /** Return true if some transformation was performed */
        bool transform_rules(const rule_set & orig, rule_set & tgt);

        bool is_oriented_rewriter(rule * r, rule_stratifier const& strat);

        /** 
            Return false if nothing was done with the rule.
            res may be set to zero if we managed to prove the rule unsatisfiable.
        */
        bool do_eager_inlining(rule * r, rule_set const& rules, rule_ref& res);


        /**
           Inline rules even if it doesn't lead to elimination of the whole predicate.

           The inlining is done as long as it doesn't increase the number of rules
           (i.e. when only one rule defining a predicate can replace tail atom).
           
           The original rule-set must be closed before passing t this function
        */
        bool do_eager_inlining(scoped_ptr<rule_set> & rules);

        bool has_quantifier(rule const& r) const;

        /**
           Inline predicates that are known to not be join-points.
         */
        bool inline_linear(scoped_ptr<rule_set>& rules);

        void add_rule(rule_set const& rule_set, rule* r, unsigned i);
        void del_rule(rule* r, unsigned i);

    public:
        mk_rule_inliner(context & ctx, unsigned priority=35000)
            : plugin(priority),
            m(ctx.get_manager()),
            m_rm(ctx.get_rule_manager()),
            m_context(ctx),
            m_simp(m_context.get_rewriter()),
            m_pinned(m_rm),
            m_inlined_rules(m_context),
            m_mc(0),
            m_unifier(ctx),
            m_head_index(m),
            m_tail_index(m),
            m_subst(m),
            m_head_visitor(ctx, m_subst),
            m_tail_visitor(ctx, m_subst)
        {}
        virtual ~mk_rule_inliner() { }

        rule_set * operator()(rule_set const & source);
    };

};

#endif /* _DL_MK_INTERP_TAIL_SIMPLIFIER_H_ */

