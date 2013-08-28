/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_mk_slice.h

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-10-4.

Revision History:

--*/
#ifndef _DL_MK_SLICE_H_
#define _DL_MK_SLICE_H_

#include"dl_context.h"
#include"dl_rule_set.h"
#include"uint_set.h"
#include"dl_rule_transformer.h"

namespace datalog {

    /**
       \brief Implements a slicing rule transformation.
    */
    class mk_slice : public rule_transformer::plugin {
        class slice_proof_converter;
        class slice_model_converter;
        context&      m_ctx;
        ast_manager&  m;
        rule_manager& rm;
        svector<bool>   m_input;
        svector<bool>   m_output;
        expr_ref_vector m_solved_vars;
        svector<bool>   m_var_is_sliceable;
        obj_map<func_decl, func_decl*>  m_predicates;        
        obj_map<func_decl, bit_vector> m_sliceable;
        ast_ref_vector  m_pinned;
        slice_proof_converter*      m_pc;        
        slice_model_converter*      m_mc;

        void reset();

        void init(rule_set const& source);

        void saturate(rule_set const& source);
        
        void display(std::ostream& out);

        bool prune_rule(rule& r);
        
        void init_vars(rule& r);

        void init_vars(app* p, bool is_output, bool is_neg_tail);

        bool finalize_vars(app* p);

        unsigned num_vars() const { return m_input.size(); }

        bit_vector& get_predicate_slice(func_decl* p);

        bit_vector& get_predicate_slice(app* p) { return get_predicate_slice(p->get_decl()); }

        bool is_eq(expr* e, unsigned& v, expr_ref& r);

        void add_free_vars(uint_set& s, expr* e);

        void add_var(unsigned idx);

        bool is_output(expr* e);

        bool is_output(unsigned idx);

        void update_rules(rule_set const& src, rule_set& dst);

        void update_rule(rule& r, rule_set& dst);

        expr_ref_vector get_tail_conjs(rule const& r);

        void declare_predicates(rule_set const& src, rule_set& dst);
         
        bool rule_updated(rule const& r);

        void update_predicate(app* p, app_ref& q);

        void filter_unique_vars(rule& r);

        void solve_vars(rule& r, uint_set& used_vars, uint_set& parameter_vars);

    public:
        /**
           \brief Create slice rule transformer for \c goal predicate. When applying the transformer,
           the \c goal must be present in the \c rule_set that is being transformed.
         */
        mk_slice(context & ctx);

        virtual ~mk_slice() { }
        
        rule_set * operator()(rule_set const & source);

        func_decl* get_predicate(func_decl* p) { func_decl* q = p; m_predicates.find(p, q); return q; }

        obj_map<func_decl, func_decl*> const& get_predicates() { return m_predicates; }
    };

};

#endif /* _DL_MK_SLICE_H_ */

