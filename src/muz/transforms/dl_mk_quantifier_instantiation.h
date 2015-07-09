/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_mk_quantifier_instantiation.h

Abstract:

    Convert Quantified Horn clauses into non-quantified clauses using
    instantiation.

Author:

    Ken McMillan 
    Andrey Rybalchenko
    Nikolaj Bjorner (nbjorner) 2013-04-02

Revision History:

    Based on approach suggested in the SAS 2013 paper 
    "On Solving Universally Quantified Horn Clauses"    

--*/
#ifndef DL_MK_QUANTIFIER_INSTANTIATION_H_
#define DL_MK_QUANTIFIER_INSTANTIATION_H_


#include "dl_rule_transformer.h"
#include "expr_safe_replace.h"
#include "union_find.h"


namespace datalog {

    class context;

    class mk_quantifier_instantiation : public rule_transformer::plugin {
        typedef svector<std::pair<expr*,expr*> > term_pairs;


        ast_manager&      m;
        context&          m_ctx;
        expr_safe_replace m_var2cnst; 
        expr_safe_replace m_cnst2var;
        basic_union_find  m_uf;
        ptr_vector<expr>  m_todo;
        ptr_vector<expr>  m_terms;
        ptr_vector<expr>  m_binding;
        obj_map<func_decl, ptr_vector<expr>*> m_funs;


        void extract_quantifiers(rule& r, expr_ref_vector& conjs, quantifier_ref_vector& qs);
        void collect_egraph(expr* e);
        void instantiate_rule(rule& r, expr_ref_vector& conjs, quantifier_ref_vector& qs, rule_set& rules);
        void instantiate_quantifier(quantifier* q, expr_ref_vector & conjs);
        void instantiate_quantifier(quantifier* q, app* pat, expr_ref_vector & conjs);
        void match(unsigned i, app* pat, unsigned j, term_pairs& todo, quantifier* q, expr_ref_vector& conjs);
        void yield_binding(quantifier* q, expr_ref_vector& conjs);

    public:
        mk_quantifier_instantiation(context & ctx, unsigned priority);

        virtual ~mk_quantifier_instantiation();
        
        rule_set * operator()(rule_set const & source);
    };



};

#endif /* DL_MK_QUANTIFIER_INSTANTIATION_H_ */

