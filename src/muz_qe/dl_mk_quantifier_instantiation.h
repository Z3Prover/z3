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
#ifndef _DL_MK_QUANTIFIER_INSTANTIATION_H_
#define _DL_MK_QUANTIFIER_INSTANTIATION_H_


#include"dl_rule_transformer.h"
#include"expr_safe_replace.h"


namespace datalog {

    class context;

    class mk_quantifier_instantiation : public rule_transformer::plugin {
        typedef svector<std::pair<expr*,expr*> > term_pairs;

        class union_find {
            unsigned_vector   m_find;
            unsigned_vector   m_size;
            unsigned_vector   m_next;

            void ensure_size(unsigned v) {
                while (v >= get_num_vars()) {
                    mk_var();
                }
            }
        public:
            unsigned mk_var() {
                unsigned r = m_find.size();
                m_find.push_back(r);
                m_size.push_back(1);
                m_next.push_back(r);
                return r;
            }
            unsigned get_num_vars() const { return m_find.size(); }
            
            unsigned find(unsigned v) const {
                if (v >= get_num_vars()) {
                    return v;
                }
                while (true) {
                    unsigned new_v = m_find[v];
                    if (new_v == v)
                        return v;
                    v = new_v;
                }
            }
            
            unsigned next(unsigned v) const { 
                if (v >= get_num_vars()) {
                    return v;
                }
                return m_next[v]; 
            }
            
            bool is_root(unsigned v) const { 
                return v >= get_num_vars() || m_find[v] == v; 
            }
            
            void merge(unsigned v1, unsigned v2) {
                unsigned r1 = find(v1);
                unsigned r2 = find(v2);
                if (r1 == r2)
                    return;
                ensure_size(v1);
                ensure_size(v2);
                if (m_size[r1] > m_size[r2])
                    std::swap(r1, r2);
                m_find[r1] = r2;
                m_size[r2] += m_size[r1];
                std::swap(m_next[r1], m_next[r2]);
            }

            void reset() {
                m_find.reset();
                m_next.reset();
                m_size.reset();
            }
        };

        ast_manager&      m;
        context&          m_ctx;
        expr_safe_replace m_var2cnst; 
        expr_safe_replace m_cnst2var;
        union_find        m_uf;
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

#endif /* _DL_MK_QUANTIFIER_INSTANTIATION_H_ */

