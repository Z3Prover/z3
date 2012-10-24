/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_mk_filter_rules.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-18.

Revision History:

--*/
#ifndef _DL_MK_FILTER_RULES_H_
#define _DL_MK_FILTER_RULES_H_

#include"map.h"

#include"dl_rule_set.h"
#include"dl_rule_transformer.h"

namespace datalog {

    /**
       \brief Functor for applying a rule set transformation that creates "filters".
       A "filter" is a rule of the form:
       
         Head(X_1, ..., X_n) :- Tail(...)

         where X_1,...,X_n are distinct, and Tail contain repeated variables and/or values.

      After applying this functor only "filter" rules will contain atoms with repeated variables and/or values.   
    */
    class mk_filter_rules : public rule_transformer::plugin {

        struct filter_key {
            app_ref new_pred;
            expr_ref_buffer filter_args;

            filter_key(ast_manager & m) : new_pred(m), filter_args(m) {}

            unsigned hash() const {
                return new_pred->hash() ^ int_vector_hash(filter_args);
            }
            bool operator==(const filter_key & o) const {
                return o.new_pred==new_pred && vectors_equal(o.filter_args, filter_args);
            }
        };

        typedef map<filter_key*, func_decl*, obj_ptr_hash<filter_key>, deref_eq<filter_key> > filter_cache;

        context &                                 m_context;
        ast_manager &                             m_manager;
        filter_cache                              m_tail2filter;
        rule_set *                                m_result;
        rule *                                    m_current;
        bool                                      m_modified;
        ast_ref_vector                            m_pinned;

        bool is_candidate(app * pred);
        func_decl * mk_filter_decl(app * pred, var_idx_set const & non_local_vars);
        void process(rule * r);

    public:
        mk_filter_rules(context & ctx);
        ~mk_filter_rules();
        /**
           \brief Return a new rule set where only filter rules contain atoms with repeated variables and/or values.
        */
        rule_set * operator()(rule_set const & source, model_converter_ref& mc, proof_converter_ref& pc);
    };

};


#endif /* _DL_MK_FILTER_RULES_H_ */

