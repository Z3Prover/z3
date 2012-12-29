/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_mk_extract_quantifiers2.cpp

Abstract:

    Remove universal quantifiers over interpreted predicates in the body.

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-21

Revision History:

--*/

#include"dl_mk_extract_quantifiers2.h"
#include"ast_pp.h"
#include"dl_bmc_engine.h"
#include"smt_quantifier.h"
#include"smt_context.h"

namespace datalog {


    mk_extract_quantifiers2::mk_extract_quantifiers2(context & ctx) : 
        rule_transformer::plugin(101, false),
        m_ctx(ctx),
        m(ctx.get_manager()),
        rm(ctx.get_rule_manager()),
        m_query_pred(m)
    {}

    mk_extract_quantifiers2::~mk_extract_quantifiers2() {
        reset();
    }

    void mk_extract_quantifiers2::set_query(func_decl* q) {
        m_query_pred = q;
    }


    /*
     * 
     *  
     */
    void mk_extract_quantifiers2::extract(rule& r, rule_set& new_rules) {
        unsigned utsz = r.get_uninterpreted_tail_size();
        unsigned tsz = r.get_tail_size();
        expr_ref_vector conjs(m);
        quantifier_ref_vector qs(m);
        for (unsigned i = utsz; i < tsz; ++i) {
            conjs.push_back(r.get_tail(i));
        }
        datalog::flatten_and(conjs);
        for (unsigned j = 0; j < conjs.size(); ++j) {
            expr* e = conjs[j].get();
            quantifier* q;
            if (rule_manager::is_forall(m, e, q)) {
                qs.push_back(q);
            }
        }
        if (qs.empty()) {
            new_rules.add_rule(&r);
        }
        else {
            m_quantifiers.insert(&r, new quantifier_ref_vector(qs));
            // TODO
        }
    }


    void mk_extract_quantifiers2::reset() {
        obj_map<rule const, quantifier_ref_vector*>::iterator it = m_quantifiers.begin(),
            end = m_quantifiers.end();
        for (; it != end; ++it) {
            dealloc(it->m_value);
        }
        m_has_quantifiers = false;
        m_quantifiers.reset();
    }
    
    rule_set * mk_extract_quantifiers2::operator()(rule_set const & source, model_converter_ref& mc, proof_converter_ref& pc) {
        reset();
        rule_set::iterator it = source.begin(), end = source.end();
        for (; !m_has_quantifiers && it != end; ++it) {
            m_has_quantifiers = (*it)->has_quantifiers();
        }
        if (!m_has_quantifiers) {
            return 0;
        }

        rule_set* rules = alloc(rule_set, m_ctx);
        it = source.begin();
        for (; it != end; ++it) {
            extract(**it, *rules);
        }

        return rules;
    }

};


