/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_mk_backwards.cpp

Abstract:

    Create Horn clauses for backwards flow.

Author:

    Nikolaj Bjorner (nbjorner) 2013-04-17

Revision History:

--*/

#include "muz/transforms/dl_mk_backwards.h"
#include "muz/base/dl_context.h"

namespace datalog {

    mk_backwards::mk_backwards(context & ctx, unsigned priority):
        plugin(priority),
        m(ctx.get_manager()),
        m_ctx(ctx) {        
    }

    mk_backwards::~mk_backwards() { }
        
    rule_set * mk_backwards::operator()(rule_set const & source) {
        context& ctx = source.get_context();
        rule_manager& rm = source.get_rule_manager();
        rule_set * result = alloc(rule_set, ctx);
        unsigned sz = source.get_num_rules();
        rule_ref new_rule(rm);
        app_ref_vector tail(m);
        app_ref head(m);
        svector<bool> neg;
        app_ref query(m);
        query = m.mk_fresh_const("Q", m.mk_bool_sort());
        result->set_output_predicate(query->get_decl());
        m_ctx.register_predicate(query->get_decl(), false);
        for (unsigned i = 0; i < sz; ++i) {            
            tail.reset();
            neg.reset();
            rule & r = *source.get_rule(i);
            unsigned utsz = r.get_uninterpreted_tail_size();
            unsigned tsz  = r.get_tail_size();
            if (!source.is_output_predicate(r.get_decl())) {
                tail.push_back(r.get_head());
                neg.push_back(false);
            }
            for (unsigned j = utsz; j < tsz; ++j) {
                tail.push_back(r.get_tail(j));
                neg.push_back(false);
            }
            for (unsigned j = 0; j <= utsz; ++j) {                
                if (j == utsz && j > 0) {
                    break;
                }
                if (j == utsz) {
                    head = query;
                }
                else {
                    head = r.get_tail(j);
                }
                new_rule = rm.mk(head, tail.size(), tail.c_ptr(), neg.c_ptr(), r.name(), true);
                result->add_rule(new_rule);
            }
        }
        TRACE("dl", result->display(tout););
        return result;
    }

};
