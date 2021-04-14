/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_mk_magic_symbolic.cpp

Abstract:

    Create Horn clauses for magic symbolic flow.

    Q(x)  :- A(y), B(z), phi1(x,y,z).
    Q(x)  :- C(y), phi2(x,y).
    A(x)  :- C(y), phi3(x,y).
    A(x)  :- A(y), phi3(x,y).
    B(x)  :- C(y), A(z), phi4(x,y,z).
    C(x)  :- phi5(x).

    Transformed clauses:

    Q_ans(x)   :- Q_query(x), A_ans(y), B_ans(z), phi1(x,y,z).
    Q_ans(x)   :- Q_query(x), C_ans(y), phi2(x,y).
    Q_query(x) :- true.
    
    A_ans(x)   :- A_query(x), C_ans(y), phi2(x,y)
    A_ans(x)   :- A_query(x), A_ans(y), phi3(x,y).
    A_query(y) :- Q_query(x), phi1(x,y,z).
    A_query(y) :- A_query(x), phi3(x,y).
    A_query(z) :- B_query(x), C_ans(y), phi4(x,y,z).

    B_ans(x)   :- B_query(x), C_ans(y), A_ans(z), phi4(x,y,z).
    B_query(z) :- Q_query(x), A_ans(y), phi1(x,y,z).

    C_ans(x)   :- C_query(x), phi5(x).
    C_query(y) :- Q_query(x), phi2(x,y).
    C_query(y) :- Q_query(x), phi3(x,y).
    C_query(y) :- B_query(x), phi4(x,y,z).

General scheme:
    A(x) :- P1(x_1), ..., Pn(x_n), phi(x,x1,..,x_n).

    P(x) :- Prefix(x,y,z), A(z) ... 
    
    A_ans(x) :- A_query(x), P_i_ans(x_i), phi(x,..).
    A_query(z) :- P_query(x), Prefix_ans(x,y,z).

Author:

    Nikolaj Bjorner (nbjorner) 2013-06-19

Revision History:

--*/

#include "muz/transforms/dl_mk_magic_symbolic.h"
#include "muz/base/dl_context.h"

namespace datalog {


    mk_magic_symbolic::mk_magic_symbolic(context & ctx, unsigned priority):
        plugin(priority),
        m(ctx.get_manager()),
        m_ctx(ctx) {        
    }

    mk_magic_symbolic::~mk_magic_symbolic() { }
        
    rule_set * mk_magic_symbolic::operator()(rule_set const & source) {
        if (!m_ctx.magic()) {
            return nullptr;
        }
        context& ctx = source.get_context();
        rule_manager& rm = source.get_rule_manager();
        scoped_ptr<rule_set> result = alloc(rule_set, ctx);
        unsigned sz = source.get_num_rules();
        rule_ref new_rule(rm);
        app_ref_vector tail(m);
        app_ref head(m);
        bool_vector neg;
        for (unsigned i = 0; i < sz; ++i) {            
            rule & r = *source.get_rule(i);
            unsigned utsz = r.get_uninterpreted_tail_size();
            unsigned tsz  = r.get_tail_size();
            tail.reset();
            neg.reset();
            for (unsigned j = utsz; j < tsz; ++j) {
                tail.push_back(r.get_tail(j));
                neg.push_back(false);
            }
            tail.push_back(mk_query(r.get_head()));
            neg.push_back(false);
            for (unsigned j = 0; j < utsz; ++j) {
                tail.push_back(mk_ans(r.get_tail(j)));
                neg.push_back(false);
            }
            new_rule = rm.mk(mk_ans(r.get_head()), tail.size(), tail.data(), neg.data(), r.name(), true);
            result->add_rule(new_rule);                
            if (source.is_output_predicate(r.get_decl())) {
                result->set_output_predicate(new_rule->get_decl());
                new_rule = rm.mk(mk_query(r.get_head()), 0, nullptr, nullptr, r.name(), true);
                result->add_rule(new_rule);
            }

            for (unsigned j = 0; j < utsz; ++j) {
                new_rule = rm.mk(mk_query(r.get_tail(j)), tail.size()-utsz+j, tail.data(), neg.data(), r.name(), true);
                result->add_rule(new_rule);
            }            
            
        }
        TRACE("dl", result->display(tout););
        return result.detach();
    }

    app_ref mk_magic_symbolic::mk_query(app* q) {
        string_buffer<64> name;
        func_decl* f = q->get_decl();
        name << f->get_name() << "!query";
        func_decl_ref g(m);
        g = m.mk_func_decl(symbol(name.c_str()), f->get_arity(), f->get_domain(), f->get_range());
        m_ctx.register_predicate(g, false);
        return app_ref(m.mk_app(g, q->get_num_args(), q->get_args()), m);
    }

    app_ref mk_magic_symbolic::mk_ans(app* q) {
        string_buffer<64> name;
        func_decl* f = q->get_decl();
        func_decl_ref g(m);
        name << f->get_name() << "!ans";
        g = m.mk_func_decl(symbol(name.c_str()), f->get_arity(), f->get_domain(), f->get_range());
        m_ctx.register_predicate(g, false);
        return app_ref(m.mk_app(g, q->get_num_args(), q->get_args()), m);        
    }

};
