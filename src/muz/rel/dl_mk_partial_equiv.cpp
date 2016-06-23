/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_mk_partial_equiv.cpp

Abstract:

    Rule transformer which identifies predicates that are partial equivalence relations.

Author:

    Nikolaj Bjorner (nbjorner) 2012-05-14

Revision History:

--*/

#include "dl_mk_partial_equiv.h"
#include "dl_relation_manager.h"
#include "ast_pp.h"

namespace datalog {

    bool mk_partial_equivalence_transformer::is_symmetry(rule const* r) {
        func_decl* p = r->get_decl();
        return 
            p->get_arity() == 2 &&
            p->get_domain(0) == p->get_domain(1) &&
            r->get_tail_size() == 1 &&
            r->get_tail(0)->get_decl() == p &&
            r->get_head()->get_arg(0) == r->get_tail(0)->get_arg(1) &&
            r->get_head()->get_arg(1) == r->get_tail(0)->get_arg(0) &&
            is_var(r->get_head()->get_arg(0)) &&
            is_var(r->get_head()->get_arg(1)) &&
            r->get_head()->get_arg(0) != r->get_head()->get_arg(1);            
    }


    bool mk_partial_equivalence_transformer::is_transitivity(rule const* r) {
        func_decl* p = r->get_decl();
        if (p->get_arity() != 2 ||
            p->get_domain(0) != p->get_domain(1) ||
            r->get_tail_size() != 2 ||
            r->get_tail(0)->get_decl() != p ||
            r->get_tail(1)->get_decl() != p) {
            return false;
        }
        app* h = r->get_head();
        app* a = r->get_tail(0);
        app* b = r->get_tail(1);
        expr* x1 = h->get_arg(0);
        expr* x2 = h->get_arg(1);
        expr* a1 = a->get_arg(0);
        expr* a2 = a->get_arg(1);
        expr* b1 = b->get_arg(0);
        expr* b2 = b->get_arg(1);

        if (!(is_var(x1)  && is_var(x2)  && is_var(a1) && is_var(a2) && is_var(b1) && is_var(b2))) {
            return false;
        }
        if (x1 == x2 || a1 == a2 || b1 == b2) {
            return false;
        }
        if (a2 == b1) {
            if (x1 == b2 && x2 == a1) {
                return true;
            }
            if (x1 == a1 && x2 == b2) {
                return true;
            }
            return false;
        }
        if (a1 == b2) {
            if (x1 == b1 && x2 == a2) {
                return true;
            }
            if (x1 == a2 && x2 == b1) {
                return true;
            }
            return false;
        }

        return false;
;
    }


    rule_set * mk_partial_equivalence_transformer::operator()(rule_set const & source) {
        // TODO mc  

        if (source.get_num_rules() == 0) {
            return 0;
        }

        if (m_context.get_engine() != DATALOG_ENGINE) {
            return 0;
        }

        relation_manager & rm = m_context.get_rel_context()->get_rmanager();
        rule_set::decl2rules::iterator it  = source.begin_grouped_rules();
        rule_set::decl2rules::iterator end = source.end_grouped_rules();

        rule_set* res = alloc(rule_set, m_context);
        
        for (; it != end; ++it) {
            func_decl* p = it->m_key;
            rule_vector const& rv = *(it->m_value);
            bool has_symmetry = false;
            bool has_transitivity = false;
            unsigned i_symmetry = 0, i_transitivity = 0;
            family_id kind = rm.get_requested_predicate_kind(p);
            for (unsigned i = 0; i < rv.size(); ++i) {
                
                if (kind != null_family_id) {
                    res->add_rule(rv[i]);
                }
                else if (is_symmetry(rv[i])) {
                    i_symmetry = i;
                    has_symmetry = true;
                }
                else if (is_transitivity(rv[i])) {
                    i_transitivity = i;
                    has_transitivity = true;
                }
                else {
                    res->add_rule(rv[i]);
                }
            }
            if (has_symmetry && !has_transitivity) {
                res->add_rule(rv[i_symmetry]);
            }
            else if (!has_symmetry && has_transitivity) {
                res->add_rule(rv[i_transitivity]);
            }
            else if (has_symmetry && has_transitivity) {
                TRACE("dl", tout << "updating predicate " << mk_pp(p, m) << " to partial equivalence\n";);
                SASSERT(kind == null_family_id);
                rm.set_predicate_kind(p, rm.get_table_plugin(symbol("equivalence"))->get_kind());
            }
        }

        if (res->get_num_rules() == source.get_num_rules()) {
            dealloc(res);
            return 0;
        }
        res->inherit_predicates(source);

        return res;
    }

};


