/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_mk_subsumption_checker.cpp

Abstract:

    Rule transformer which checks for subsumption
    (currently just for subsumption with total relations)

Author:

    Krystof Hoder (t-khoder) 2011-10-01.

Revision History:

--*/


#include <sstream>
#include "ast/ast_pp.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "muz/transforms/dl_mk_subsumption_checker.h"
#include "muz/base/fp_params.hpp"
#include "tactic/generic_model_converter.h"


namespace datalog {


    // -----------------------------------
    //
    // mk_subsumption_checker
    //
    // -----------------------------------


    bool mk_subsumption_checker::is_total_rule(const rule * r) {
        if (r->get_tail_size() != 0) {
            return false;
        }

        unsigned pt_len = r->get_positive_tail_size();
        if(pt_len != r->get_uninterpreted_tail_size()) {
            // we don't expect rules with negative tails to be total
            return false;
        }

        for (unsigned i = 0; i < pt_len; i++) {
            func_decl * tail_pred = r->get_tail(i)->get_decl();
            if (!m_total_relations.contains(tail_pred)) {
                // this rule has a non-total predicate in the tail
                return false;
            }
        }

        unsigned t_len = r->get_positive_tail_size();
        for(unsigned i = pt_len; i < t_len; i++) {
            SASSERT(!r->is_neg_tail(i)); //we assume interpreted tail not to be negated
            if (!m.is_true(r->get_tail(i))) {
                //this rule has an interpreted tail which is not constant true
                return false;
            }
        }

        var_idx_set head_vars;
        app * head = r->get_head();
        unsigned arity = head->get_num_args();
        for(unsigned i=0; i<arity; i++) {
            expr * arg = head->get_arg(i);
            if(!is_var(arg)) { return false; }
            unsigned idx = to_var(arg)->get_idx();
            if(head_vars.contains(idx)) { return false; }
            head_vars.insert(idx);
        }
        SASSERT(head_vars.num_elems()==arity);
        return true;
    }

    void mk_subsumption_checker::on_discovered_total_relation(func_decl * pred, rule * r) {
        //this should be rule marking a new relation as total
        SASSERT(!m_total_relations.contains(pred));
        SASSERT(!r || pred==r->get_decl());
        SASSERT(!r || is_total_rule(r));

        m_total_relations.insert(pred);
        m_total_relation_defining_rules.insert(pred, r);
        m_have_new_total_rule = true;
        if(r) {
            m_ref_holder.push_back(r);
        }
    }

    void mk_subsumption_checker::scan_for_total_rules(const rule_set & rules) {
        bool new_discovered;
        //we cycle through the rules until we keep discovering new total relations
        //(discovering a total relation might reveal other total relations)
        do {
            new_discovered = false;
            rule_set::iterator rend = rules.end();
            for(rule_set::iterator rit = rules.begin(); rit!=rend; ++rit) {
                rule * r = *rit;
                func_decl * head_pred = r->get_decl();
                if(is_total_rule(r) && !m_total_relations.contains(head_pred)) {
                    on_discovered_total_relation(head_pred, r);
                    new_discovered = true;
                }
            }
        } while(new_discovered);
    }


    bool mk_subsumption_checker::transform_rule(rule * r,
        rule_subsumption_index& subs_index, rule_ref & res)
    {
        unsigned u_len = r->get_uninterpreted_tail_size();
        unsigned len = r->get_tail_size();
        if(u_len==0) {
            res = r;
            return true;
        }
        app_ref head(r->get_head(), m);

        app_ref_vector tail(m);
        svector<bool> tail_neg;

        for(unsigned i=0; i<u_len; i++) {
            app * tail_atom = r->get_tail(i);
            bool neg = r->is_neg_tail(i);
            if(m_total_relations.contains(tail_atom->get_decl())
                || subs_index.is_subsumed(tail_atom)) {
                if(neg) {
                    //rule contains negated total relation, this means that it is unsatisfiable
                    //and can be removed
                    return false;
                }
                else {
                    //we remove total relations from the tail
                    continue;
                }
            }
            if(!neg && head.get()==tail_atom) {
                //rule contains its head positively in the tail, therefore
                //it will never add any new facts to the relation, so it
                //can be removed
                return false;
            }
            tail.push_back(tail_atom);
            tail_neg.push_back(neg);
        }

        if(tail.size()==u_len) {
            res = r;
            return true;
        }

        //we just copy the interpreted part of the tail
        for(unsigned i=u_len; i<len; i++) {
            tail.push_back(r->get_tail(i));
            tail_neg.push_back(r->is_neg_tail(i));
        }

        SASSERT(tail.size()==tail_neg.size());
        res = m_context.get_rule_manager().mk(head, tail.size(), tail.c_ptr(), tail_neg.c_ptr(), r->name());
        res->set_accounting_parent_object(m_context, r);
        m_context.get_rule_manager().fix_unbound_vars(res, true);
        m_context.get_rule_manager().mk_rule_rewrite_proof(*r, *res.get());

        return true;
    }

    bool rule_size_comparator(rule * r1, rule * r2) {
        return r1->get_tail_size() < r2->get_tail_size();
    }

    bool mk_subsumption_checker::transform_rules(const rule_set & orig, rule_set & tgt) {

        bool modified = false;

        func_decl_set total_relations_with_included_rules;

        rule_subsumption_index subs_index(m_context);

        rule_ref_vector orig_rules(m_context.get_rule_manager());
        orig_rules.append(orig.get_num_rules(), orig.begin());

        //before traversing we sort rules so that the shortest are in the beginning.
        //this will help make subsumption checks more efficient
        std::sort(orig_rules.c_ptr(), orig_rules.c_ptr() + orig_rules.size(), rule_size_comparator);

        for (rule * r : orig_rules) {
            func_decl * head_pred = r->get_decl();

            if (m_total_relations.contains(head_pred)) {
                if (!orig.is_output_predicate(head_pred) ||
                        total_relations_with_included_rules.contains(head_pred)) {
                    //We just skip definitions of total non-output relations as
                    //we'll eliminate them from the problem.
                    //We also skip rules of total output relations for which we have
                    //already output the rule which implies their totality.
                    modified = true;
                    continue;
                }
                rule * defining_rule = m_total_relation_defining_rules.find(head_pred);
                if (defining_rule) {
                    rule_ref totality_rule(m_context.get_rule_manager());
                    VERIFY(transform_rule(defining_rule, subs_index, totality_rule));
                    if(defining_rule!=totality_rule) {
                        modified = true;
                    }
                    tgt.add_rule(totality_rule);
                    SASSERT(totality_rule->get_decl()==head_pred);
                }
                else {
                    modified = true;
                }
                total_relations_with_included_rules.insert(head_pred);
                continue;
            }

            rule_ref new_rule(m_context.get_rule_manager());
            if (!transform_rule(r, subs_index, new_rule)) {
                modified = true;
                continue;
            }
            if (m_new_total_relation_discovery_during_transformation && is_total_rule(new_rule)) {
                on_discovered_total_relation(head_pred, new_rule.get());
            }
            if (subs_index.is_subsumed(new_rule)) {
                modified = true;
                continue;
            }
            if (new_rule.get()!=r) {
                modified = true;
            }
            tgt.add_rule(new_rule);
            subs_index.add(new_rule);
        }
        tgt.inherit_predicates(orig);
        if (!m_total_relations.empty() && m_context.get_model_converter()) {
            generic_model_converter* mc0 = alloc(generic_model_converter, m, "dl-subsumption");
            for (func_decl* p : m_total_relations) {
                mc0->add(p, m.mk_true());
            }
            m_context.add_model_converter(mc0);
        }
        TRACE("dl",
            tout << "original set size: "<<orig.get_num_rules()<<"\n"
                 << "reduced set size: "<<tgt.get_num_rules()<<"\n"; );
        return modified;
    }

    void mk_subsumption_checker::scan_for_relations_total_due_to_facts(rule_set const& source) {
        rel_context_base* rel = m_context.get_rel_context();
        if (!rel) {
            return;
        }

        func_decl_set const& candidate_preds = m_context.get_predicates();

        func_decl_set::iterator end = candidate_preds.end();
        for(func_decl_set::iterator it = candidate_preds.begin(); it!=end; ++it) {
            func_decl * pred = *it;
            unsigned rel_sz;

            if (m_total_relations.contains(pred)) { continue; } // already total
            if (!rel->try_get_size(pred, rel_sz)) { continue; }

            unsigned arity = pred->get_arity();
            if (arity > 30) { continue; }

            //for now we only check booleans domains
            for(unsigned i=0; i<arity; i++) {
                if(!m.is_bool(pred->get_domain(i))) {
                    goto next_pred;
                }
            }

            {
                unsigned total_size = 1<<arity;
                //by calling rel.knows_exact_size() we got assured that the estimate is exact

                obj_hashtable<app> * head_store;
                if(m_ground_unconditional_rule_heads.find(pred, head_store)) {
                    //Some relations may receive facts by ground unconditioned rules.
                    //We scanned for those earlier, so now we check whether we cannot get a
                    //better estimate of relation size from these.

                    unsigned gnd_rule_cnt = head_store->size();
                    if(gnd_rule_cnt>rel_sz) {
                        rel_sz = gnd_rule_cnt;
                    }
                }

                SASSERT(total_size>=rel_sz);
                if(total_size==rel_sz) {
                    on_discovered_total_relation(pred, nullptr);
                }
            }
        next_pred:;
        }
    }

    void mk_subsumption_checker::collect_ground_unconditional_rule_heads(const rule_set & rules)
    {
        rule_set::iterator rend = rules.end();
        for(rule_set::iterator rit = rules.begin(); rit!=rend; ++rit) {
            rule * r = *rit;
            func_decl * pred = r->get_decl();

            if(r->get_tail_size()!=0) { continue; }


            app * head = r->get_head();
            unsigned arity = pred->get_arity();
            for(unsigned i=0; i<arity; i++) {
                expr * arg = head->get_arg(i);
                if(!is_app(arg)) {
                    goto next_rule;
                }
            }

            if(!m_ground_unconditional_rule_heads.contains(pred)) {
                m_ground_unconditional_rule_heads.insert(pred, alloc(obj_hashtable<app>));
            }
            m_ground_unconditional_rule_heads.find(pred)->insert(head);

        next_rule:;
        }
    }

    rule_set * mk_subsumption_checker::operator()(rule_set const & source) {
        // TODO mc
        if (!m_context.get_params ().xform_subsumption_checker())
          return nullptr;

        m_have_new_total_rule = false;
        collect_ground_unconditional_rule_heads(source);
        scan_for_relations_total_due_to_facts(source);
        scan_for_total_rules(source);

        m_have_new_total_rule = false;
        rule_set * res = alloc(rule_set, m_context);
        bool modified = transform_rules(source, *res);

        if (!m_have_new_total_rule && !modified) {
            dealloc(res);
            return nullptr;
        }


        //During the construction of the new set we may discover new total relations
        //(by quantifier elimination on the uninterpreted tails).
        SASSERT(m_new_total_relation_discovery_during_transformation || !m_have_new_total_rule);
        while (m_have_new_total_rule) {
            m_have_new_total_rule = false;

            rule_set * old = res;
            res = alloc(rule_set, m_context);
            transform_rules(*old, *res);
            dealloc(old);
        }

        return res;
    }

};
