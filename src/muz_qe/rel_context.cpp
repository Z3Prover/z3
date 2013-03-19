/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    rel_context.cpp

Abstract:

    context for relational datalog engine.

Author:

    Nikolaj Bjorner (nbjorner) 2012-12-3.

Revision History:

    Extracted from dl_context

--*/
#include"rel_context.h"
#include"dl_context.h"
#include"dl_compiler.h"
#include"dl_instruction.h"
#include"dl_mk_explanations.h"
#include"dl_mk_magic_sets.h"
#include"dl_product_relation.h"
#include"dl_bound_relation.h"
#include"dl_interval_relation.h"
#include"dl_finite_product_relation.h"
#include"dl_sparse_table.h"
#include"dl_table.h"
#include"dl_table_relation.h"

namespace datalog {
   
    rel_context::rel_context(context& ctx)
        : m_context(ctx), 
          m(ctx.get_manager()),
          m_rmanager(ctx),
          m_answer(m), 
          m_cancel(false), 
          m_last_result_relation(0) {

        // register plugins for builtin tables

        get_rmanager().register_plugin(alloc(sparse_table_plugin, get_rmanager()));
        get_rmanager().register_plugin(alloc(hashtable_table_plugin, get_rmanager()));
        get_rmanager().register_plugin(alloc(bitvector_table_plugin, get_rmanager()));
        get_rmanager().register_plugin(alloc(equivalence_table_plugin, get_rmanager()));


        // register plugins for builtin relations

        get_rmanager().register_plugin(alloc(bound_relation_plugin, get_rmanager()));
        get_rmanager().register_plugin(alloc(interval_relation_plugin, get_rmanager()));

}

    rel_context::~rel_context() {
        if (m_last_result_relation) {
            m_last_result_relation->deallocate();
            m_last_result_relation = 0;
        }        
    }

    void rel_context::collect_predicates(decl_set & res) {
        unsigned rule_cnt = m_context.get_rules().get_num_rules();
        for (unsigned rindex=0; rindex<rule_cnt; rindex++) {
            rule * r = m_context.get_rules().get_rule(rindex);
            res.insert(r->get_head()->get_decl());
            unsigned tail_len = r->get_uninterpreted_tail_size();
            for (unsigned tindex=0; tindex<tail_len; tindex++) {
                res.insert(r->get_tail(tindex)->get_decl());
            }
        }
        decl_set::iterator oit = m_output_preds.begin();
        decl_set::iterator oend = m_output_preds.end();
        for (; oit!=oend; ++oit) {
            res.insert(*oit);
        }
        get_rmanager().collect_predicates(res);
    }


    lbool rel_context::saturate() {
        m_context.ensure_closed();
        
        bool time_limit = m_context.soft_timeout()!=0;
        unsigned remaining_time_limit = m_context.soft_timeout();
        unsigned restart_time = m_context.initial_restart_timeout();
        
        rule_set original_rules(m_context.get_rules());
        decl_set original_predicates;
        m_context.collect_predicates(original_predicates);
                
        instruction_block rules_code;
        instruction_block termination_code;
        execution_context ex_ctx(m_context);

        lbool result;

        TRACE("dl", m_context.display(tout););

        while (true) {
            m_context.transform_rules();
            compiler::compile(m_context, m_context.get_rules(), rules_code, termination_code);

            TRACE("dl", rules_code.display(*this, tout); );

            bool timeout_after_this_round = time_limit && (restart_time==0 || remaining_time_limit<=restart_time);

            if (time_limit || restart_time!=0) {
                unsigned timeout = time_limit ? (restart_time!=0) ? 
                    std::min(remaining_time_limit, restart_time)
                    : remaining_time_limit : restart_time;
                ex_ctx.set_timelimit(timeout);
            }

            bool early_termination = !rules_code.perform(ex_ctx);
            ex_ctx.reset_timelimit();
            VERIFY( termination_code.perform(ex_ctx) );

            rules_code.process_all_costs();

            IF_VERBOSE(10, ex_ctx.report_big_relations(1000, verbose_stream()););
        
            if (!early_termination) {
                m_context.set_status(OK);
                result = l_true;
                break;
            }

            if (memory::above_high_watermark()) {
                m_context.set_status(MEMOUT);
                result = l_undef;
                break;
            }
            if (timeout_after_this_round || m_cancel) {
                m_context.set_status(TIMEOUT);
                result = l_undef;
                break;
            }
            SASSERT(restart_time != 0);
            if (time_limit) {
                SASSERT(remaining_time_limit>restart_time);
                remaining_time_limit -= restart_time;
            }
            uint64 new_restart_time = static_cast<uint64>(restart_time)*m_context.initial_restart_timeout();
            if (new_restart_time > UINT_MAX) {
                restart_time = UINT_MAX;
            }
            else {
                restart_time = static_cast<unsigned>(new_restart_time);
            }

            rules_code.reset();
            termination_code.reset();
            ex_ctx.reset();
            m_context.reopen();
            restrict_predicates(original_predicates);
            m_context.replace_rules(original_rules);
            m_context.close();
        }
        m_context.reopen();
        restrict_predicates(original_predicates);
        m_context.replace_rules(original_rules);
        m_context.close();
        TRACE("dl", ex_ctx.report_big_relations(100, tout););
        m_cancel = false;
        return result;
    }

#define BEGIN_QUERY()                           \
    rule_set original_rules(m_context.get_rules());       \
    decl_set original_preds;                    \
    m_context.collect_predicates(original_preds);       \
    bool was_closed = m_context.is_closed();    \
    if (was_closed) {                           \
        m_context.reopen();                               \
    }                                           \

#define END_QUERY()                             \
    m_context.reopen();                                   \
    m_context.replace_rules(original_rules);              \
    restrict_predicates(original_preds);        \
                                                \
    if (was_closed) {                           \
        m_context.close();                                \
    }                                           \
 
    lbool rel_context::query(unsigned num_rels, func_decl * const* rels) {
        get_rmanager().reset_saturated_marks();
        BEGIN_QUERY();
        for (unsigned i = 0; i < num_rels; ++i) {
            set_output_predicate(rels[i]);
        }
        m_context.close();
        reset_negated_tables();
        lbool res = saturate();

        switch(res) {
        case l_true: {
            expr_ref_vector ans(m);
            expr_ref e(m);
            bool some_non_empty = num_rels == 0;
            for (unsigned i = 0; i < num_rels; ++i) {
                relation_base& rel = get_relation(rels[i]);
                if (!rel.empty()) {
                    some_non_empty = true;
                }
                rel.to_formula(e);
                ans.push_back(e);
            }
            SASSERT(!m_last_result_relation);
            if (some_non_empty) {
                m_answer = m.mk_and(ans.size(), ans.c_ptr());
            }
            else {
                m_answer = m.mk_false();
                res = l_false;
            }
            break;
        }            
        case l_false:
            m_answer = m.mk_false();
            break;
        case l_undef:
            break;
        }
        END_QUERY();
        return res;
    }

    lbool rel_context::query(expr* query) {
        get_rmanager().reset_saturated_marks();
        BEGIN_QUERY();
        rule_manager& rm = m_context.get_rule_manager();
        rule_ref qrule(rm);
        rule_ref_vector qrules(rm);
        func_decl_ref query_pred(m);
        try {
            rm.mk_query(query, query_pred, qrules, qrule);
        }
        catch(default_exception& exn) {
            m_context.close();
            m_context.set_status(INPUT_ERROR);
            throw exn;
        }
        try {            
            m_context.add_rules(qrules);
        }
        catch (default_exception& exn) {
            m_context.close();
            m_context.set_status(INPUT_ERROR);
            throw exn;
        }
        
        set_output_predicate(qrule->get_head()->get_decl());
        m_context.close();
        reset_negated_tables();
        
        if (m_context.generate_explanations()) {
            rule_transformer transformer(m_context);
            //expl_plugin is deallocated when transformer goes out of scope
            mk_explanations * expl_plugin = 
                alloc(mk_explanations, m_context, m_context.explanations_on_relation_level());
            transformer.register_plugin(expl_plugin);
            m_context.transform_rules(transformer);

            //we will retrieve the predicate with explanations instead of the original query predicate
            query_pred = expl_plugin->get_e_decl(query_pred);
            const rule_vector & query_rules = m_context.get_rules().get_predicate_rules(query_pred);
            SASSERT(query_rules.size()==1);
            qrule = query_rules.back();
        }

        if (m_context.magic_sets_for_queries()) {
            rule_transformer transformer(m_context);
            transformer.register_plugin(alloc(mk_magic_sets, m_context, qrule.get()));
            m_context.transform_rules(transformer);
        }

        lbool res = saturate();
        
        if (res != l_undef) {
            m_last_result_relation = get_relation(query_pred).clone();
            if (m_last_result_relation->empty()) {
                res = l_false;
                m_answer = m.mk_false();
            }
            else {
                m_last_result_relation->to_formula(m_answer);
            }
        }
        
        END_QUERY();
        return res;
    }

    void rel_context::reset_negated_tables() {
        rule_set::pred_set_vector const & pred_sets = m_context.get_rules().get_strats();
        bool non_empty = false;
        for (unsigned i = 1; i < pred_sets.size(); ++i) {
            func_decl_set::iterator it = pred_sets[i]->begin(), end = pred_sets[i]->end();
            for (; it != end; ++it) {
                func_decl* pred = *it;
                relation_base & rel = get_relation(pred);
                if (!rel.empty()) {
                    non_empty = true;
                    break;
                }
            }
        }
        if (!non_empty) {
            return;
        }
        // collect predicates that depend on negation.
        func_decl_set depends_on_negation;
        for (unsigned i = 1; i < pred_sets.size(); ++i) {
            bool change = true;
            while (change) {
                change = false;
                func_decl_set::iterator it = pred_sets[i]->begin(), end = pred_sets[i]->end();
                for (; it != end; ++it) {
                    func_decl* pred = *it;
                    if (depends_on_negation.contains(pred)) {
                        continue;
                    }
                    rule_vector const& rules = m_context.get_rules().get_predicate_rules(pred);
                    bool inserted = false;
                    for (unsigned j = 0; !inserted && j < rules.size(); ++j) {
                        rule* r = rules[j];
                        unsigned psz = r->get_positive_tail_size();
                        unsigned tsz = r->get_uninterpreted_tail_size();
                        if (psz < tsz) {
                            depends_on_negation.insert(pred);
                            change = true;
                            inserted = true;
                        }
                        for (unsigned k = 0; !inserted && k < tsz; ++k) {
                            func_decl* tail_decl = r->get_tail(k)->get_decl();
                            if (depends_on_negation.contains(tail_decl)) {
                                depends_on_negation.insert(pred);
                                change   = true;
                                inserted = true;
                            }
                        }
                    }
                }
            }
        }        
        func_decl_set::iterator it = depends_on_negation.begin(), end = depends_on_negation.end();
        for (; it != end; ++it) {
            func_decl* pred = *it;
            relation_base & rel = get_relation(pred);
            
            if (!rel.empty()) {
                TRACE("dl", tout << "Resetting: " << mk_ismt2_pp(pred, m) << "\n";);
                rel.reset();
            }
        }
    }

    void rel_context::set_output_predicate(func_decl * pred) { 
        if (!m_output_preds.contains(pred)) {
            m_output_preds.insert(pred);
        }
    }

    void rel_context::restrict_predicates( const decl_set & res ) {
        set_intersection(m_output_preds, res);
        get_rmanager().restrict_predicates(res);
    }

    relation_base & rel_context::get_relation(func_decl * pred)  { return get_rmanager().get_relation(pred); }
    relation_base * rel_context::try_get_relation(func_decl * pred) const { return get_rmanager().try_get_relation(pred); }

    relation_manager & rel_context::get_rmanager() { return m_rmanager; }

    const relation_manager & rel_context::get_rmanager() const { return m_rmanager; }

    bool rel_context::output_profile() const { return m_context.output_profile(); }


    void rel_context::set_predicate_representation(func_decl * pred, unsigned relation_name_cnt, 
                                                   symbol const * relation_names) {

        relation_manager & rmgr = get_rmanager();

        family_id target_kind = null_family_id;
        switch (relation_name_cnt) {
        case 0: 
            return;
        case 1:
            target_kind = get_ordinary_relation_plugin(relation_names[0]).get_kind();
            break;
        default: {
            svector<family_id> rel_kinds; // kinds of plugins that are not table plugins
            family_id rel_kind;           // the aggregate kind of non-table plugins
            for (unsigned i = 0; i < relation_name_cnt; i++) {
                relation_plugin & p = get_ordinary_relation_plugin(relation_names[i]);
                rel_kinds.push_back(p.get_kind());                
            }
            if (rel_kinds.size() == 1) {
                rel_kind = rel_kinds[0];
            }
            else {
                relation_signature rel_sig;
                //rmgr.from_predicate(pred, rel_sig);
                product_relation_plugin & prod_plugin = product_relation_plugin::get_plugin(rmgr);
                rel_kind = prod_plugin.get_relation_kind(rel_sig, rel_kinds);
            }
            target_kind = rel_kind;
            break;
        }       
        }

        SASSERT(target_kind != null_family_id);
        get_rmanager().set_predicate_kind(pred, target_kind);
    }

    relation_plugin & rel_context::get_ordinary_relation_plugin(symbol relation_name) {
        relation_plugin * plugin = get_rmanager().get_relation_plugin(relation_name);
        if (!plugin) {
            std::stringstream sstm;
            sstm << "relation plugin " << relation_name << " does not exist";
            throw default_exception(sstm.str());
        }
        if (plugin->is_product_relation()) {
            throw default_exception("cannot request product relation directly");
        }
        if (plugin->is_sieve_relation()) {
            throw default_exception("cannot request sieve relation directly");
        }
        if (plugin->is_finite_product_relation()) {
            throw default_exception("cannot request finite product relation directly");
        }
        return *plugin;
    }

    bool rel_context::result_contains_fact(relation_fact const& f) {
        SASSERT(m_last_result_relation);
        return m_last_result_relation->contains_fact(f);
    }

    void rel_context::reset_tables() {
        get_rmanager().reset_saturated_marks();
        rule_set::decl2rules::iterator it  = m_context.get_rules().begin_grouped_rules();
        rule_set::decl2rules::iterator end = m_context.get_rules().end_grouped_rules();
        for (; it != end; ++it) {
            func_decl* p = it->m_key;
            relation_base & rel = get_relation(p);
            rel.reset();
        }
        for (unsigned i = 0; i < m_table_facts.size(); ++i) {
            func_decl* pred = m_table_facts[i].first;
            relation_fact const& fact = m_table_facts[i].second;
            get_relation(pred).add_fact(fact);
        }
    }
 
    void rel_context::add_fact(func_decl* pred, relation_fact const& fact) {
        get_rmanager().reset_saturated_marks();
        get_relation(pred).add_fact(fact);
        m_table_facts.push_back(std::make_pair(pred, fact));
    }

    void rel_context::add_fact(func_decl* pred, table_fact const& fact) {
        get_rmanager().reset_saturated_marks();
        relation_base & rel0 = get_relation(pred);
        if (rel0.from_table()) {
            table_relation & rel = static_cast<table_relation &>(rel0);
            rel.add_table_fact(fact);
            // TODO: table facts?
        }
        else {
            relation_fact rfact(m);
            for (unsigned i = 0; i < fact.size(); ++i) {
                rfact.push_back(m_context.get_decl_util().mk_numeral(fact[i], pred->get_domain()[i]));
            }
            add_fact(pred, rfact);
        }
    }

    void rel_context::store_relation(func_decl * pred, relation_base * rel) {
        get_rmanager().store_relation(pred, rel);
    }

    void rel_context::inherit_predicate_kind(func_decl* new_pred, func_decl* orig_pred) {
        if (orig_pred) {
            family_id target_kind = get_rmanager().get_requested_predicate_kind(orig_pred);            
            if (target_kind != null_family_id) {
                get_rmanager().set_predicate_kind(new_pred, target_kind);
            }
        }
    }

    void rel_context::display_output_facts(std::ostream & out) const {
        get_rmanager().display_output_tables(out);
    }

    void rel_context::display_facts(std::ostream& out) const {
        get_rmanager().display(out);
    }


};
