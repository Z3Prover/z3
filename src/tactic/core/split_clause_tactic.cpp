/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    split_clause_tactic.cpp

Abstract:

    Tactic that creates a subgoal for each literal in a clause (l_1 or ... or l_n).
    The tactic fails if the main goal does not contain any clause.

Author:

    Leonardo (leonardo) 2011-11-21

Notes:

--*/
#include "tactic/tactical.h"
#include "tactic/core/split_clause_tactic.h"

class split_clause_tactic : public tactic {
    bool          m_largest_clause;
    
    unsigned select_clause(ast_manager & m, goal_ref const & in) {
        unsigned result_idx = UINT_MAX;
        unsigned len = 0;
        unsigned sz  = in->size();
        for (unsigned i = 0; i < sz; i++) {
            expr * f = in->form(i);
            if (m.is_or(f)) {
                unsigned curr_len = to_app(f)->get_num_args();
                if (curr_len >= 2) {
                    // consider only non unit clauses
                    if (!m_largest_clause)
                        return i;
                    if (curr_len > len) {
                        result_idx = i;
                        len    = curr_len;
                    }
                }
            }
        }
        return result_idx;
    }

    class split_pc : public proof_converter {
        app_ref       m_clause;
        proof_ref     m_clause_pr;
    public:
        split_pc(ast_manager & m, app * cls, proof * pr):m_clause(cls, m), m_clause_pr(pr, m) {
        }

        ~split_pc() override { }

        proof_ref operator()(ast_manager & m, unsigned num_source, proof * const * source) override {
            // Let m_clause be of the form (l_0 or ... or l_{num_source - 1})
            // Each source[i] proof is a proof for "false" using l_i as a hypothesis
            // So, I use lemma for producing a proof for (not l_i) that does not contain the hypothesis,
            // and unit_resolution for building a proof for the goal.
            SASSERT(num_source == m_clause->get_num_args());
            proof_ref_buffer prs(m);
            prs.push_back(m_clause_pr);
            for (unsigned i = 0; i < num_source; i++) {
                proof * pr_i  = source[i];
                expr * not_li = m.mk_not(m_clause->get_arg(i));
                prs.push_back(m.mk_lemma(pr_i, not_li));
            }
            return proof_ref(m.mk_unit_resolution(prs.size(), prs.data()), m);
        }

        proof_converter * translate(ast_translation & translator) override {
            return alloc(split_pc, translator.to(), translator(m_clause.get()), translator(m_clause_pr.get()));
        }

        void display(std::ostream & out) override { out << "(split-clause-pc)\n"; }
    };

public:
    split_clause_tactic(params_ref const & ref = params_ref()) {
        updt_params(ref);
    }

    tactic * translate(ast_manager & m) override {
        split_clause_tactic * t = alloc(split_clause_tactic);
        t->m_largest_clause = m_largest_clause;
        return t;
    }
    
    ~split_clause_tactic() override {
    }

    void updt_params(params_ref const & p) override {
        m_largest_clause = p.get_bool("split_largest_clause", false);
    }

    void collect_param_descrs(param_descrs & r) override { 
        r.insert("split_largest_clause", CPK_BOOL, "(default: false) split the largest clause in the goal.");
    }
    
    void operator()(goal_ref const & in, 
                    goal_ref_buffer & result) override {
        tactic_report report("split-clause", *in);
        TRACE("before_split_clause", in->display(tout););
        ast_manager & m = in->m();
        unsigned cls_pos = select_clause(m, in);
        if (cls_pos == UINT_MAX) {
            throw tactic_exception("split-clause tactic failed, goal does not contain any clause");
        }
        bool produce_proofs       = in->proofs_enabled();
        app * cls                 = to_app(in->form(cls_pos));
        expr_dependency * cls_dep = in->dep(cls_pos);
        if (produce_proofs)
            in->set(alloc(split_pc, m, cls, in->pr(cls_pos)));
        report_tactic_progress(":num-new-branches", cls->get_num_args());
        for (expr* lit_i : *cls) {
            goal * subgoal_i = alloc(goal, *in);
            subgoal_i->set(in->mc());
            proof * pr_i = nullptr;
            if (produce_proofs)
                pr_i = m.mk_hypothesis(lit_i);
            subgoal_i->update(cls_pos, lit_i, pr_i, cls_dep);
            subgoal_i->inc_depth();
            result.push_back(subgoal_i);
        }
        in->set(concat(in->pc(), result.size(), result.data()));
        in->add(dependency_converter::concat(result.size(), result.data()));
    }
    
    void cleanup() override {
        // do nothing this tactic is too simple
    }
};

tactic * mk_split_clause_tactic(params_ref const & p) {
    return clean(alloc(split_clause_tactic, p));
}
