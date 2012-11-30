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
#include"tactical.h"
#include"split_clause_tactic.h"

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
        ast_manager & m_manager;
        app *         m_clause;
        proof *       m_clause_pr;
    public:
        split_pc(ast_manager & m, app * cls, proof * pr):m_manager(m), m_clause(cls), m_clause_pr(pr) {
            m.inc_ref(cls); 
            m.inc_ref(pr);
        }

        ~split_pc() {
            m_manager.dec_ref(m_clause);
            m_manager.dec_ref(m_clause_pr);
        }

        virtual void operator()(ast_manager & m, unsigned num_source, proof * const * source, proof_ref & result) {
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
            result = m.mk_unit_resolution(prs.size(), prs.c_ptr());
        }

        virtual proof_converter * translate(ast_translation & translator) {
            return alloc(split_pc, translator.to(), translator(m_clause), translator(m_clause_pr));
        }
    };

public:
    split_clause_tactic(params_ref const & ref = params_ref()) {
        updt_params(ref);
    }

    virtual tactic * translate(ast_manager & m) {
        split_clause_tactic * t = alloc(split_clause_tactic);
        t->m_largest_clause = m_largest_clause;
        return t;
    }
    
    virtual ~split_clause_tactic() {
    }

    virtual void updt_params(params_ref const & p) {
        m_largest_clause = p.get_bool("split_largest_clause", false);
    }

    virtual void collect_param_descrs(param_descrs & r) { 
        r.insert("split_largest_clause", CPK_BOOL, "(default: false) split the largest clause in the goal.");
    }
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        SASSERT(in->is_well_sorted());
        tactic_report report("split-clause", *in);
        TRACE("before_split_clause", in->display(tout););
        pc = 0; mc = 0; core = 0; 
        ast_manager & m = in->m();
        unsigned cls_pos = select_clause(m, in);
        if (cls_pos == UINT_MAX) {
            throw tactic_exception("split-clause tactic failed, goal does not contain any clause");
        }
        bool produce_proofs       = in->proofs_enabled();
        app * cls                 = to_app(in->form(cls_pos));
        expr_dependency * cls_dep = in->dep(cls_pos);
        if (produce_proofs)
            pc = alloc(split_pc, m, cls, in->pr(cls_pos));
        unsigned cls_sz = cls->get_num_args();
        report_tactic_progress(":num-new-branches", cls_sz);
        for (unsigned i = 0; i < cls_sz; i++) {
            goal * subgoal_i;
            if (i == cls_sz - 1)
                subgoal_i = in.get();
            else
                subgoal_i = alloc(goal, *in);
            expr * lit_i = cls->get_arg(i);
            proof * pr_i = 0;
            if (produce_proofs)
                pr_i = m.mk_hypothesis(lit_i);
            subgoal_i->update(cls_pos, lit_i, pr_i, cls_dep);
            subgoal_i->inc_depth();
            result.push_back(subgoal_i);
        }
    }
    
    virtual void cleanup() {
        // do nothing this tactic is too simple
    }
};

tactic * mk_split_clause_tactic(params_ref const & p) {
    return clean(alloc(split_clause_tactic, p));
}
