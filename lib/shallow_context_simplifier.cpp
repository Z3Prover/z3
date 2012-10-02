/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    shallow_context_simplifier.h

Abstract:

    Depth 1 context simplifier.

Author:

    Leonardo de Moura (leonardo) 2011-04-28


Revision History:

--*/
#include"shallow_context_simplifier.h"
#include"assertion_set_util.h"
#include"expr_substitution.h"
#include"th_rewriter.h"
#include"ast_smt2_pp.h"
#include"assertion_set_util.h"

struct shallow_context_simplifier::imp {
    ast_manager &     m_manager;
    th_rewriter       m_r;
    expr_substitution m_subst;
    assertion_set *   m_set;
    as_shared_occs    m_occs;
    unsigned          m_idx;
    unsigned          m_num_steps;
    unsigned          m_max_rounds;
    bool              m_modified;

    imp(ast_manager & m, params_ref const & p):
        m_manager(m),
        m_r(m, p),
        m_subst(m),
        m_set(0),
        m_occs(m, true /* track atoms */) {
        m_r.set_substitution(&m_subst);
        updt_params_core(p);
    }

    void updt_params_core(params_ref const & p) {
        m_max_rounds = p.get_uint(":max-rounds", 4);
    }
    
    void updt_params(params_ref const & p) {
        m_r.updt_params(p);
        updt_params_core(p);
    }

    ast_manager & m() const { return m_manager; }

    void set_cancel(bool f) {
        m_r.set_cancel(f);
    }

    void reset() {
        m_subst.reset();
        m_set = 0;
        m_num_steps = 0;
    }

    void push_result(expr * new_curr, proof * new_pr) {
        if (m().proofs_enabled()) {
            proof * pr = m_set->pr(m_idx);
            new_pr     = m().mk_modus_ponens(pr, new_pr);
        }
        
        m_set->update(m_idx, new_curr, new_pr);
        
        if (is_shared(new_curr)) {
            m_subst.insert(new_curr, m().mk_true(), m().mk_iff_true(new_pr));
        }
        expr * atom;
        if (is_shared_neg(new_curr, atom)) {
            m_subst.insert(atom, m().mk_false(), m().mk_iff_false(new_pr));
        }
        expr * lhs, * value;
        if (is_shared_eq(new_curr, lhs, value)) {
            TRACE("shallow_context_simplifier_bug", tout << "found eq:\n" << mk_ismt2_pp(new_curr, m()) << "\n";);
            m_subst.insert(lhs, value, new_pr);
        }
    }

    void process_current() {
        expr * curr = m_set->form(m_idx);
        expr_ref   new_curr(m());
        proof_ref  new_pr(m());

        
        if (!m_subst.empty()) {
            m_r(curr, new_curr, new_pr);
            m_num_steps += m_r.get_num_steps();
        }
        else {
            new_curr = curr;
            if (m().proofs_enabled())
                new_pr   = m().mk_reflexivity(curr);
        }

        TRACE("shallow_context_simplifier_bug", tout << mk_ismt2_pp(curr, m()) << "\n---->\n" << mk_ismt2_pp(new_curr, m()) << "\n";);
        push_result(new_curr, new_pr);
        if (new_curr != curr)
            m_modified = true;
    }

    void operator()(assertion_set & s) {
        SASSERT(is_well_sorted(s));
        as_st_report report("shallow-context-simplifier", s);
        m_num_steps = 0;
        if (s.inconsistent())
            return;
        SASSERT(m_set == 0);
        bool forward = true;
        m_set        = &s;
        m_occs(*m_set);
        TRACE("shallow_context_simplifier_bug", m_occs.display(tout, m()); );

        unsigned size = s.size();
        m_idx         = 0;
        m_modified    = false;


        expr_ref   new_curr(m());
        proof_ref  new_pr(m());
        
        unsigned round = 0;

        while (true) {
            TRACE("shallow_context_simplifier_round", s.display(tout););
            if (forward) {
                for (; m_idx < size; m_idx++) {
                    process_current();
                    if (m_set->inconsistent()) 
                        goto end;
                }
                if (m_subst.empty() && !m_modified)
                    goto end;
                m_occs(*m_set);
                m_idx        = m_set->size();
                forward      = false;
                m_subst.reset();
                m_r.set_substitution(&m_subst); // reset, but keep substitution
            }
            else {
                while (m_idx > 0) {
                    m_idx--;
                    process_current();
                    if (m_set->inconsistent()) 
                        goto end;
                }
                if (!m_modified)
                    goto end;
                m_subst.reset();
                m_r.set_substitution(&m_subst); // reset, but keep substitution
                m_modified   = false;
                m_occs(*m_set);
                m_idx        = 0;
                size         = m_set->size();
                forward      = true;
            }
            round++;
            if (round >= m_max_rounds)
                break;
            IF_VERBOSE(100, verbose_stream() << "starting new round, assertion-set size: " << m_set->num_exprs() << std::endl;);
            TRACE("shallow_context_simplifier", tout << "round finished\n"; m_set->display(tout); tout << "\n";);
        }
    end:
        m_set = 0;
        SASSERT(is_well_sorted(s));
    }

    bool is_shared(expr * t) {
        return m_occs.is_shared(t);
    }

    bool is_shared_neg(expr * t, expr * & atom) {
        if (!m().is_not(t))
            return false;
        atom = to_app(t)->get_arg(0);
        return is_shared(atom);
    }

    bool is_shared_eq(expr * t, expr * & lhs, expr * & value) {
        if (!m().is_eq(t))
            return false;
        expr * arg1 = to_app(t)->get_arg(0);
        expr * arg2 = to_app(t)->get_arg(1);
        if (m().is_value(arg1) && is_shared(arg2)) {
            lhs   = arg2;
            value = arg1;
            return true;
        }
        if (m().is_value(arg2) && is_shared(arg1)) {
            lhs   = arg1;
            value = arg2;
            return true;
        }
        return false;
    }

    unsigned get_num_steps() const { return m_num_steps; }
};

shallow_context_simplifier::shallow_context_simplifier(ast_manager & m, params_ref const & p):
    m_params(p) {
    m_imp = alloc(imp, m, p);
}

shallow_context_simplifier::~shallow_context_simplifier() {
    dealloc(m_imp);
}

void shallow_context_simplifier::updt_params(params_ref const & p) {
    m_params = p;
    m_imp->updt_params(p);
}

void shallow_context_simplifier::get_param_descrs(param_descrs & r) {
    th_rewriter::get_param_descrs(r);
    r.insert(":max-rounds", CPK_UINT, "(default: 2) maximum number of rounds.");
}

void shallow_context_simplifier::operator()(assertion_set & s) {
    m_imp->operator()(s);
}

void shallow_context_simplifier::set_cancel(bool f) {
    if (m_imp)
        m_imp->set_cancel(f);
}

void shallow_context_simplifier::cleanup() {
    ast_manager & m = m_imp->m();
    imp * d = m_imp;
    #pragma omp critical (as_st_cancel)
    {
        m_imp = 0;
    }
    dealloc(d);
    d = alloc(imp, m, m_params);
    #pragma omp critical (as_st_cancel)
    {
        m_imp = d;
    }
}

unsigned shallow_context_simplifier::get_num_steps() const {
    return m_imp->get_num_steps();
}

