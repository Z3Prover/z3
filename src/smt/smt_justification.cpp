/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_justification.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-25.

Revision History:

--*/
#include"smt_context.h"
#include"smt_conflict_resolution.h"
#include"ast_pp.h"
#include"ast_ll_pp.h"

namespace smt {


    justification_proof_wrapper::justification_proof_wrapper(context & ctx, proof * pr, bool in_region):
        justification(in_region),
        m_proof(pr) {
        ctx.get_manager().inc_ref(pr); 
    }

    void justification_proof_wrapper::del_eh(ast_manager & m) {
        m.dec_ref(m_proof);
    }
    
    proof * justification_proof_wrapper::mk_proof(conflict_resolution & cr) {
        return m_proof;
    }

    unit_resolution_justification::unit_resolution_justification(region & r, 
                                                                 justification * js, 
                                                                 unsigned num_lits, 
                                                                 literal const * lits):
        m_antecedent(js),
        m_num_literals(num_lits) {
        SASSERT(!js || js->in_region());
        m_literals = new (r) literal[num_lits];
        memcpy(m_literals, lits, sizeof(literal) * num_lits);
        TRACE("unit_resolution_justification_bug",
              for (unsigned i = 0; i < num_lits; i++) {
                  tout << lits[i] << " ";
              }
              tout << "\n";);
        SASSERT(m_num_literals > 0);
    }

    unit_resolution_justification::unit_resolution_justification(justification * js, 
                                                                 unsigned num_lits, 
                                                                 literal const * lits):
        justification(false), // object is not allocated in a region
        m_antecedent(js),
        m_num_literals(num_lits) {
        SASSERT(!js || !js->in_region());
        m_literals = alloc_vect<literal>(num_lits);
        memcpy(m_literals, lits, sizeof(literal) * num_lits);
        TRACE("unit_resolution_justification_bug",
              for (unsigned i = 0; i < num_lits; i++) {
                  tout << lits[i] << " ";
              }
              tout << "\n";);
        SASSERT(num_lits != 0);
    }

    unit_resolution_justification::~unit_resolution_justification() {
        if (!in_region()) {
            dealloc_svect(m_literals); // I don't need to invoke destructor...
            dealloc(m_antecedent);
        }
    }

    void unit_resolution_justification::get_antecedents(conflict_resolution & cr) {
        if (m_antecedent)
            cr.mark_justification(m_antecedent);
        for (unsigned i = 0; i < m_num_literals; i++)
            cr.mark_literal(m_literals[i]);
    }

    proof * unit_resolution_justification::mk_proof(conflict_resolution & cr) {
        SASSERT(m_antecedent);
        ptr_buffer<proof> prs;
        proof * pr   = cr.get_proof(m_antecedent);
        bool visited = pr != 0;
        prs.push_back(pr);
        for (unsigned i = 0; i < m_num_literals; i++) {
            proof * pr = cr.get_proof(m_literals[i]);
            if (pr == 0)
                visited = false;
            else
                prs.push_back(pr);
        }
        if (!visited)
            return 0;
        ast_manager & m = cr.get_manager();
        TRACE("unit_resolution_justification_bug",
              tout << "in mk_proof\n";
              for (unsigned i = 0; i < m_num_literals; i++) {
                  tout << m_literals[i] << " ";
              }
              tout << "\n";
              for (unsigned i = 0; i < prs.size(); i++) {
                  tout << mk_ll_pp(m.get_fact(prs[i]), m);
              });
        return m.mk_unit_resolution(prs.size(), prs.c_ptr());
    }

    void eq_conflict_justification::get_antecedents(conflict_resolution & cr) {
        SASSERT(m_node1->get_root()->is_interpreted());
        SASSERT(m_node2->get_root()->is_interpreted());
        cr.mark_eq(m_node1, m_node1->get_root());
        cr.mark_eq(m_node2, m_node2->get_root());
        cr.mark_justified_eq(m_node1, m_node2, m_js);
    }

    proof * eq_conflict_justification::mk_proof(conflict_resolution & cr) {
        ast_manager & m = cr.get_manager();
        bool visited = true;
        ptr_buffer<proof> prs;

        if (m_node1 != m_node1->get_root()) {
            proof * pr = cr.get_proof(m_node1, m_node1->get_root());
            if (pr && m.fine_grain_proofs())
                pr = m.mk_symmetry(pr);
            prs.push_back(pr);
            if (!pr) 
                visited = false;
        }

        SASSERT(m_node1 != m_node2);
        proof * pr = cr.get_proof(m_node1, m_node2, m_js);
        prs.push_back(pr);
        if (!pr)
            visited = false;

        if (m_node2 != m_node2->get_root()) {
            proof * pr = cr.get_proof(m_node2, m_node2->get_root());
            prs.push_back(pr);
            if (!pr) 
                visited = false;
        }
        
        if (!visited)
            return 0;
        
        expr * lhs = m_node1->get_root()->get_owner();
        expr * rhs = m_node2->get_root()->get_owner();
        proof * pr1 = m.mk_transitivity(prs.size(), prs.c_ptr(), lhs, rhs);
        proof * pr2 = m.mk_rewrite(m.mk_eq(lhs, rhs), m.mk_false());
        return m.mk_modus_ponens(pr1, pr2);
    }

    void eq_root_propagation_justification::get_antecedents(conflict_resolution & cr) {
        cr.mark_eq(m_node, m_node->get_root());
    }

    proof * eq_root_propagation_justification::mk_proof(conflict_resolution & cr) {
        ast_manager & m = cr.get_manager();
        expr * var = m_node->get_owner();
        expr * val = m_node->get_root()->get_owner();
        SASSERT(m.is_true(val) || m.is_false(val));
        proof * pr1 = cr.get_proof(m_node, m_node->get_root());
        if (pr1) {
            expr * lit;
            if (m.is_true(val))
                lit = var;
            else 
                lit = m.mk_not(var);
            proof * pr2 = m.mk_rewrite(m.get_fact(pr1), lit);
            return m.mk_modus_ponens(pr1, pr2);
        }
        return 0;
    }

    void eq_propagation_justification::get_antecedents(conflict_resolution & cr) {
        cr.mark_eq(m_node1, m_node2);
    }

    proof * eq_propagation_justification::mk_proof(conflict_resolution & cr) {
        return cr.get_proof(m_node1, m_node2);
    }


    void mp_iff_justification::get_antecedents(conflict_resolution & cr) {
        SASSERT(m_node1 != m_node2);
        cr.mark_eq(m_node1, m_node2);
        context & ctx = cr.get_context();
        bool_var v    = ctx.enode2bool_var(m_node1);
        lbool val     = ctx.get_assignment(v);
        literal l(v, val == l_false);
        cr.mark_literal(l);
    }

    proof * mp_iff_justification::mk_proof(conflict_resolution & cr) {
        proof * pr1   = cr.get_proof(m_node1, m_node2);
        context & ctx = cr.get_context();
        bool_var v    = ctx.enode2bool_var(m_node1);
        lbool val     = ctx.get_assignment(v);
        literal l(v, val == l_false);
        proof * pr2   = cr.get_proof(l);
        if (pr1 && pr2) {
            ast_manager & m = cr.get_manager();
            proof * pr;
            SASSERT(m.has_fact(pr1));
            SASSERT(m.has_fact(pr2));
            app* fact1 = to_app(m.get_fact(pr1));  
            app* fact2 = to_app(m.get_fact(pr2));
            SASSERT(m.is_iff(fact1));
            if (fact1->get_arg(1) == fact2) {
                pr1 = m.mk_symmetry(pr1);
                fact1 = to_app(m.get_fact(pr1));
            }
            SASSERT(m.is_iff(fact1));
            
            if (l.sign()) { 
                SASSERT(m.is_not(fact2));
                expr* lhs = fact1->get_arg(0);
                expr* rhs = fact1->get_arg(1);
                if (lhs != fact2->get_arg(0)) {
                    pr1 = m.mk_symmetry(pr1);
                    fact1 = to_app(m.get_fact(pr1));
                    std::swap(lhs, rhs);
                }
                SASSERT(lhs == fact2->get_arg(0));
                app* new_lhs = fact2;
                app* new_rhs = m.mk_not(rhs);
                pr1 = m.mk_congruence(new_lhs, new_rhs, 1, &pr1);
            }
            pr = m.mk_modus_ponens(pr2, pr1);
            
            TRACE("mp_iff_justification", tout << mk_pp(fact1, m) << "\n" << mk_pp(fact2, m) << "\n" <<
                  mk_pp(m.get_fact(pr), m) << "\n";);
            return pr;
        }
        return 0;
    }

    simple_justification::simple_justification(region & r, unsigned num_lits, literal const * lits):
        m_num_literals(num_lits) {
        m_literals = new (r) literal[num_lits];
        memcpy(m_literals, lits, sizeof(literal) * num_lits);
#ifdef Z3DEBUG
        for (unsigned i = 0; i < num_lits; i++) {
            SASSERT(lits[i] != null_literal);
        }
#endif
    }

    void simple_justification::get_antecedents(conflict_resolution & cr) {
        for (unsigned i = 0; i < m_num_literals; i++)
            cr.mark_literal(m_literals[i]);
    }

    bool simple_justification::antecedent2proof(conflict_resolution & cr, ptr_buffer<proof> & result) {
        bool visited = true;
        for (unsigned i = 0; i < m_num_literals; i++) {
            proof * pr = cr.get_proof(m_literals[i]);
            if (pr == 0)
                visited = false;
            else
                result.push_back(pr);
        }
        return visited;
    }

    proof * theory_axiom_justification::mk_proof(conflict_resolution & cr) {
        context & ctx   = cr.get_context();
        ast_manager & m = cr.get_manager();
        expr_ref_vector lits(m);
        for (unsigned i = 0; i < m_num_literals; i++) {
            expr_ref l(m);
            ctx.literal2expr(m_literals[i], l);
            lits.push_back(l);
        }
        if (lits.size() == 1)
            return m.mk_th_lemma(m_th_id, lits.get(0), 0, 0, m_params.size(), m_params.c_ptr());
        else
            return m.mk_th_lemma(m_th_id, m.mk_or(lits.size(), lits.c_ptr()), 0, 0, m_params.size(), m_params.c_ptr());
    }

    proof * theory_propagation_justification::mk_proof(conflict_resolution & cr) {
        ptr_buffer<proof> prs;
        if (!antecedent2proof(cr, prs))
            return 0;
        context & ctx = cr.get_context();
        ast_manager & m = cr.get_manager();
        expr_ref fact(m);
        ctx.literal2expr(m_consequent, fact);
        return m.mk_th_lemma(m_th_id, fact, prs.size(), prs.c_ptr(), m_params.size(), m_params.c_ptr());
    }

    proof * theory_conflict_justification::mk_proof(conflict_resolution & cr) {
        ptr_buffer<proof> prs;
        if (!antecedent2proof(cr, prs))
            return 0;
        ast_manager & m = cr.get_manager();
        return m.mk_th_lemma(m_th_id, m.mk_false(), prs.size(), prs.c_ptr(), m_params.size(), m_params.c_ptr());
    }

    ext_simple_justification::ext_simple_justification(region & r, unsigned num_lits, literal const * lits, unsigned num_eqs, enode_pair const * eqs):
        simple_justification(r, num_lits, lits),
        m_num_eqs(num_eqs) {
        m_eqs = new (r) enode_pair[num_eqs];
        if (num_eqs != 0)
            memcpy(m_eqs, eqs, sizeof(enode_pair) * num_eqs);
        DEBUG_CODE({
            for (unsigned i = 0; i < num_eqs; i++) {
                SASSERT(eqs[i].first->get_root() == eqs[i].second->get_root());
            }
        });
    }

    void ext_simple_justification::get_antecedents(conflict_resolution & cr) {
        simple_justification::get_antecedents(cr);
        for (unsigned i = 0; i < m_num_eqs; i++) {
            enode_pair const & p = m_eqs[i];
            cr.mark_eq(p.first, p.second);
        }
    }

    bool ext_simple_justification::antecedent2proof(conflict_resolution & cr, ptr_buffer<proof> & result) {
        bool visited = simple_justification::antecedent2proof(cr, result);
        for (unsigned i = 0; i < m_num_eqs; i++) {
            enode_pair const & p = m_eqs[i];
            proof * pr = cr.get_proof(p.first, p.second);
            if (pr == 0)
                visited = false;
            else
                result.push_back(pr);
        }
        return visited;
    }

    proof * ext_theory_propagation_justification::mk_proof(conflict_resolution & cr) {
        ptr_buffer<proof> prs;
        if (!antecedent2proof(cr, prs))
            return 0;
        context & ctx = cr.get_context();
        ast_manager & m = cr.get_manager();
        expr_ref fact(m);
        ctx.literal2expr(m_consequent, fact);
        return m.mk_th_lemma(m_th_id, fact, prs.size(), prs.c_ptr(), m_params.size(), m_params.c_ptr());
    }
    
    proof * ext_theory_conflict_justification::mk_proof(conflict_resolution & cr) {
        ptr_buffer<proof> prs;
        if (!antecedent2proof(cr, prs))
            return 0;
        ast_manager & m = cr.get_manager();
        return m.mk_th_lemma(m_th_id, m.mk_false(), prs.size(), prs.c_ptr(), m_params.size(), m_params.c_ptr());
    }

    proof * ext_theory_eq_propagation_justification::mk_proof(conflict_resolution & cr) {
        ptr_buffer<proof> prs;
        if (!antecedent2proof(cr, prs))
            return 0;
        ast_manager & m = cr.get_manager();
        context & ctx   = cr.get_context();
        expr * fact     = ctx.mk_eq_atom(m_lhs->get_owner(), m_rhs->get_owner());
        return m.mk_th_lemma(m_th_id, fact, prs.size(), prs.c_ptr(), m_params.size(), m_params.c_ptr());
    }

    
    theory_lemma_justification::theory_lemma_justification(family_id fid, context & ctx, unsigned num_lits, literal const * lits,
                                                           unsigned num_params, parameter* params):
        justification(false),
        m_th_id(fid),
        m_params(num_params, params),
        m_num_literals(num_lits) {
        ast_manager & m   = ctx.get_manager();
        m_literals        = alloc_svect(expr*, num_lits);
        for (unsigned i   = 0; i < num_lits; i++) {
            bool sign     = lits[i].sign();
            expr * v      = ctx.bool_var2expr(lits[i].var());
            m.inc_ref(v);
            m_literals[i] = TAG(expr*, v, sign);
        }
        SASSERT(!in_region());
    }

    theory_lemma_justification::~theory_lemma_justification() {
        SASSERT(!in_region());
        dealloc_svect(m_literals); 
    }
    
    void theory_lemma_justification::del_eh(ast_manager & m) {
        for (unsigned i = 0; i < m_num_literals; i++) {
            m.dec_ref(UNTAG(expr*, m_literals[i]));
        }
        m_params.reset();
    }

    proof * theory_lemma_justification::mk_proof(conflict_resolution & cr) {
        ast_manager & m = cr.get_manager();
        expr_ref_vector lits(m);
        for (unsigned i = 0; i < m_num_literals; i++) {
            bool sign   = GET_TAG(m_literals[i]) != 0;
            expr * v    = UNTAG(expr*, m_literals[i]);
            expr_ref l(m);
            if (sign) 
                l       = m.mk_not(v);
            else
                l       = v;
            lits.push_back(l);
        }
        if (lits.size() == 1)
            return m.mk_th_lemma(m_th_id, lits.get(0), 0, 0, m_params.size(), m_params.c_ptr());
        else
            return m.mk_th_lemma(m_th_id, m.mk_or(lits.size(), lits.c_ptr()), 0, 0, m_params.size(), m_params.c_ptr());
    }

};

