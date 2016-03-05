/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    arith_eq_adapter.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-05-25.

Revision History:

--*/

#include"smt_context.h"
#include"arith_eq_adapter.h"
#include"ast_pp.h"
#include"ast_ll_pp.h"
#include"stats.h"
#include"simplifier.h"
#include"ast_smt2_pp.h"

namespace smt {

    class already_processed_trail : public trail<context> {
        // Remark: it is safer to use a trail object, because it guarantees that the enodes
        // are still alive when the undo operation is performed.
        //
        // If a local backtracking stack is used in the class arith_eq_adapter is used,
        // then we cannot guarantee that.
        arith_eq_adapter::already_processed & m_already_processed;
        enode *                               m_n1;
        enode *                               m_n2;
    public:
        already_processed_trail(arith_eq_adapter::already_processed & m, enode * n1, enode * n2):
            m_already_processed(m),
            m_n1(n1),
            m_n2(n2) {
        }
        
        virtual void undo(context & ctx) {
            m_already_processed.erase(m_n1, m_n2);
            TRACE("arith_eq_adapter_profile", tout << "del #" << m_n1->get_owner_id() << " #" << m_n2->get_owner_id() << "\n";);
        }
    };

    /**
       \brief The atoms m_eq, m_le, and m_ge should be marked as relevant only after
       m_n1 and m_n2 are marked as relevant.
    */
    class arith_eq_relevancy_eh : public relevancy_eh {
        expr * m_n1;
        expr * m_n2;
        expr * m_eq;
        expr * m_le;
        expr * m_ge;
    public:
        arith_eq_relevancy_eh(expr * n1, expr * n2, expr * eq, expr * le, expr * ge):
            m_n1(n1), 
            m_n2(n2),
            m_eq(eq),
            m_le(le),
            m_ge(ge) {
        }

        virtual ~arith_eq_relevancy_eh() {}

        virtual void operator()(relevancy_propagator & rp) {
            if (!rp.is_relevant(m_n1))
                return;
            if (!rp.is_relevant(m_n2))
                return;
            rp.mark_as_relevant(m_eq);
            rp.mark_as_relevant(m_le);
            rp.mark_as_relevant(m_ge);
        }
    };

    void arith_eq_adapter::mk_axioms(enode * n1, enode * n2) {
        SASSERT(n1 != n2);
        ast_manager & m = get_manager();
        TRACE("arith_eq_adapter_mk_axioms", tout << "#" << n1->get_owner_id() << " #" << n2->get_owner_id() << "\n";
              tout << mk_ismt2_pp(n1->get_owner(), m) << "\n" << mk_ismt2_pp(n2->get_owner(), m) << "\n";);
        if (n1->get_owner_id() > n2->get_owner_id())
            std::swap(n1, n2);
        app * t1        = n1->get_owner();
        app * t2        = n2->get_owner();
        if (m.is_value(t1) && m.is_value(t2)) {
            // Nothing to be done
            // We don't need to create axioms for 2 = 3
            return; 
        }
        if (t1 == t2) {
            return;
        }
        
        context & ctx = get_context();
        CTRACE("arith_eq_adapter_relevancy", !(ctx.is_relevant(n1) && ctx.is_relevant(n2)),
               tout << "is_relevant(n1): #" << n1->get_owner_id() << " " << ctx.is_relevant(n1) << "\n";
               tout << "is_relevant(n2): #" << n2->get_owner_id() << " " << ctx.is_relevant(n2) << "\n";
               tout << mk_pp(n1->get_owner(), get_manager()) << "\n";
               tout << mk_pp(n2->get_owner(), get_manager()) << "\n";
               ctx.display(tout););
        //
        // The atoms d.m_t1_eq_t2, d.m_le, and d.m_ge should only be marked as relevant
        // after n1 and n2 are marked as relevant.
        //
        data d;
        if (m_already_processed.find(n1, n2, d))
            return;
        
        TRACE("arith_eq_adapter_profile", tout << "mk #" << n1->get_owner_id() << " #" << n2->get_owner_id() << " " <<
              m_already_processed.size() << " " << ctx.get_scope_level() << "\n";);
        
        m_stats.m_num_eq_axioms++;
        
        TRACE("arith_eq_adapter_profile_detail", 
              tout << "mk_detail " << mk_bounded_pp(n1->get_owner(), m, 5) << " " << 
              mk_bounded_pp(n2->get_owner(), m, 5) << "\n";);
        
        app_ref t1_eq_t2(m);
        
        t1_eq_t2 = ctx.mk_eq_atom(t1, t2);
        SASSERT(!m.is_false(t1_eq_t2));
        
        TRACE("arith_eq_adapter_bug", tout << mk_bounded_pp(t1_eq_t2, m) << "\n" 
              << mk_bounded_pp(t1, m) << "\n"
              << mk_bounded_pp(t2, m) << "\n";);

        // UNRESOLVED ISSUE:
        //
        //   arith_eq_adapter is still creating problems.
        //   The following disabled code fixes the issues, but create performance problems.
        //   The alternative does not works 100%. It generates problems when the literal
        //   created by the adapter during the search is included in a learned clause.
        //   Here is a sequence of events that triggers a crash:
        //      1) The terms t1 >= t2 and t1 <= t2 are not in simplified form.
        //         For example, let us assume t1 := (* -1 x) and t2 := x.
        //         Since, t1 and t2 were internalized at this point, the following code works.
        //         That is the arith internalizer accepts the formula (+ (* -1 x) (* -1 x))
        //         that is not in simplified form. Let s be the term (+ (* -1 x) (* -1 x))
        //      2) Assume now that a conflict is detected a lemma containing s is created.
        //      3) The enodes associated with t1, t2 and s are destroyed during backtracking.
        //      4) The term s is reinternalized at smt::context::reinit_clauses. Term t2 is
        //         also reinitialized, but t1 is not. We only create a "name" for a term (* -1 x)
        //         if it is embedded in a function application.
        //      5) theory_arith fails to internalize (+ (* -1 x) (* -1 x)), and Z3 crashes.
        // 

        // Requires that the theory arithmetic internalizer accept non simplified terms of the form t1 - t2 
        // if t1 and t2 already have slacks (theory variables) associated with them.
        // It also accepts terms with repeated variables (Issue #429).
        app * le = 0;
        app * ge = 0;
        if (m_util.is_numeral(t1))
            std::swap(t1, t2);
        if (m_util.is_numeral(t2)) {
            le = m_util.mk_le(t1, t2);
            ge = m_util.mk_ge(t1, t2);
        }        
        else {
            sort * st       = m.get_sort(t1);
            app_ref minus_one(m_util.mk_numeral(rational::minus_one(), st), m);
            app_ref zero(m_util.mk_numeral(rational::zero(), st), m);
            app_ref t3(m_util.mk_mul(minus_one, t2), m);
            app_ref s(m_util.mk_add(t1, t3), m);
            le              = m_util.mk_le(s, zero);
            ge              = m_util.mk_ge(s, zero);
        }
        TRACE("arith_eq_adapter_perf",
              tout << mk_ismt2_pp(t1_eq_t2, m) << "\n" << mk_ismt2_pp(le, m) << "\n" << mk_ismt2_pp(ge, m) << "\n";);

        ctx.push_trail(already_processed_trail(m_already_processed, n1, n2));
        m_already_processed.insert(n1, n2, data(t1_eq_t2, le, ge));
        TRACE("arith_eq_adapter_profile", tout << "insert #" << n1->get_owner_id() << " #" << n2->get_owner_id() << "\n";);
        ctx.internalize(t1_eq_t2, true); 
        literal t1_eq_t2_lit(ctx.get_bool_var(t1_eq_t2)); 
        TRACE("interface_eq", 
              tout << "core should try true phase first for the equality: " << t1_eq_t2_lit << "\n";
              tout << "#" << n1->get_owner_id() << " == #" << n2->get_owner_id() << "\n";
              tout << "try_true_first: " << ctx.try_true_first(t1_eq_t2_lit.var()) << "\n";);
        TRACE("arith_eq_adapter_bug",
              tout << "le: " << mk_ismt2_pp(le, m) << "\nge: " << mk_ismt2_pp(ge, m) << "\n";);
        ctx.internalize(le, true);
        ctx.internalize(ge, true);
        SASSERT(ctx.lit_internalized(le));
        SASSERT(ctx.lit_internalized(ge));
        literal le_lit = ctx.get_literal(le);
        literal ge_lit = ctx.get_literal(ge);
        if (ctx.try_true_first(t1_eq_t2_lit.var())) {
            // Remark: I need to propagate the try_true_first flag to the auxiliary atom le_lit and ge_lit.
            // Otherwise model based theory combination will be ineffective, because if the core
            // case splits in le_lit and ge_lit before t1_eq_t2_lit it will essentially assign an arbitrary phase to t1_eq_t2_lit.
            ctx.set_true_first_flag(le_lit.var());
            ctx.set_true_first_flag(ge_lit.var());
        }
        theory_id tid = m_owner.get_id();
        if (m.proofs_enabled() && m_proof_hint.empty()) {
            m_proof_hint.push_back(parameter(symbol("triangle-eq")));
        }
        ctx.mk_th_axiom(tid, ~t1_eq_t2_lit, le_lit, m_proof_hint.size(), m_proof_hint.c_ptr());
        ctx.mk_th_axiom(tid, ~t1_eq_t2_lit, ge_lit, m_proof_hint.size(), m_proof_hint.c_ptr());
        ctx.mk_th_axiom(tid, t1_eq_t2_lit, ~le_lit, ~ge_lit, m_proof_hint.size(), m_proof_hint.c_ptr());
        TRACE("arith_eq_adapter", tout << "internalizing: "
              << " " << mk_pp(le, m) << ": " << le_lit 
              << " " << mk_pp(ge, m) << ": " << ge_lit 
              << " " << mk_pp(t1_eq_t2, m) << ": " << t1_eq_t2_lit << "\n";);

        if (m_params.m_arith_add_binary_bounds) {
            TRACE("arith_eq_adapter", tout << "adding binary bounds...\n";);
            ctx.mk_th_axiom(tid, le_lit, ge_lit, 3, m_proof_hint.c_ptr());
        }
        if (ctx.relevancy()) {
            relevancy_eh * eh = ctx.mk_relevancy_eh(arith_eq_relevancy_eh(n1->get_owner(), n2->get_owner(), t1_eq_t2, le, ge));
            ctx.add_relevancy_eh(n1->get_owner(), eh);
            ctx.add_relevancy_eh(n2->get_owner(), eh);
        }
        if (!m_params.m_arith_lazy_adapter && !ctx.at_base_level() && 
            n1->get_iscope_lvl() <= ctx.get_base_level() && n2->get_iscope_lvl() <= ctx.get_base_level()) {
            m_restart_pairs.push_back(enode_pair(n1, n2));
        }
        TRACE("arith_eq_adapter_detail", ctx.display(tout););
    }

    void arith_eq_adapter::new_eq_eh(theory_var v1, theory_var v2) {
        TRACE("arith_eq_adapter", tout << "v" << v1 << " = v" << v2 << " #" << get_enode(v1)->get_owner_id() << " = #" << get_enode(v2)->get_owner_id() << "\n";);
        TRACE("arith_eq_adapter_bug", tout << mk_bounded_pp(get_enode(v1)->get_owner(), get_manager()) << "\n" << mk_bounded_pp(get_enode(v2)->get_owner(), get_manager()) << "\n";);
        mk_axioms(get_enode(v1), get_enode(v2));
    }

    void arith_eq_adapter::new_diseq_eh(theory_var v1, theory_var v2) {
        TRACE("arith_eq_adapter", tout << "v" << v1 << " != v" << v2 << " #" << get_enode(v1)->get_owner_id() << " != #" << get_enode(v2)->get_owner_id() << "\n";);
        mk_axioms(get_enode(v1), get_enode(v2));
    }

    void arith_eq_adapter::init_search_eh() {
        m_restart_pairs.reset();
    }

    void arith_eq_adapter::reset_eh() {
        TRACE("arith_eq_adapter", tout << "reset\n";);
        m_already_processed .reset();
        m_restart_pairs     .reset();
        m_stats             .reset();
    }

    void arith_eq_adapter::restart_eh() { 
        context & ctx = get_context();
        TRACE("arith_eq_adapter", tout << "restart\n";);
        enode_pair_vector tmp(m_restart_pairs);
        enode_pair_vector::iterator it  =  tmp.begin();
        enode_pair_vector::iterator end =  tmp.end();
        m_restart_pairs.reset();
        for (; it != end && !ctx.inconsistent(); ++it) {
            TRACE("arith_eq_adapter", tout << "creating arith_eq_adapter axioms at the base level #" << it->first->get_owner_id() << " #" <<
                  it->second->get_owner_id() << "\n";);
            mk_axioms(it->first, it->second);
        }
    }

    void arith_eq_adapter::collect_statistics(::statistics & st) const {
        st.update("eq adapter", m_stats.m_num_eq_axioms);
    }

    void arith_eq_adapter::display_already_processed(std::ostream & out) const {
        obj_pair_map<enode, enode, data>::iterator it  = m_already_processed.begin();
        obj_pair_map<enode, enode, data>::iterator end = m_already_processed.end();
        for (; it != end; ++it) {
            enode * n1 = it->get_key1();
            enode * n2 = it->get_key2();
            out << "eq_adapter: #" << n1->get_owner_id() << " #" << n2->get_owner_id() << "\n";
        }
    }
};

