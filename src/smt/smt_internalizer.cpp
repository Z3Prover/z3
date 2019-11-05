/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_internalizer.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-20.

Revision History:

--*/
#include "smt/smt_context.h"
#include "ast/expr_stat.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_smt2_pp.h"
#include "smt/smt_model_finder.h"
#include "ast/for_each_expr.h"

namespace smt {

    /**
       \brief Return true if the expression is viewed as a logical gate.
    */
    inline bool is_gate(ast_manager const & m, expr * n) {
        if (is_app(n) && to_app(n)->get_family_id() == m.get_basic_family_id()) {
            switch (to_app(n)->get_decl_kind()) {
            case OP_AND:
            case OP_OR:
            case OP_ITE:
                return true;
            case OP_EQ:
                return m.is_bool(to_app(n)->get_arg(0));
            default:
                return false;
            }
        }
        return false;
    }

#define White 0 
#define Grey  1
#define Black 2

    static int get_color(svector<int> & tcolors, svector<int> & fcolors, expr * n, bool gate_ctx) {
        svector<int> & colors = gate_ctx ? tcolors : fcolors;
        if (colors.size() > n->get_id()) 
            return colors[n->get_id()];
        return White;
    }

    static void set_color(svector<int> & tcolors, svector<int> & fcolors, expr * n, bool gate_ctx, int color) {
       svector<int> & colors = gate_ctx ? tcolors : fcolors;
       if (colors.size() <= n->get_id()) {
           colors.resize(n->get_id()+1, White);
       }
       colors[n->get_id()] = color;
    }

    /**
       \brief Return the foreign descendants of n. That is, the descendants of n where the family_id is different from fid.
       For example the descendants of (+ a (+ (f b) (* 2 (h (+ c d))))) are:
       - a
       - (f b)
       - (h (+ c d))
    */
    static void get_foreign_descendants(app * n, family_id fid, ptr_buffer<expr> & descendants) {
        SASSERT(n->get_family_id() == fid);
        SASSERT(fid != null_family_id);
        ptr_buffer<expr> todo;
        todo.push_back(n);
        ast_mark visited;
        while (!todo.empty()) {
            expr * curr = todo.back();
            todo.pop_back();
            if (visited.is_marked(n)) {
                continue;
            }
            visited.mark(n, true);
            if (!is_app(curr) || to_app(curr)->get_family_id() != fid) {
                descendants.push_back(curr);
                continue;
            }

            SASSERT(is_app(curr));
            SASSERT(to_app(curr)->get_family_id() == fid);
            unsigned j = to_app(curr)->get_num_args();
            while (j > 0) {
                --j;
                todo.push_back(to_app(curr)->get_arg(j));
            }
        }
    }

    void context::ts_visit_child(expr * n, bool gate_ctx, svector<int> & tcolors, svector< int> & fcolors, svector<expr_bool_pair> & todo, bool & visited) {
        if (get_color(tcolors, fcolors, n, gate_ctx) == White) {
            todo.push_back(expr_bool_pair(n, gate_ctx));
            visited = false;
        }
    }

    bool context::ts_visit_children(expr * n, bool gate_ctx, svector<int> & tcolors, svector<int> & fcolors, svector<expr_bool_pair> & todo) {
        if (is_quantifier(n))
            return true;
        SASSERT(is_app(n));
        if (m.is_bool(n)) {
            if (b_internalized(n))
                return true;
        }
        else {
            if (e_internalized(n))
                return true;
        }

        bool visited  = true;
        family_id fid = to_app(n)->get_family_id();
        theory * th   = m_theories.get_plugin(fid);
        bool def_int  = th == nullptr || th->default_internalizer();
        if (!def_int) {
            ptr_buffer<expr> descendants;
            get_foreign_descendants(to_app(n), fid, descendants);
            ptr_buffer<expr>::iterator it  = descendants.begin();
            ptr_buffer<expr>::iterator end = descendants.end();
            for (; it != end; ++it) {
                expr * arg = *it;
                ts_visit_child(arg, false, tcolors, fcolors, todo, visited);
            }
            return visited;
        }

        SASSERT(def_int);

        if (m.is_term_ite(n)) {
            ts_visit_child(to_app(n)->get_arg(0), true, tcolors, fcolors, todo, visited);
            ts_visit_child(to_app(n)->get_arg(1), false, tcolors, fcolors, todo, visited);
            ts_visit_child(to_app(n)->get_arg(2), false, tcolors, fcolors, todo, visited);
            return visited;
        }
        bool new_gate_ctx = m.is_bool(n) && (is_gate(m, n) || m.is_not(n));
        unsigned j = to_app(n)->get_num_args();
        while (j > 0) {
            --j;
            expr * arg = to_app(n)->get_arg(j);
            ts_visit_child(arg, new_gate_ctx, tcolors, fcolors, todo, visited);
        }
        return visited;
    }

    void context::top_sort_expr(expr * n, svector<expr_bool_pair> & sorted_exprs) {
        svector<expr_bool_pair> todo;
        svector<int>      tcolors;
        svector<int>      fcolors;
        todo.push_back(expr_bool_pair(n, true));
        while (!todo.empty()) {
            expr_bool_pair & p = todo.back();
            expr * curr        = p.first;
            bool   gate_ctx    = p.second;
            switch (get_color(tcolors, fcolors, curr, gate_ctx)) {
            case White:
                set_color(tcolors, fcolors, curr, gate_ctx, Grey);
                ts_visit_children(curr, gate_ctx, tcolors, fcolors, todo);
                break;
            case Grey:
                SASSERT(ts_visit_children(curr, gate_ctx, tcolors, fcolors, todo));
                set_color(tcolors, fcolors, curr, gate_ctx, Black);
                if (n != curr && !m.is_not(curr))
                    sorted_exprs.push_back(expr_bool_pair(curr, gate_ctx));
                break;
            case Black:
                todo.pop_back();
                break;
            default:
                UNREACHABLE();
            }
        }
    }

#define DEEP_EXPR_THRESHOLD 1024
 
    /**
       \brief Internalize an expression asserted into the logical context using the given proof as a justification.
       
       \remark pr is 0 if proofs are disabled.
    */
    void context::internalize_assertion(expr * n, proof * pr, unsigned generation) {
        TRACE("internalize_assertion", tout << mk_pp(n, m) << "\n";); 
        TRACE("internalize_assertion_ll", tout << mk_ll_pp(n, m) << "\n";); 
        TRACE("generation", tout << "generation: " << m_generation << "\n";);
        TRACE("incompleteness_bug", tout << "[internalize-assertion]: #" << n->get_id() << "\n";);
        flet<unsigned> l(m_generation, generation);
        m_stats.m_max_generation = std::max(m_generation, m_stats.m_max_generation);
        if (::get_depth(n) > DEEP_EXPR_THRESHOLD) {
            // if the expression is deep, then execute topological sort to avoid
            // stack overflow.
            // a caveat is that theory internalizers do rely on recursive descent so
            // internalization over these follows top-down
            TRACE("deep_internalize", tout << "expression is deep: #" << n->get_id() << "\n" << mk_ll_pp(n, m););
            svector<expr_bool_pair> sorted_exprs;
            top_sort_expr(n, sorted_exprs);
            TRACE("deep_internalize", for (auto & kv : sorted_exprs) tout << "#" << kv.first->get_id() << " " << kv.second << "\n"; );
            for (auto & kv : sorted_exprs) {
                expr* e = kv.first;
                if (!is_app(e) || 
                    to_app(e)->get_family_id() == null_family_id || 
                    to_app(e)->get_family_id() == m.get_basic_family_id()) 
                    internalize(e, kv.second);
            }
        }
        SASSERT(m.is_bool(n));
        if (is_gate(m, n)) {
            switch(to_app(n)->get_decl_kind()) {
            case OP_AND: {
                for (expr * arg : *to_app(n)) {
                    internalize(arg, true);
                    literal lit = get_literal(arg);
                    mk_root_clause(1, &lit, pr);
                }
                break;
            }
            case OP_OR: {
                literal_buffer lits;
                for (expr * arg : *to_app(n)) { 
                    internalize(arg, true);
                    lits.push_back(get_literal(arg));
                }
                mk_root_clause(lits.size(), lits.c_ptr(), pr);
                add_or_rel_watches(to_app(n));
                break;
            }
            case OP_EQ: {
                expr * lhs = to_app(n)->get_arg(0);
                expr * rhs = to_app(n)->get_arg(1);
                internalize(lhs, true);
                internalize(rhs, true);
                literal l1 = get_literal(lhs);
                literal l2 = get_literal(rhs);
                mk_root_clause(l1, ~l2, pr);
                mk_root_clause(~l1, l2, pr);
                break;
            }
            case OP_ITE: {
                expr * c = to_app(n)->get_arg(0);
                expr * t = to_app(n)->get_arg(1);
                expr * e = to_app(n)->get_arg(2);
                internalize(c, true);
                internalize(t, true);
                internalize(e, true);
                literal cl = get_literal(c);
                literal tl = get_literal(t);
                literal el = get_literal(e);
                mk_root_clause(~cl, tl, pr);
                mk_root_clause(cl,  el, pr);
                add_ite_rel_watches(to_app(n));
                break;
            }
            default:
                UNREACHABLE();
            }
            mark_as_relevant(n);
        }
        else if (m.is_distinct(n)) {
            assert_distinct(to_app(n), pr);
            mark_as_relevant(n);
        }
        else {
            assert_default(n, pr);
        }
    }

    void context::assert_default(expr * n, proof * pr) {
        internalize(n, true);
        literal l = get_literal(n);
        if (l == false_literal) {
            set_conflict(mk_justification(justification_proof_wrapper(*this, pr)));
        }
        else {
            justification* j = mk_justification(justification_proof_wrapper(*this, pr));
            m_clause_proof.add(l, CLS_AUX, j);
            assign(l, j);
            mark_as_relevant(l);
        }
    }

#define DISTINCT_SZ_THRESHOLD 32

    void context::assert_distinct(app * n, proof * pr) {
        TRACE("assert_distinct", tout << mk_pp(n, m) << "\n";);
        unsigned num_args = n->get_num_args();
        if (num_args == 0 || num_args <= DISTINCT_SZ_THRESHOLD || m.proofs_enabled()) {
            assert_default(n, pr);
            return;
        }
        sort * s = m.get_sort(n->get_arg(0));
        sort_ref u(m.mk_fresh_sort("distinct-elems"), m);
        func_decl_ref f(m.mk_fresh_func_decl("distinct-aux-f", "", 1, &s, u), m);
        for (expr * arg : *n) {
            app_ref fapp(m.mk_app(f, arg), m);
            app_ref val(m.mk_fresh_const("unique-value", u), m);
            enode * e   = mk_enode(val, false, false, true);
            e->mark_as_interpreted();
            app_ref eq(m.mk_eq(fapp, val), m);
            TRACE("assert_distinct", tout << "eq: " << mk_pp(eq, m) << "\n";);
            assert_default(eq, nullptr);
            mark_as_relevant(eq.get());
            // TODO: we may want to hide the auxiliary values val and the function f from the model.
        }
    }

    void context::internalize(expr * n, bool gate_ctx, unsigned generation) {
        flet<unsigned> l(m_generation, generation);
        m_stats.m_max_generation = std::max(m_generation, m_stats.m_max_generation);
        internalize(n, gate_ctx);
    }

    void context::ensure_internalized(expr* e) {
        if (!e_internalized(e)) {
            internalize(e, false);
        }
    }

    /**
       \brief Internalize the given expression into the logical context.
       
       - gate_ctx is true if the expression is in the context of a logical gate.
    */
    void context::internalize(expr * n, bool gate_ctx) {
        TRACE("internalize", tout << "internalizing:\n" << mk_pp(n, m) << "\n";);
        TRACE("internalize_bug", tout << "internalizing:\n" << mk_bounded_pp(n, m) << "\n";);
        if (is_var(n)) {
            throw default_exception("Formulas should not contain unbound variables");
        }
        if (m.is_bool(n)) {
            SASSERT(is_quantifier(n) || is_app(n));
            internalize_formula(n, gate_ctx);
        }
        else if (is_lambda(n)) {
            internalize_lambda(to_quantifier(n));
        }
        else {
            SASSERT(is_app(n));
            SASSERT(!gate_ctx);
            internalize_term(to_app(n));
        }
    }


    /**
       \brief Internalize the given formula into the logical context.
    */
    void context::internalize_formula(expr * n, bool gate_ctx) {
        TRACE("internalize_bug", tout << "internalize formula: #" << n->get_id() << ", gate_ctx: " << gate_ctx << "\n" << mk_pp(n, m) << "\n";);
        SASSERT(m.is_bool(n));
        if (m.is_true(n) || m.is_false(n))
            return;

        if (m.is_not(n) && gate_ctx) {
            // a boolean variable does not need to be created if n a NOT gate is in
            // the context of a gate.
            internalize(to_app(n)->get_arg(0), true);
            return;
        }

        if (b_internalized(n)) {
            // n was already internalized as a boolean.
            bool_var v = get_bool_var(n);
            TRACE("internalize_bug", tout << "#" << n->get_id() << " already has bool_var v" << v << "\n";);
            
            // n was already internalized as boolean, but an enode was
            // not associated with it.  So, an enode is necessary, if
            // n is not in the context of a gate and is an application.
            if (!gate_ctx && is_app(n)) {
                if (e_internalized(n)) {
                    TRACE("internalize_bug", tout << "forcing enode #" << n->get_id() << " to merge with t/f\n";);
                    enode * e = get_enode(to_app(n));
                    set_merge_tf(e, v, false);
                }
                else {
                    TRACE("internalize_bug", tout << "creating enode for #" << n->get_id() << "\n";);
                    mk_enode(to_app(n), 
                             true, /* suppress arguments, we not not use CC for this kind of enode */
                             true, /* bool enode must be merged with true/false, since it is not in the context of a gate */
                             false /* CC is not enabled */ );
                    set_enode_flag(v, false);
                    if (get_assignment(v) != l_undef)
                        propagate_bool_var_enode(v);
                }
                SASSERT(has_enode(v));
            }
            return;
        }

        if (m.is_eq(n) && !m.is_iff(n))
            internalize_eq(to_app(n), gate_ctx);
        else if (m.is_distinct(n))
            internalize_distinct(to_app(n), gate_ctx);
        else if (is_app(n) && internalize_theory_atom(to_app(n), gate_ctx))
            return;
        else if (is_quantifier(n)) 
            internalize_quantifier(to_quantifier(n), gate_ctx);
        else
            internalize_formula_core(to_app(n), gate_ctx);
    }

    /**
       \brief Internalize an equality.
    */
    void context::internalize_eq(app * n, bool gate_ctx) {
        TRACE("internalize", tout << mk_pp(n, m) << "\n";);
        SASSERT(!b_internalized(n));
        SASSERT(m.is_eq(n));
        internalize_formula_core(n, gate_ctx);
        bool_var v        = get_bool_var(n);
        bool_var_data & d = get_bdata(v);
        d.set_eq_flag();
        
        sort * s    = m.get_sort(n->get_arg(0));
        theory * th = m_theories.get_plugin(s->get_family_id());
        if (th)
            th->internalize_eq_eh(n, v);
    }

    /**
       \brief Internalize distinct constructor.
    */
    void context::internalize_distinct(app * n, bool gate_ctx) {
        TRACE("distinct", tout << "internalizing distinct: " << mk_pp(n, m) << "\n";);
        SASSERT(!b_internalized(n));
        SASSERT(m.is_distinct(n));
        expr_ref def(m.mk_distinct_expanded(n->get_num_args(), n->get_args()), m);
        internalize(def, true);
        bool_var v    = mk_bool_var(n);
        literal l(v);
        literal l_def = get_literal(def);
        mk_gate_clause(~l, l_def);
        mk_gate_clause(l, ~l_def);
        add_relevancy_dependency(n, def);
        if (!gate_ctx) {
            mk_enode(n, true, true, false);
            set_enode_flag(v, true);
            SASSERT(get_assignment(v) == l_undef);
        }
    }

    /** 
        \brief Try to internalize n as a theory atom. Return true if succeeded.
        The application can be internalize as a theory atom, if there is a theory (plugin)
        that can internalize n.
    */
    bool context::internalize_theory_atom(app * n, bool gate_ctx) {
        SASSERT(!b_internalized(n));
        theory * th  = m_theories.get_plugin(n->get_family_id());
        TRACE("datatype_bug", tout << "internalizing theory atom:\n" << mk_pp(n, m) << "\n";);
        if (!th || !th->internalize_atom(n, gate_ctx))
            return false;
        TRACE("datatype_bug", tout << "internalization succeeded\n" << mk_pp(n, m) << "\n";);
        SASSERT(b_internalized(n));
        TRACE("internalize_theory_atom", tout << "internalizing theory atom: #" << n->get_id() << "\n";);
        bool_var v        = get_bool_var(n);
        if (!gate_ctx) {
            // if the formula is not in the context of a gate, then it
            // must be associated with an enode.
            if (!e_internalized(n)) {
                mk_enode(to_app(n), 
                         true, /* suppress arguments, we not not use CC for this kind of enode */
                         true  /* bool enode must be merged with true/false, since it is not in the context of a gate */,
                         false /* CC is not enabled */);
            }
            else {
                SASSERT(e_internalized(n));
                enode * e = get_enode(n);
                set_enode_flag(v, true);
                set_merge_tf(e, v, true);
            }
        }
        if (e_internalized(n)) {
            set_enode_flag(v, true);
            if (get_assignment(v) != l_undef)
                propagate_bool_var_enode(v);
        }
        SASSERT(!e_internalized(n) || has_enode(v));
        return true;
    }

#ifdef Z3DEBUG
    struct check_pattern_proc {
        void operator()(var * v) {}
        void operator()(quantifier * q) {}
        void operator()(app * n) {
            if (is_ground(n))
                return;
            SASSERT(n->get_decl()->is_flat_associative() || n->get_num_args() == n->get_decl()->get_arity());
        }
    };
    
    /**
       Debugging code: check whether for all (non-ground) applications (f a_1 ... a_n) in t, f->get_arity() == n
    */
    static bool check_pattern(expr * t) {
        check_pattern_proc p;
        for_each_expr(p, t);
        return true;
    }

    static bool check_patterns(quantifier * q) {
        for (unsigned i = 0; i < q->get_num_patterns(); i++) {
            SASSERT(check_pattern(q->get_pattern(i)));
        }
        for (unsigned i = 0; i < q->get_num_no_patterns(); i++) {
            SASSERT(check_pattern(q->get_no_pattern(i)));
        }
        return true;
    }
#endif
    
    /**
       \brief Internalize the given quantifier into the logical
       context. 
    */
    void context::internalize_quantifier(quantifier * q, bool gate_ctx) {
        TRACE("internalize_quantifier", tout << mk_pp(q, m) << "\n";);
        CTRACE("internalize_quantifier_zero", q->get_weight() == 0, tout << mk_pp(q, m) << "\n";);
        SASSERT(gate_ctx); // limitation of the current implementation
        SASSERT(!b_internalized(q));
        SASSERT(is_forall(q));
        SASSERT(check_patterns(q));
        bool_var v             = mk_bool_var(q);
        unsigned generation    = m_generation;
        unsigned _generation;
        if (!m_cached_generation.empty() && m_cached_generation.find(q, _generation)) {
            generation = _generation;
        }
        // TODO: do we really need this flag?
        bool_var_data & d      = get_bdata(v);
        d.set_quantifier_flag();
        m_qmanager->add(q, generation);
    }

    void context::internalize_lambda(quantifier * q) {
        TRACE("internalize_quantifier", tout << mk_pp(q, m) << "\n";);
        SASSERT(is_lambda(q));
        app_ref lam_name(m.mk_fresh_const("lambda", m.get_sort(q)), m);
        app_ref eq(m), lam_app(m);
        expr_ref_vector vars(m);
        vars.push_back(lam_name);
        unsigned sz = q->get_num_decls();
        for (unsigned i = 0; i < sz; ++i) {
            vars.push_back(m.mk_var(sz - i - 1, q->get_decl_sort(i)));
        }
        array_util autil(m);
        lam_app = autil.mk_select(vars.size(), vars.c_ptr());
        eq = m.mk_eq(lam_app, q->get_expr());
        quantifier_ref fa(m);
        expr * patterns[1] = { m.mk_pattern(lam_app) };
        fa = m.mk_forall(sz, q->get_decl_sorts(), q->get_decl_names(), eq, 0, m.lambda_def_qid(), symbol::null, 1, patterns);
        internalize_quantifier(fa, true);
        if (!e_internalized(lam_name)) internalize_uninterpreted(lam_name);
        m_app2enode.setx(q->get_id(), get_enode(lam_name), nullptr);
    }

    /**
       \brief Internalize gates and (uninterpreted and equality) predicates.
    */
    void context::internalize_formula_core(app * n, bool gate_ctx) {
        SASSERT(!b_internalized(n));
        SASSERT(!e_internalized(n));

        CTRACE("resolve_conflict_crash", m.is_not(n), tout << mk_ismt2_pp(n, m) << "\ngate_ctx: " << gate_ctx << "\n";);

        bool _is_gate  = is_gate(m, n) || m.is_not(n);
        // process args
        for (expr * arg : *n) {
            internalize(arg, _is_gate);
        }
        
        CTRACE("internalize_bug", b_internalized(n), tout << mk_ll_pp(n, m) << "\n";);
        
        bool is_new_var = false;
        bool_var v;
        // n can be already internalized after its children are internalized.
        // Example (ite-term): (= (ite c 1 0) 1)
        // 
        // When (ite c 1 0) is internalized, it will force the internalization of (= (ite c 1 0) 1) and (= (ite c 1 0) 0)
        //
        // TODO: avoid the problem by delaying the internalization of (= (ite c 1 0) 1) and (= (ite c 1 0) 0).
        // Add them to a queue.
        if (!b_internalized(n)) {
            is_new_var  = true;
            v = mk_bool_var(n);
        }
        else {
            v = get_bool_var(n);
        }

        // a formula needs to be associated with an enode when:
        // 1) it is not in the context of a gate, or
        // 2) it has arguments and it is not a gate (i.e., uninterpreted predicate or equality).
        if (!e_internalized(n) && (!gate_ctx || (!_is_gate && n->get_num_args() > 0))) {
            bool suppress_args = _is_gate || m.is_not(n);
            bool merge_tf      = !gate_ctx;
            mk_enode(n, suppress_args, merge_tf, true);
            set_enode_flag(v, is_new_var);
            SASSERT(has_enode(v));
        }

        // The constraints associated with node 'n' should be asserted
        // after the bool_var and enode associated with are created.
        // Reason: incompleteness. An assigned boolean variable is only inserted
        // in m_atom_propagation_queue if the predicate is_atom() is true.
        // When the constraints for n are created, they may force v to be assigned.
        // Now, if v is assigned before being associated with an enode, then
        // v is not going to be inserted in m_atom_propagation_queue, and
        // propagate_bool_var_enode() method is not going to be invoked for v.
        if (is_new_var && n->get_family_id() == m.get_basic_family_id()) {
            switch (n->get_decl_kind()) {
            case OP_NOT:
                SASSERT(!gate_ctx);
                mk_not_cnstr(to_app(n));
                break;
            case OP_AND:
                mk_and_cnstr(to_app(n));
                add_and_rel_watches(to_app(n));
                break;
            case OP_OR:
                mk_or_cnstr(to_app(n));
                add_or_rel_watches(to_app(n));
                break;
            case OP_EQ:
                if (m.is_iff(n))
                    mk_iff_cnstr(to_app(n));
                break;
            case OP_ITE:
                mk_ite_cnstr(to_app(n));
                add_ite_rel_watches(to_app(n));
                break;
            case OP_TRUE:
            case OP_FALSE:
                break;
            case OP_DISTINCT:
            case OP_IMPLIES:
            case OP_XOR:
                UNREACHABLE();
            case OP_OEQ:
                UNREACHABLE();
            default:
                break;
            }
        }
        
        CTRACE("internalize_bug", e_internalized(n), 
               tout << "#" << n->get_id() << ", merge_tf: " << get_enode(n)->merge_tf() << "\n";);
    }

    /**
       \brief Trail object to disable the m_merge_tf flag of an enode.
    */
    class set_merge_tf_trail : public trail<context> {
        enode * m_node;
    public:
        set_merge_tf_trail(enode * n):
            m_node(n) {
        }
        void undo(context & ctx) override {
            m_node->m_merge_tf = false;
        }
    };

    /**
       \brief Enable the flag m_merge_tf in the given enode.  When the
       flag m_merge_tf is enabled, the enode n will be merged with the
       true_enode (false_enode) whenever the Boolean variable v is
       assigned to true (false).

       If is_new_var is true, then trail is not created for the flag update.
    */
    void context::set_merge_tf(enode * n, bool_var v, bool is_new_var) {
        SASSERT(bool_var2enode(v) == n);
        if (!n->m_merge_tf) {
            if (!is_new_var)
                push_trail(set_merge_tf_trail(n));
            n->m_merge_tf = true;
            lbool val = get_assignment(v); 
            switch (val) {
            case l_undef: 
                break;
            case l_true: 
                if (n->get_root() != m_true_enode->get_root()) 
                    push_eq(n, m_true_enode, eq_justification(literal(v, false))); 
                break;
            case l_false: 
                if (n->get_root() != m_false_enode->get_root()) 
                    push_eq(n, m_false_enode, eq_justification(literal(v, true))); 
                break;
            }
        }
    }

    /**
       \brief Trail object to disable the m_enode flag of a Boolean
       variable. The flag m_enode is true for a Boolean variable v,
       if there is an enode n associated with it.
    */
    class set_enode_flag_trail : public trail<context> {
        bool_var m_var;
    public:
        set_enode_flag_trail(bool_var v):
            m_var(v) {
        }
        void undo(context & ctx) override {
            bool_var_data & data = ctx.m_bdata[m_var];
            data.reset_enode_flag();
        }
    };

    /**
       \brief Enable the flag m_enode in the given boolean variable. That is,
       the boolean variable is associated with an enode.

       If is_new_var is true, then trail is not created for the flag uodate.
    */
    void context::set_enode_flag(bool_var v, bool is_new_var) {
        SASSERT(e_internalized(bool_var2expr(v)));
        bool_var_data & data = m_bdata[v];
        if (!data.is_enode()) {
            if (!is_new_var)
                push_trail(set_enode_flag_trail(v));
            data.set_enode_flag();
        }
    }

    /**
       \brief Internalize the given term into the logical context.
    */
    void context::internalize_term(app * n) {
        if (e_internalized(n)) {
            theory * th = m_theories.get_plugin(n->get_family_id());
            if (th != nullptr) {
                // This code is necessary because some theories may decide
                // not to create theory variables for a nested application.
                // Example:
                //   Suppose (+ (* 2 x) y) is internalized by arithmetic
                //   and an enode is created for the + and * applications,
                //   but a theory variable is only created for the + application.
                //   The (* 2 x) is internal to the arithmetic module.
                //   Later, the core tries to internalize (f (* 2 x)).
                //   Now, (* 2 x) is not internal to arithmetic anymore,
                //   and a theory variable must be created for it.
                enode * e = get_enode(n);
                if (!th->is_attached_to_var(e))
                    internalize_theory_term(n);
            }
            return;
        }

        if (m.is_term_ite(n)) {
            internalize_ite_term(n);
            return; // it is not necessary to apply sort constraint
        }
        else if (internalize_theory_term(n)) {
            // skip
        }
        else {
            internalize_uninterpreted(n);
        }
        SASSERT(e_internalized(n));
        enode * e = get_enode(n);
        apply_sort_cnstr(n, e);
    }

    /**
       \brief Internalize an if-then-else term.
    */
    void context::internalize_ite_term(app * n) {
        SASSERT(!e_internalized(n));
        expr * c  = n->get_arg(0);
        expr * t  = n->get_arg(1);
        expr * e  = n->get_arg(2);
        app_ref eq1(mk_eq_atom(n, t), m);
        app_ref eq2(mk_eq_atom(n, e), m);
        mk_enode(n, 
                 true /* suppress arguments, I don't want to apply CC on ite terms */,
                 false /* it is a term, so it should not be merged with true/false */,
                 false /* CC is not enabled */);
        internalize(c, true);
        internalize(t, false);
        internalize(e, false);
        internalize(eq1, true);
        internalize(eq2, true);
        literal c_lit   = get_literal(c);
        literal eq1_lit = get_literal(eq1);
        literal eq2_lit = get_literal(eq2);
        TRACE("internalize_ite_term_bug",
              tout << mk_ismt2_pp(n, m) << "\n";
              tout << mk_ismt2_pp(c, m) << "\n";
              tout << mk_ismt2_pp(t, m) << "\n";
              tout << mk_ismt2_pp(e, m) << "\n";              
              tout << mk_ismt2_pp(eq1, m) << "\n";              
              tout << mk_ismt2_pp(eq2, m) << "\n";              
              tout << "literals:\n" << c_lit << " " << eq1_lit << " " << eq2_lit << "\n";);
        mk_gate_clause(~c_lit, eq1_lit);
        mk_gate_clause( c_lit, eq2_lit);
        if (relevancy()) {
            relevancy_eh * eh = m_relevancy_propagator->mk_term_ite_relevancy_eh(n, eq1, eq2);
            TRACE("ite_term_relevancy", tout << "#" << n->get_id() << " #" << eq1->get_id() << " #" << eq2->get_id() << "\n";);
            add_rel_watch(c_lit, eh);
            add_rel_watch(~c_lit, eh);
            add_relevancy_eh(n, eh);
        }
        SASSERT(e_internalized(n));
    }

    /** 
        \brief Try to internalize a theory term. That is, a theory (plugin)
        will be invoked to internalize n. Return true if succeeded.
        
        It may fail because there is no plugin or the plugin does not support it.
    */
    bool context::internalize_theory_term(app * n) {
        theory * th  = m_theories.get_plugin(n->get_family_id());
        if (!th || !th->internalize_term(n))
            return false;
        return true;
    }

    /**
       \brief Internalize an uninterpreted function application or constant.
    */
    void context::internalize_uninterpreted(app * n) {
        SASSERT(!e_internalized(n));
        // process args
        for (expr * arg : *n) {
            internalize(arg, false);
            SASSERT(e_internalized(arg));
        }
        
        enode * e = mk_enode(n, 
                             false, /* do not suppress args */
                             false, /* it is a term, so it should not be merged with true/false */
                             true);
        apply_sort_cnstr(n, e);
    }

    /**
       \brief Create a new boolean variable and associate it with n.
    */
    bool_var context::mk_bool_var(expr * n) {
        SASSERT(!b_internalized(n));
        //SASSERT(!m.is_not(n));
        unsigned id = n->get_id();
        bool_var v  = m_b_internalized_stack.size();
#ifndef _EXTERNAL_RELEASE 
        if (m_fparams.m_display_bool_var2expr) {
            char const * header = "(iff z3@";
            int  id_sz = 6;
            std::cerr.width(id_sz);
            std::cerr << header << std::left << v << " " << mk_pp(n, m, static_cast<unsigned>(strlen(header)) + id_sz + 1) << ")\n";
        }
        if (m_fparams.m_display_ll_bool_var2expr) {
            std::cerr << v << " ::=\n" << mk_ll_pp(n, m) << "<END-OF-FORMULA>\n";
        }
#endif
        TRACE("mk_bool_var", tout << "creating boolean variable: " << v << " for:\n" << mk_pp(n, m) << " " << n->get_id() << "\n";);
        TRACE("mk_var_bug", tout << "mk_bool: " << v << "\n";);                
        set_bool_var(id, v);
        m_bdata.reserve(v+1);
        m_activity.reserve(v+1);
        m_bool_var2expr.reserve(v+1);
        m_bool_var2expr[v] = n;
        literal l(v, false);
        literal not_l(v, true);
        unsigned aux = std::max(l.index(), not_l.index()) + 1;
        m_assignment.reserve(aux);
        m_assignment[l.index()]     = l_undef;
        m_assignment[not_l.index()] = l_undef;
        m_watches.reserve(aux);
        SASSERT(m_assignment.size() == m_watches.size());
        m_watches[l.index()]        .reset();
        m_watches[not_l.index()]    .reset();
        if (lit_occs_enabled()) {
            m_lit_occs.reserve(aux);
            m_lit_occs[l.index()]     .reset();
            m_lit_occs[not_l.index()] .reset();
        }
        bool_var_data & data = m_bdata[v];
        unsigned iscope_lvl = m_scope_lvl; // record when the boolean variable was internalized.
        data.init(iscope_lvl); 
        if (m_fparams.m_random_initial_activity == IA_RANDOM || (m_fparams.m_random_initial_activity == IA_RANDOM_WHEN_SEARCHING && m_searching))
            m_activity[v]      = -((m_random() % 1000) / 1000.0); 
        else
            m_activity[v]      = 0.0;
        m_case_split_queue->mk_var_eh(v);
        m_b_internalized_stack.push_back(n);
        m_trail_stack.push_back(&m_mk_bool_var_trail);
        m_stats.m_num_mk_bool_var++;
        SASSERT(check_bool_var_vector_sizes());
        return v;
    }
    
    void context::undo_mk_bool_var() {
        SASSERT(!m_b_internalized_stack.empty());
        m_stats.m_num_del_bool_var++;
        expr * n              = m_b_internalized_stack.back();
        unsigned n_id         = n->get_id();
        bool_var v            = get_bool_var_of_id(n_id);
        m_bool_var2expr[v]    = nullptr;
        TRACE("undo_mk_bool_var", tout << "undo_bool: " << v << "\n" << mk_pp(n, m) << "\n" << "m_bdata.size: " << m_bdata.size()
              << " m_assignment.size: " << m_assignment.size() << "\n";);
        TRACE("mk_var_bug", tout << "undo_mk_bool: " << v << "\n";);
        // bool_var_data & d     = m_bdata[v];
        m_case_split_queue->del_var_eh(v);
        if (is_quantifier(n))
            m_qmanager->del(to_quantifier(n));
        set_bool_var(n_id, null_bool_var);
        m_b_internalized_stack.pop_back();
    }

    /**
       \brief Create an new enode. 

       \remark If suppress_args is true, then the enode is viewed as a constant
       in the egraph.
    */
    enode * context::mk_enode(app * n, bool suppress_args, bool merge_tf, bool cgc_enabled) {
        TRACE("mk_enode_detail", tout << mk_pp(n, m) << "\nsuppress_args: " << suppress_args << ", merge_tf: " << 
              merge_tf << ", cgc_enabled: " << cgc_enabled << "\n";);
        SASSERT(!e_internalized(n));
        unsigned id          = n->get_id();
        unsigned generation  = m_generation;
        unsigned _generation = 0;
        if (!m_cached_generation.empty() && m_cached_generation.find(n, _generation)) {
            generation = _generation;
            CTRACE("cached_generation", generation != m_generation,
                   tout << "cached_generation: #" << n->get_id() << " " << generation << " " << m_generation << "\n";);
        }
        enode * e           = enode::mk(m, m_region, m_app2enode, n, generation, suppress_args, merge_tf, m_scope_lvl, cgc_enabled, true);
        TRACE("mk_enode_detail", tout << "e.get_num_args() = " << e->get_num_args() << "\n";);
        if (n->get_num_args() == 0 && m.is_unique_value(n))
            e->mark_as_interpreted();
        TRACE("mk_var_bug", tout << "mk_enode: " << id << "\n";);
        TRACE("generation", tout << "mk_enode: " << id << " " << generation << "\n";);
        m_app2enode.setx(id, e, nullptr);
        m_e_internalized_stack.push_back(n);
        m_trail_stack.push_back(&m_mk_enode_trail);
        m_enodes.push_back(e);
        if (e->get_num_args() > 0) {
            if (e->is_true_eq()) {
                bool_var v = enode2bool_var(e);
                assign(literal(v), mk_justification(eq_propagation_justification(e->get_arg(0), e->get_arg(1))));
                e->m_cg    = e;
            }
            else {
                if (cgc_enabled) {
                    enode_bool_pair pair = m_cg_table.insert(e);
                    enode * e_prime      = pair.first;
                    if (e != e_prime) {
                        e->m_cg = e_prime;
                        bool used_commutativity = pair.second;
                        push_new_congruence(e, e_prime, used_commutativity);
                    }
                    else {
                        e->m_cg = e;
                    }
                }
                else {
                    e->m_cg = e;
                }
            }
            if (!e->is_eq()) {
                unsigned decl_id = n->get_decl()->get_decl_id();
                if (decl_id >= m_decl2enodes.size())
                    m_decl2enodes.resize(decl_id+1);
                m_decl2enodes[decl_id].push_back(e);
            }
        }
        SASSERT(e_internalized(n));
        m_stats.m_num_mk_enode++;
        TRACE("mk_enode", tout << "created enode: #" << e->get_owner_id() << " for:\n" << mk_pp(n, m) << "\n";
              if (e->get_num_args() > 0) {
                  tout << "is_true_eq: " << e->is_true_eq() << " in cg_table: " << m_cg_table.contains_ptr(e) << " is_cgr: " 
                       << e->is_cgr() << "\n";
              });

        if (m.has_trace_stream())
            m.trace_stream() << "[attach-enode] #" << n->get_id() << " " << m_generation << "\n";        

        return e;
    }

    void context::undo_mk_enode() {
        SASSERT(!m_e_internalized_stack.empty());
        m_stats.m_num_del_enode++;
        expr * n              = m_e_internalized_stack.back();
        TRACE("undo_mk_enode", tout << "undo_enode: #" << n->get_id() << "\n" << mk_pp(n, m) << "\n";);
        TRACE("mk_var_bug", tout << "undo_mk_enode: " << n->get_id() << "\n";);
        unsigned n_id         = n->get_id();
        SASSERT(is_app(n));
        enode * e             = m_app2enode[n_id];
        m_app2enode[n_id]     = 0;
        if (e->is_cgr() && !e->is_true_eq() && e->is_cgc_enabled()) {
            SASSERT(m_cg_table.contains_ptr(e));
            m_cg_table.erase(e);
        }
        if (e->get_num_args() > 0 && !e->is_eq()) {
            unsigned decl_id = to_app(n)->get_decl()->get_decl_id();
            SASSERT(decl_id < m_decl2enodes.size());
            SASSERT(m_decl2enodes[decl_id].back() == e);
            m_decl2enodes[decl_id].pop_back();
        }
        e->del_eh(m);
        SASSERT(m_e_internalized_stack.size() == m_enodes.size());
        m_enodes.pop_back();
        m_e_internalized_stack.pop_back();
    }

    /**
       \brief Apply sort constraints on e.
    */
    void context::apply_sort_cnstr(app * term, enode * e) {
        sort * s    = term->get_decl()->get_range();
        theory * th = m_theories.get_plugin(s->get_family_id());
        if (th) {
            th->apply_sort_cnstr(e, s);
        }
    }

    /**
       \brief Return the literal associated with n.
    */
    literal context::get_literal(expr * n) const {
        if (m.is_not(n)) {
            CTRACE("get_literal_bug", !b_internalized(to_app(n)->get_arg(0)), tout << mk_ll_pp(n, m) << "\n";);
            SASSERT(b_internalized(to_app(n)->get_arg(0)));
            return literal(get_bool_var(to_app(n)->get_arg(0)), true);
        }
        else if (m.is_true(n)) {
            return true_literal;
        }
        else if (m.is_false(n)) {
            return false_literal;
        }
        else {
            SASSERT(b_internalized(n));
            return literal(get_bool_var(n), false);
        }
    }

    /**
       \brief Simplify the literals of an auxiliary clause. An
       auxiliary clause is transient. So, the current assignment can
       be used for simplification.

       The following simplifications are applied:

       - Duplicates are removed.
       
       - Literals assigned to false are removed
       
       - If l and ~l are in lits, then return false (the clause is equivalent to true)

       - If a literal in source is assigned to true, then return false.

       \remark The removed literals are stored in simp_lits
       
       It is safe to use the current assignment to simplify aux
       clauses because they are deleted during backtracking.
    */
    bool context::simplify_aux_clause_literals(unsigned & num_lits, literal * lits, literal_buffer & simp_lits) {
        std::sort(lits, lits + num_lits);
        literal prev = null_literal;
        unsigned j = 0;
        for (unsigned i = 0; i < num_lits; i++) {
            literal curr = lits[i];
            lbool   val  = get_assignment(curr);
            switch(val) {
            case l_false:
                TRACE("simplify_aux_clause_literals", display_literal(tout << get_assign_level(curr) << " " << get_scope_level() << " ", curr); tout << "\n"; );
                simp_lits.push_back(~curr);
                break; // ignore literal                
                // fall through
            case l_undef:
                if (curr == ~prev)
                    return false; // clause is equivalent to true
                if (curr != prev) {
                    prev = curr;
                    if (i != j)
                        lits[j] = lits[i];
                    j++;
                }
                break;
            case l_true:
                return false; // clause is equivalent to true
            }
        }
        num_lits = j;
        return true;
    }

    /**
       \brief Simplify the literals of an auxiliary lemma. An
       auxiliary lemma has the status of a learned clause, but it is
       not created by conflict resolution.  

       A dynamic ackermann clause is an example of auxiliary lemma.

       The following simplifications are applied:

       - Duplicates are removed.
       
       - If a literal is assigned to true at a base level, then return
         false (the clause is equivalent to true).
       
       - If l and ~l are in lits, then return false (source is
         irrelevant, that is, it is equivalent to true)

       \remark Literals assigned to false at the base level are not
       removed because I don't want to create a justification for this
       kind of simplification.
    */
    bool context::simplify_aux_lemma_literals(unsigned & num_lits, literal * lits) {
        TRACE("simplify_aux_lemma_literals", tout << "1) "; display_literals(tout, num_lits, lits); tout << "\n";);
        std::sort(lits, lits + num_lits);
        TRACE("simplify_aux_lemma_literals", tout << "2) "; display_literals(tout, num_lits, lits); tout << "\n";);
        literal prev = null_literal;
        unsigned i = 0;
        unsigned j = 0;
        for (; i < num_lits; i++) {
            literal curr = lits[i];
            bool_var var = curr.var();
            lbool   val  = l_undef;
            if (get_assign_level(var) <= m_base_lvl)
                val = get_assignment(curr);
            if (val == l_true)
                return false; // clause is equivalent to true
            if (curr == ~prev)
                return false; // clause is equivalent to true
            if (curr != prev) {
                prev = curr;
                if (i != j)
                    lits[j] = lits[i];
                j++;
            }
        }
        num_lits = j;
        TRACE("simplify_aux_lemma_literals", tout << "3) "; display_literals(tout, num_lits, lits); tout << "\n";);
        return true;
    }
    
    /**
       \brief A clause (lemma or aux lemma) may need to be reinitialized for two reasons:

       1) Lemmas and aux lemmas may contain literals that were created during the search,
       and the maximum internalization scope level of its literals is scope_lvl.
       Since the clauses may remain alive when scope_lvl is backtracked, it must
       be reinitialised. In this case, reinitialize_atoms must be true.
     
       2) An aux lemma is in conflict or propagated a literal when it was created.
       Then, we should check whether the aux lemma is still in conflict or propagating
       a literal after backtracking the current scope level.
    */
    void context::mark_for_reinit(clause * cls, unsigned scope_lvl, bool reinternalize_atoms) {
        SASSERT(scope_lvl >= m_base_lvl);
        cls->m_reinit              = true;
        cls->m_reinternalize_atoms = reinternalize_atoms;
        if (scope_lvl >= m_clauses_to_reinit.size()) 
            m_clauses_to_reinit.resize(scope_lvl+1, clause_vector());
        m_clauses_to_reinit[scope_lvl].push_back(cls);
    }

    /**
       \brief Return max({ get_intern_level(var) | var \in lits })
    */
    unsigned context::get_max_iscope_lvl(unsigned num_lits, literal const * lits) const {
        unsigned r = 0;
        for (unsigned i = 0; i < num_lits; i++) {
            unsigned ilvl = get_intern_level(lits[i].var());
            if (ilvl > r)
                r = ilvl;
        }
        return r;
    }

    /**
       \brief Return true if it safe to use the binary clause optimization at this point in time.
    */
    bool context::use_binary_clause_opt(literal l1, literal l2, bool lemma) const {
        if (!binary_clause_opt_enabled())
            return false;
        // When relevancy is enable binary clauses should not be used.
        // Reason: when a learned clause becomes unit, it should mark the
        // unit literal as relevant. When binary_clause_opt is used,
        // it is not possible to distinguish between learned and non-learned clauses.
        if (lemma && m_fparams.m_relevancy_lvl >= 2)
            return false; 
        if (m_base_lvl > 0)
            return false;
        if (!lemma && m_scope_lvl > 0)
            return false;
        if (get_intern_level(l1.var()) > 0)
            return false;
        if (get_intern_level(l2.var()) > 0)
            return false;
        return true;
    }

    /**
       \brief The learned clauses (lemmas) produced by the SAT solver
       have the property that the first literal will be implied by it
       after backtracking. All other literals are assigned to (or
       implied to be) false when the learned clause is created. The
       first watch literal will always be the first literal.  The
       second watch literal is computed by this method. It should be
       the literal with the highest decision level.

       If a literal is not assigned, it means it was re-initialized
       after backtracking. So, its level is assumed to be m_scope_lvl.
    */
    int context::select_learned_watch_lit(clause const * cls) const {
        SASSERT(cls->get_num_literals() >= 2);
        int max_false_idx = -1;
        unsigned max_lvl  = UINT_MAX;
        int num_lits      = cls->get_num_literals();
        for (int i = 1; i < num_lits; i++) {
            literal l    = cls->get_literal(i);
            lbool val    = get_assignment(l);
            SASSERT(val == l_false || val == l_undef);
            unsigned lvl = val == l_false ? get_assign_level(l) : m_scope_lvl;
            if (max_false_idx == -1 || lvl > max_lvl) {
                max_false_idx = i;
                max_lvl       = lvl;
            }
        }
        return max_false_idx;
    }

    /**
       \brief Select a watch literal from a set of literals which is
       different from the literal in position other_watch_lit.

       I use the following rules to select a watch literal.

       1- select a literal l in idx >= starting_at such that get_assignment(l) = l_true,
       and for all l' in idx' >= starting_at . get_assignment(l') = l_true implies get_level(l) <= get_level(l')

       The purpose of this rule is to make the clause inactive for as long as possible. A clause
       is inactive when it contains a literal assigned to true.

       2- if there isn't a literal assigned to true, then select an unassigned literal l is in idx >= starting_at

       3- if there isn't a literal l in idx >= starting_at such that get_assignment(l) = l_true or
       get_assignment(l) = l_undef (that is, all literals different from other_watch_lit are assigned
       to false), then peek the literal l different starting at starting_at such that for all l' starting at starting_at
       get_level(l) >= get_level(l')

       Without rule 3, boolean propagation is incomplete, that is, it may miss possible propagations.
       
       \remark The method select_lemma_watch_lit is used to select the
       watch literal for regular learned clauses.
    */
    int context::select_watch_lit(clause const * cls, int starting_at) const {
        SASSERT(cls->get_num_literals() >= 2);
        int min_true_idx  = -1;
        int max_false_idx = -1;
        int unknown_idx   = -1;
        int n = cls->get_num_literals();
        for (int i = starting_at; i < n; i++) {
            literal l   = cls->get_literal(i);
            switch(get_assignment(l)) {
            case l_false:
                if (max_false_idx == -1 || get_assign_level(l.var()) > get_assign_level(cls->get_literal(max_false_idx).var()))
                    max_false_idx = i;
                break;
            case l_undef:
                unknown_idx = i;
                break;
            case l_true:
                if (min_true_idx == -1 || get_assign_level(l.var()) < get_assign_level(cls->get_literal(min_true_idx).var()))
                    min_true_idx = i;
                break;
            }
        }
        if (min_true_idx != -1)
            return min_true_idx;
        if (unknown_idx != -1)
            return unknown_idx;
        SASSERT(max_false_idx != -1);
        return max_false_idx;
    }

    /**
       \brief Add watch literal to the given clause. 

       \pre idx must be 0 or 1.
    */
    void context::add_watch_literal(clause * cls, unsigned idx) {
        SASSERT(idx == 0 || idx == 1);
        literal l      = cls->get_literal(idx);
        unsigned l_idx = (~l).index();
        watch_list & wl = const_cast<watch_list &>(m_watches[l_idx]);
        wl.insert_clause(cls);
        CASSERT("watch_list", check_watch_list(l_idx));
    }

    /**
       \brief Create a new clause using the given literals, justification, kind and deletion event handler.
       The deletion event handler is ignored if binary clause optimization is applicable.
    */
    clause * context::mk_clause(unsigned num_lits, literal * lits, justification * j, clause_kind k, clause_del_eh * del_eh) {
        TRACE("mk_clause", display_literals_verbose(tout << "creating clause: " << literal_vector(num_lits, lits) << "\n", num_lits, lits) << "\n";);
        m_clause_proof.add(num_lits, lits, k, j);
        switch (k) {
        case CLS_AUX: 
        case CLS_TH_AXIOM: {
            literal_buffer simp_lits;
            if (!simplify_aux_clause_literals(num_lits, lits, simp_lits))
                return nullptr; // clause is equivalent to true;
            DEBUG_CODE({
                for (unsigned i = 0; i < simp_lits.size(); i++) {
                    SASSERT(get_assignment(simp_lits[i]) == l_true);
                }
            });
            if (!simp_lits.empty()) {
                j = mk_justification(unit_resolution_justification(m_region, j, simp_lits.size(), simp_lits.c_ptr()));
            }
            break;
        }
        case CLS_TH_LEMMA: {
            if (!simplify_aux_lemma_literals(num_lits, lits))
                return nullptr; // clause is equivalent to true
            // simplify_aux_lemma_literals does not delete literals assigned to false, so
            // it is not necessary to create a unit_resolution_justification
            break;
        }
        default:
            break;
        }
        TRACE("mk_clause", tout << "after simplification:\n"; display_literals_verbose(tout, num_lits, lits) << "\n";);
        unsigned activity = 0;
        if (activity == 0)
            activity = 1;
        bool  lemma = is_lemma(k);
        m_stats.m_num_mk_lits += num_lits;
        switch (num_lits) {
        case 0:
            if (j && !j->in_region())
                m_justifications.push_back(j);
            TRACE("mk_clause", tout << "empty clause... setting conflict\n";);
            set_conflict(j == nullptr ? b_justification::mk_axiom() : b_justification(j));
            SASSERT(inconsistent());
            return nullptr;
        case 1:
            if (j && !j->in_region())
                m_justifications.push_back(j);
            assign(lits[0], j);
            return nullptr;
        case 2:
            if (use_binary_clause_opt(lits[0], lits[1], lemma)) {
                literal l1 = lits[0];
                literal l2 = lits[1];
                m_watches[(~l1).index()].insert_literal(l2);
                m_watches[(~l2).index()].insert_literal(l1);
                if (get_assignment(l2) == l_false) {
                    assign(l1, b_justification(~l2));
                }
                m_clause_proof.add(l1, l2, k, j);
                m_stats.m_num_mk_bin_clause++;
                return nullptr;
            }
        default: {
            m_stats.m_num_mk_clause++;
            unsigned iscope_lvl = lemma ? get_max_iscope_lvl(num_lits, lits) : 0;
            SASSERT(m_scope_lvl >= iscope_lvl);
            bool save_atoms     = lemma && iscope_lvl > m_base_lvl;
            bool reinit         = save_atoms;
            SASSERT(!lemma || j == 0 || !j->in_region());
            clause * cls = clause::mk(m, num_lits, lits, k, j, del_eh, save_atoms, m_bool_var2expr.c_ptr());
            m_clause_proof.add(*cls);
            if (lemma) {
                cls->set_activity(activity);
                if (k == CLS_LEARNED) {
                    int w2_idx  = select_learned_watch_lit(cls);
                    cls->swap_lits(1, w2_idx);
                }
                else {
                    SASSERT(k == CLS_TH_LEMMA);
                    int w1_idx = select_watch_lit(cls, 0);
                    cls->swap_lits(0, w1_idx);
                    int w2_idx = select_watch_lit(cls, 1);
                    cls->swap_lits(1, w2_idx);
                    TRACE("mk_th_lemma", display_clause(tout, cls); tout << "\n";);
                }
                // display_clause(std::cout, cls); std::cout << "\n";
                m_lemmas.push_back(cls);
                add_watch_literal(cls, 0);
                add_watch_literal(cls, 1);
                if (get_assignment(cls->get_literal(0)) == l_false) {
                    set_conflict(b_justification(cls));
                    if (k == CLS_TH_LEMMA && m_scope_lvl > m_base_lvl) {
                        reinit     = true;
                        iscope_lvl = m_scope_lvl;
                    }
                }
                else if (get_assignment(cls->get_literal(1)) == l_false) {
                    assign(cls->get_literal(0), b_justification(cls));
                    if (k == CLS_TH_LEMMA && m_scope_lvl > m_base_lvl) {
                        reinit     = true;
                        iscope_lvl = m_scope_lvl;
                    }
                }
                if (reinit)
                    mark_for_reinit(cls, iscope_lvl, save_atoms);
            }
            else {
                m_aux_clauses.push_back(cls);
                add_watch_literal(cls, 0);
                add_watch_literal(cls, 1);
                if (get_assignment(cls->get_literal(0)) == l_false)
                    set_conflict(b_justification(cls));
                else if (get_assignment(cls->get_literal(1)) == l_false)
                    assign(cls->get_literal(0), b_justification(cls));
            }
            
            if (lit_occs_enabled())
                add_lit_occs(cls);
            
            TRACE("add_watch_literal_bug", display_clause_detail(tout, cls););
            TRACE("mk_clause_result", display_clause_detail(tout, cls););
            CASSERT("mk_clause", check_clause(cls));
            return cls;
        }} 
    }

    void context::add_lit_occs(clause * cls) {
        for (literal l : *cls) {
            m_lit_occs[l.index()].insert(cls);
        }
    }

    void context::mk_clause(literal l1, literal l2, justification * j) {
        literal ls[2] = { l1, l2 };
        mk_clause(2, ls, j);
    }

    void context::mk_clause(literal l1, literal l2, literal l3, justification * j) {
        literal ls[3] = { l1, l2, l3 };
        mk_clause(3, ls, j);
    }
    
    void context::mk_th_axiom(theory_id tid, unsigned num_lits, literal * lits, unsigned num_params, parameter * params) {
        justification * js = nullptr;
        TRACE("mk_th_axiom", display_literals_verbose(tout, num_lits, lits) << "\n";);

        if (m.proofs_enabled()) {
            js = mk_justification(theory_axiom_justification(tid, m_region, num_lits, lits, num_params, params));
        }
        if (m_fparams.m_smtlib_dump_lemmas) {
            literal_buffer tmp;
            neg_literals(num_lits, lits, tmp);
            SASSERT(tmp.size() == num_lits);
            display_lemma_as_smt_problem(tmp.size(), tmp.c_ptr(), false_literal, m_fparams.m_logic);
        }
        mk_clause(num_lits, lits, js, CLS_TH_AXIOM);
    }
    
    void context::mk_th_axiom(theory_id tid, literal l1, literal l2, unsigned num_params, parameter * params) {
        literal ls[2] = { l1, l2 };
        mk_th_axiom(tid, 2, ls, num_params, params);
    }

    void context::mk_th_axiom(theory_id tid, literal l1, literal l2, literal l3, unsigned num_params, parameter * params) {
        literal ls[3] = { l1, l2, l3 };
        mk_th_axiom(tid, 3, ls, num_params, params);
    }

    proof * context::mk_clause_def_axiom(unsigned num_lits, literal * lits, expr * root_gate) {
        ptr_buffer<expr> new_lits;
        for (unsigned i = 0; i < num_lits; i++) {
            literal l      = lits[i];
            bool_var v     = l.var();
            expr * atom    = m_bool_var2expr[v]; 
            new_lits.push_back(l.sign() ? m.mk_not(atom) : atom);
        }
        if (root_gate)
            new_lits.push_back(m.mk_not(root_gate));
        SASSERT(num_lits > 1);
        expr * fact        = m.mk_or(new_lits.size(), new_lits.c_ptr());
        return m.mk_def_axiom(fact);
        
    }

    void context::mk_gate_clause(unsigned num_lits, literal * lits) {
        if (m.proofs_enabled()) {
            proof * pr = mk_clause_def_axiom(num_lits, lits, nullptr);
            TRACE("gate_clause", tout << mk_ll_pp(pr, m););
            mk_clause(num_lits, lits, mk_justification(justification_proof_wrapper(*this, pr)));
        }
        else {
            mk_clause(num_lits, lits, nullptr);
        }
    }

    void context::mk_gate_clause(literal l1, literal l2) {
        literal ls[2] = { l1, l2 };
        mk_gate_clause(2, ls);
    }

    void context::mk_gate_clause(literal l1, literal l2, literal l3) {
        literal ls[3] = { l1, l2, l3 };
        mk_gate_clause(3, ls);
    }

    void context::mk_gate_clause(literal l1, literal l2, literal l3, literal l4) {
        literal ls[4] = { l1, l2, l3, l4 };
        mk_gate_clause(4, ls);
    }

    void context::mk_root_clause(unsigned num_lits, literal * lits, proof * pr) {
        if (m.proofs_enabled()) {
            SASSERT(m.get_fact(pr));
            expr * fact = m.get_fact(pr);
            if (!m.is_or(fact)) {
                proof * def = mk_clause_def_axiom(num_lits, lits, m.get_fact(pr));
                TRACE("gate_clause", tout << mk_ll_pp(def, m) << "\n";
                      tout << mk_ll_pp(pr, m););
                proof * prs[2] = { def, pr };
                pr  = m.mk_unit_resolution(2, prs);
            }
            mk_clause(num_lits, lits, mk_justification(justification_proof_wrapper(*this, pr)));
        }
        else {
            mk_clause(num_lits, lits, nullptr);
        }
    }

    void context::mk_root_clause(literal l1, literal l2, proof * pr) {
        literal ls[2] = { l1, l2 };
        mk_root_clause(2, ls, pr);
    }

    void context::mk_root_clause(literal l1, literal l2, literal l3, proof * pr) {
        literal ls[3] = { l1, l2, l3 };
        mk_root_clause(3, ls, pr);
    }

    void context::add_and_rel_watches(app * n) {
        if (relevancy()) {
            relevancy_eh * eh = m_relevancy_propagator->mk_and_relevancy_eh(n);
            for (expr * arg : *n) {
                // if one child is assigned to false, the and-parent must be notified
                literal l = get_literal(arg);
                add_rel_watch(~l, eh);
            }
        }
    }

    void context::add_or_rel_watches(app * n) {
        if (relevancy()) {
            relevancy_eh * eh = m_relevancy_propagator->mk_or_relevancy_eh(n);
            for (expr * arg : *n) {
                // if one child is assigned to true, the or-parent must be notified
                literal l = get_literal(arg);
                add_rel_watch(l, eh);
            }
        }
    }

    void context::add_ite_rel_watches(app * n) {
        if (relevancy()) {
            relevancy_eh * eh = m_relevancy_propagator->mk_ite_relevancy_eh(n);
            literal l         = get_literal(n->get_arg(0));
            // when the condition of an ite is assigned to true or false, the ite-parent must be notified.
            TRACE("propagate_relevant_ite", tout << "#" << n->get_id() << ", eh: " << eh << "\n";);
            add_rel_watch(l, eh);
            add_rel_watch(~l, eh);
        }    
    }
    
    void context::mk_not_cnstr(app * n) {
        SASSERT(b_internalized(n));
        bool_var v = get_bool_var(n);
        literal l(v, false);
        literal c          = get_literal(n->get_arg(0));
        mk_gate_clause(~l, ~c);
        mk_gate_clause(l,   c);
    }
    
    void context::mk_and_cnstr(app * n) {
        literal l = get_literal(n);
        TRACE("mk_and_cnstr", tout << "l: "; display_literal(tout, l); tout << "\n";);
        literal_buffer buffer;
        buffer.push_back(l);
        for (expr * arg : *n) {
            literal l_arg = get_literal(arg);
            TRACE("mk_and_cnstr", tout << "l_arg: "; display_literal(tout, l_arg); tout << "\n";);
            mk_gate_clause(~l, l_arg);
            buffer.push_back(~l_arg);
        }
        mk_gate_clause(buffer.size(), buffer.c_ptr());
    }

    void context::mk_or_cnstr(app * n) {
        literal l = get_literal(n);
        literal_buffer buffer;
        buffer.push_back(~l);
        for (expr * arg : *n) {
            literal l_arg = get_literal(arg);
            mk_gate_clause(l, ~l_arg);
            buffer.push_back(l_arg);
        }
        mk_gate_clause(buffer.size(), buffer.c_ptr());
    }

    void context::mk_iff_cnstr(app * n) {
        literal l  = get_literal(n);
        literal l1 = get_literal(n->get_arg(0));
        literal l2 = get_literal(n->get_arg(1));
        TRACE("mk_iff_cnstr", tout << "l: " << l << ", l1: " << l1 << ", l2: " << l2 << "\n";);
        mk_gate_clause(~l,  l1, ~l2);
        mk_gate_clause(~l, ~l1 , l2);
        mk_gate_clause( l,  l1,  l2);
        mk_gate_clause( l, ~l1, ~l2);
    }

    void context::mk_ite_cnstr(app * n) {
        literal l  = get_literal(n);
        literal l1 = get_literal(n->get_arg(0));
        literal l2 = get_literal(n->get_arg(1));
        literal l3 = get_literal(n->get_arg(2));
        mk_gate_clause(~l, ~l1,  l2);
        mk_gate_clause(~l,  l1,  l3);
        mk_gate_clause(l,  ~l1, ~l2);
        mk_gate_clause(l,   l1, ~l3);
    }

    /**
       \brief Trail for add_th_var
    */
    class add_th_var_trail : public trail<context> {
        enode *    m_enode;
        theory_id  m_th_id;
#ifdef Z3DEBUG
        theory_var m_th_var;
#endif
    public:
        add_th_var_trail(enode * n, theory_id th_id):
            m_enode(n),
            m_th_id(th_id) {
            DEBUG_CODE(m_th_var = n->get_th_var(th_id););
            SASSERT(m_th_var != null_theory_var);
        }
        
        void undo(context & ctx) override {
            theory_var v = m_enode->get_th_var(m_th_id);
            SASSERT(v != null_theory_var);
            SASSERT(m_th_var == v);
            m_enode->del_th_var(m_th_id);
            enode * root = m_enode->get_root();
            if (root != m_enode && root->get_th_var(m_th_id) == v) 
                root->del_th_var(m_th_id);
        }
    };

    /**
       \brief Trail for replace_th_var
    */
    class replace_th_var_trail : public trail<context> {
        enode *    m_enode;
        unsigned   m_th_id:8;
        unsigned   m_old_th_var:24;
    public:
        replace_th_var_trail(enode * n, theory_id th_id, theory_var old_var):
            m_enode(n),
            m_th_id(th_id),
            m_old_th_var(old_var) {
        }
        
        void undo(context & ctx) override {
            SASSERT(m_enode->get_th_var(m_th_id) != null_theory_var);
            m_enode->replace_th_var(m_old_th_var, m_th_id);
        }
    };


    /**
       \brief Attach theory var v to the enode n. 

       Enode n is to attached to any theory variable of th.

       This method should be invoked whenever the theory creates a new theory variable.

       \remark The methods new_eq_eh and new_diseq_eh of th may be invoked before this method 
       returns.
    */
    void context::attach_th_var(enode * n, theory * th, theory_var v) {
        SASSERT(!th->is_attached_to_var(n));
        theory_id th_id = th->get_id();
        theory_var old_v = n->get_th_var(th_id);
        if (old_v == null_theory_var) {
            enode * r     = n->get_root();
            theory_var v2 = r->get_th_var(th_id);
            n->add_th_var(v, th_id, m_region);
            push_trail(add_th_var_trail(n, th_id));
            if (v2 == null_theory_var) {
                if (r != n)
                    r->add_th_var(v, th_id, m_region);
                push_new_th_diseqs(r, v, th);
            }
            else if (r != n) {
                push_new_th_eq(th_id, v2, v);
            }
        }
        else {
            // Case) there is a variable old_v in the var-list of n.
            //
            // Remark: This variable was moved to the var-list of n due to a add_eq.
            SASSERT(th->get_enode(old_v) != n); // this varialbe is not owned by n
            SASSERT(n->get_root()->get_th_var(th_id) != null_theory_var); // the root has also a variable in its var-list.
            n->replace_th_var(v, th_id);
            push_trail(replace_th_var_trail(n, th_id, old_v));
            push_new_th_eq(th_id, v, old_v);
        }
        SASSERT(th->is_attached_to_var(n));
    }
};

