/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    theory_special_relations.cpp

Abstract:

    Special Relations theory plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2015-9-16
    Ashutosh Gupta 2016

Notes:

--*/

#include <fstream>

#include "ast/reg_decl_plugins.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/recfun_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/recfun_replace.h"
#include "smt/smt_context.h"
#include "smt/theory_arith.h"
#include "smt/theory_special_relations.h"


namespace smt {

    func_decl* theory_special_relations::relation::next() {
        if (!m_next) {
            sort* s = decl()->get_domain(0);
            sort* domain[2] = {s, s};
            m_next = m.mk_fresh_func_decl("next", "", 2, domain, s);
        }
        return m_next;
    }

    void theory_special_relations::relation::push() {
        m_scopes.push_back(scope());
        scope& s = m_scopes.back();
        s.m_asserted_atoms_lim = m_asserted_atoms.size();
        s.m_asserted_qhead_old = m_asserted_qhead;
        m_graph.push();        
        m_ufctx.get_trail_stack().push_scope();
    }

    void theory_special_relations::relation::pop(unsigned num_scopes) {
        unsigned new_lvl = m_scopes.size() - num_scopes;
        scope& s = m_scopes[new_lvl];
        m_asserted_atoms.shrink(s.m_asserted_atoms_lim);
        m_asserted_qhead = s.m_asserted_qhead_old;
        m_scopes.shrink(new_lvl);
        m_graph.pop(num_scopes);        
        m_ufctx.get_trail_stack().pop_scope(num_scopes);
    }

    void theory_special_relations::relation::ensure_var(theory_var v) {
        while ((unsigned)v > m_uf.mk_var());
        if ((unsigned)v >= m_graph.get_num_nodes()) {
            m_graph.init_var(v);
        }
    }

    bool theory_special_relations::relation::new_eq_eh(literal l, theory_var v1, theory_var v2) {
        ensure_var(v1);
        ensure_var(v2);
        literal_vector ls;
        ls.push_back(l);
        return m_graph.add_non_strict_edge(v1, v2, ls) && m_graph.add_non_strict_edge(v2, v1, ls);
    }

    std::ostream& theory_special_relations::relation::display(theory_special_relations const& th, std::ostream& out) const {
        out << mk_pp(m_decl, th.get_manager());
        for (unsigned i = 0; i < m_decl->get_num_parameters(); ++i) {
            th.get_manager().display(out << " ", m_decl->get_parameter(i));
        }
        out << ":\n";
        m_graph.display(out);
        out << "explanation: " << m_explanation << "\n";
        m_uf.display(out);
        for (atom* ap : m_asserted_atoms) {
            th.display_atom(out, *ap);
        }
        return out;
    }

    theory_special_relations::theory_special_relations(ast_manager& m):
        theory(m.mk_family_id("special_relations")),
        m_util(m),
        m_can_propagate(false) {
    }

    theory_special_relations::~theory_special_relations() {
        reset_eh();
    }

    theory * theory_special_relations::mk_fresh(context * new_ctx) {
        return alloc(theory_special_relations, new_ctx->get_manager());
    }

    /**
       \brief for term := next(next(a,b),c) for relation f
       assert f(term,c) or term != c
       assert f(term,c) or term != next(a,b)
       assert f(term,c) or term != b
       assert f(term,c) or term != a
     */
    void theory_special_relations::internalize_next(func_decl* f, app* term) {
        context& ctx = get_context();
        ast_manager& m = get_manager();
        func_decl* nxt = term->get_decl();
        expr* src = term->get_arg(0);
        expr* dst = term->get_arg(1);
        expr_ref f_rel(m.mk_app(f, src, dst), m);
        ensure_enode(term);
        ensure_enode(f_rel);
        literal f_lit = ctx.get_literal(f_rel);
        src = term;
        while (to_app(src)->get_decl() == nxt) {
            dst = to_app(src)->get_arg(1);
            src = to_app(src)->get_arg(0);
            ctx.mk_th_axiom(get_id(), f_lit, ~mk_eq(term, src, false));
            ctx.mk_th_axiom(get_id(), f_lit, ~mk_eq(term, dst, false));
        }
    }

    bool theory_special_relations::internalize_term(app * term) {
        return false;
    }

    bool theory_special_relations::internalize_atom(app * atm, bool gate_ctx) {
        SASSERT(m_util.is_special_relation(atm));
        relation* r = 0;
        ast_manager& m = get_manager();
        if (!m_relations.find(atm->get_decl(), r)) {
            r = alloc(relation, m_util.get_property(atm), atm->get_decl(), m);
            m_relations.insert(atm->get_decl(), r);
            for (unsigned i = 0; i < m_atoms_lim.size(); ++i) r->push();
        }
        context& ctx = get_context();
        expr* arg0 = atm->get_arg(0);
        expr* arg1 = atm->get_arg(1);
        theory_var v0 = mk_var(arg0);
        theory_var v1 = mk_var(arg1);
        bool_var v = ctx.mk_bool_var(atm);
        ctx.set_var_theory(v, get_id());
        atom* a = alloc(atom, v, *r, v0, v1);
        m_atoms.push_back(a);
        TRACE("special_relations", tout << mk_pp(atm, m) << " : bv" << v << " v" << a->v1() << " v" << a->v2() << ' ' << gate_ctx << "\n";);
        m_bool_var2atom.insert(v, a);
        return true;
    }

    theory_var theory_special_relations::mk_var(expr* e) {
        context& ctx = get_context();
        if (!ctx.e_internalized(e)) {
            ctx.internalize(e, false);
        }
        enode * n = ctx.get_enode(e);
        theory_var v = n->get_th_var(get_id());
        if (null_theory_var == v) {
            v = theory::mk_var(n);
            TRACE("special_relations", tout << "v" << v << " := " << mk_pp(e, get_manager()) << "\n";);
            ctx.attach_th_var(n, this, v);
        }
        return v;
    }

    void theory_special_relations::new_eq_eh(theory_var v1, theory_var v2) {
        app* t1 = get_expr(v1);
        app* t2 = get_expr(v2);
        literal eq = mk_eq(t1, t2, false);
        for (auto const& kv : m_relations) {
            relation& r = *kv.m_value;
            if (!r.new_eq_eh(eq, v1, v2)) {
                set_neg_cycle_conflict(r);
                break;
            }
        }
    }

    final_check_status theory_special_relations::final_check_eh() {
        TRACE("special_relations", tout << "\n";);
        for (auto const& kv : m_relations) {
            lbool r = final_check(*kv.m_value);
            switch (r) {
            case l_undef:
                return FC_GIVEUP;
            case l_false:
                return FC_CONTINUE;
            default:
                break;
            }
        }
        bool new_equality = false;
        for (auto const& kv : m_relations) {
            if (extract_equalities(*kv.m_value)) {
                new_equality = true;
            }
            if (get_context().inconsistent()) {
                return FC_CONTINUE;
            }
        }
        if (new_equality) {
            return FC_CONTINUE;
        }
        else {
            return FC_DONE;
        }
    }

    lbool theory_special_relations::final_check_lo(relation& r) {
        // all constraints are saturated by propagation.
        return l_true;
    }

    enode* theory_special_relations::ensure_enode(expr* e) {
        context& ctx = get_context();
        if (!ctx.e_internalized(e)) {
            ctx.internalize(e, false);
        }
        enode* n = ctx.get_enode(e);
        ctx.mark_as_relevant(n);
        return n;
    }

    literal theory_special_relations::mk_literal(expr* _e) {
        expr_ref e(_e, get_manager());
        ensure_enode(e);
        return get_context().get_literal(e);
    }

    theory_var theory_special_relations::mk_var(enode* n) {
        if (is_attached_to_var(n)) {
            return n->get_th_var(get_id());
        }
        else {
            theory_var v = theory::mk_var(n);
            get_context().attach_th_var(n, this, v);
            get_context().mark_as_relevant(n);
            return v;
        }
    }

    lbool theory_special_relations::final_check_plo(relation& r) {
        //
        // ensure that !Rxy -> Ryx between connected components
        // (where Rzx & Rzy or Rxz & Ryz for some z)
        //
        lbool res = l_true;
        for (unsigned i = 0; res == l_true && i < r.m_asserted_atoms.size(); ++i) {
            atom& a = *r.m_asserted_atoms[i];
            if (!a.phase() && r.m_uf.find(a.v1()) == r.m_uf.find(a.v2())) {
                res = enable(a);
            }
        }
        return res;
    }


    lbool theory_special_relations::final_check_tc(relation& r) {
        //
        // Ensure that Rxy -> TC(R)xy
        //
        func_decl* tcf = r.decl();
        func_decl* f = to_func_decl(tcf->get_parameter(0).get_ast());
        context& ctx = get_context();
        ast_manager& m = get_manager();
        bool new_assertion = false;
        graph r_graph;
        for (enode* n : ctx.enodes_of(f)) {
            literal lit = ctx.enode2literal(n);
            if (l_true == ctx.get_assignment(lit)) {
                expr* e = ctx.bool_var2expr(lit.var());
                expr* arg1 = to_app(e)->get_arg(0);
                expr* arg2 = to_app(e)->get_arg(1);
                expr_ref tc_app(m.mk_app(tcf, arg1, arg2), m);
                enode* tcn = ensure_enode(tc_app);
                if (ctx.get_assignment(tcn) != l_true) {
                    literal consequent = ctx.get_literal(tc_app);
                    justification* j = ctx.mk_justification(theory_propagation_justification(get_id(), ctx.get_region(), 1, &lit, consequent));
                    TRACE("special_relations", tout << "propagate: " << tc_app << "\n";);
                    ctx.assign(consequent, j);
                    new_assertion = true;
                }
                else {
                    theory_var v1 = get_representative(get_th_var(arg1));
                    theory_var v2 = get_representative(get_th_var(arg2));
                    r_graph.init_var(v1);
                    r_graph.init_var(v2);
                    literal_vector ls;
                    r_graph.enable_edge(r_graph.add_edge(v1, v2, s_integer(0), ls));
                }
            }
        }

        //
        // Ensure that  TC(R)xy -> Rxz1 Rz1z2 .. Rzky
        //
        // if not Rxy and no path in graph:
        // Introduce next(x,y), such that
        // TC(R)(x,y) => R(x,y) or TR(R)(next(x,y),y) & R(x,next(x,y))
        //
        // next(x,y) is fresh unless R(x,y) is true:
        // R(x,y) or x != next(x,y)
        // R(x,y) or y != next(x,y)
        // 
        unsigned sz = r.m_asserted_atoms.size();
        for (unsigned i = 0; i < sz; ++i) {
            atom& a = *r.m_asserted_atoms[i];
            if (a.phase()) {
                bool_var bv = a.var();
                expr* arg1 = get_expr(a.v1());
                expr* arg2 = get_expr(a.v2());

                // we need reachability in the R graph not R* graph
                theory_var r1 = get_representative(a.v1());
                theory_var r2 = get_representative(a.v2());
                if (r_graph.can_reach(r1, r2)) {
                    TRACE("special_relations", 
                          tout << a.v1() << ": " << mk_pp(arg1, m) << " -> " 
                          << a.v2() << ": " << mk_pp(arg2, m) << " is positive reachable\n";
                          r.m_graph.display(tout);
                          );
                    continue;
                }
                expr_ref f_app(m.mk_app(f, arg1, arg2), m);                
                ensure_enode(f_app);
                literal f_lit = ctx.get_literal(f_app);
                switch (ctx.get_assignment(f_lit)) {
                case l_true:
                    UNREACHABLE(); 
                    // it should already be the case that v1 and reach v2 in the graph.
                    // whenever f(n1, n2) is asserted.
                    break;
                case l_false: {
                    //
                    // Add the axioms:
                    //  TC(R)(x,y) => R(x,y) or TC(R)(next(x,y),y) 
                    //  TC(R)(x,y) => R(x,y) or R(x,next(x,y))
                    // R(x,y) or next(x,y) != x
                    // R(x,y) or next(x,y) != y, 
                    // and recursively on all next subterms of x.
                    // Add the literal R(next(x,y),y) - set case split preference to true.
                    //
                    // TBD: perhaps replace by recursion unfolding similar to theory_rec_fun
                    //
                    
                    app_ref next(r.next(arg1, arg2), m);
                    internalize_next(f, next);
                    expr_ref a2next(m.mk_app(f, arg1, next), m);
                    expr_ref next2b(m.mk_app(tcf, next, arg2), m);
                    expr_ref next_b(m.mk_app(f, next, arg2), m);
                    ensure_enode(a2next);
                    ensure_enode(next2b);
                    ensure_enode(next_b);
                    literal next2b_l = ctx.get_literal(next2b);
                    literal a2next_l = ctx.get_literal(a2next);
                    if (ctx.get_assignment(next2b_l) == l_true && ctx.get_assignment(a2next_l) == l_true) {
                        break;
                    }
                    ctx.mk_th_axiom(get_id(), ~literal(bv), f_lit, a2next_l);
                    ctx.mk_th_axiom(get_id(), ~literal(bv), f_lit, next2b_l);
                    expr* nxt = next;
                    while (r.is_next(nxt)) {
                        expr* left  = to_app(nxt)->get_arg(0);
                        expr* right = to_app(nxt)->get_arg(1);
                        ctx.assign(~mk_eq(next, left,  false), nullptr);
                        ctx.assign(~mk_eq(next, right, false), nullptr);
                        nxt = left;
                    }
                    ctx.set_true_first_flag(ctx.get_literal(next_b).var());
                    new_assertion = true;
                    break;
                }
                case l_undef:
                    ctx.set_true_first_flag(bv);
                    TRACE("special_relations", tout << f_app << " is undefined\n";);
                    new_assertion = true;
                    break;
                }
            }
        }
        if (new_assertion) {
            TRACE("special_relations", tout << "new assertion\n";);
            return l_false;
        }
        return final_check_po(r);
    }


    lbool theory_special_relations::final_check_to(relation& r) {
        uint_set visited, target;
        for (atom* ap : r.m_asserted_atoms) {
            atom& a = *ap;
            if (a.phase()) {
                continue;
            }
            TRACE("special_relations", tout << a.v1() << " !<= " << a.v2() << "\n";);
            target.reset();
            theory_var w;
            // v1 !<= v2 is asserted
            target.insert(a.v1());
            if (r.m_graph.reachable(a.v2(), target, visited, w)) {
                // we already have v2 <= v1
                TRACE("special_relations", tout << "already: " << a.v2() << " <= " << a.v1() << "\n";);
                continue;
            }
            // the nodes visited from v1 become target for v2
            if (r.m_graph.reachable(a.v2(), visited, target, w)) {
                //
                // we have the following:
                // v1 <= w
                // v2 <= w
                // v1 !<= v2
                //
                // enforce the assertion
                //
                //   v1 <= w & v2 <= w & v1 !<= v2 -> v2 <= v1
                //
                unsigned timestamp = r.m_graph.get_timestamp();
                r.m_explanation.reset();
                r.m_graph.find_shortest_reachable_path(a.v1(), w, timestamp, r);
                r.m_graph.find_shortest_reachable_path(a.v2(), w, timestamp, r);
                TRACE("special_relations", tout << "added edge\n";);
                r.m_explanation.push_back(a.explanation());
                literal_vector const& lits = r.m_explanation;
                if (!r.m_graph.add_non_strict_edge(a.v2(), a.v1(), lits)) {
                    set_neg_cycle_conflict(r);
                    return l_false;
                }
            }
            target.reset();
            visited.reset();
            target.insert(a.v2());
            if (r.m_graph.reachable(a.v1(), target, visited, w)) {
                // we have v1 <= v2
                unsigned timestamp = r.m_graph.get_timestamp();
                r.m_explanation.reset();
                r.m_graph.find_shortest_reachable_path(a.v1(), w, timestamp, r);
                r.m_explanation.push_back(a.explanation());
                set_conflict(r);                
            }

        }
        return l_true;
    }

    lbool theory_special_relations::enable(atom& a) {
        if (!a.enable()) {
            relation& r = a.get_relation();
            set_neg_cycle_conflict(r);
            return l_false;
        }
        else {
            return l_true;
        }
    }

    void theory_special_relations::set_neg_cycle_conflict(relation& r) {
        r.m_explanation.reset();
        r.m_graph.traverse_neg_cycle2(false, r);
        set_conflict(r);
    }

    void theory_special_relations::set_conflict(relation& r) {
        literal_vector const& lits = r.m_explanation;
        context & ctx = get_context();
        TRACE("special_relations", ctx.display_literals_verbose(tout, lits) << "\n";);
        vector<parameter> params;
        ctx.set_conflict(
            ctx.mk_justification(
                ext_theory_conflict_justification(
                    get_id(), ctx.get_region(),
                    lits.size(), lits.c_ptr(), 0, 0, params.size(), params.c_ptr())));
    }

    lbool theory_special_relations::final_check(relation& r) {
        lbool res = propagate(r);
        if (res != l_true) return res;
        switch (r.m_property) {
        case sr_lo:
            res = final_check_lo(r);
            break;
        case sr_po:
            res = final_check_po(r);
            break;
        case sr_plo:
            res = final_check_plo(r);
            break;
        case sr_to:
            res = final_check_to(r);
            break;
        case sr_tc:
            res = final_check_tc(r);
            break;
        default:
            UNREACHABLE();
            res = l_undef;
            break;
        }
        TRACE("special_relations", r.display(*this, tout << res << "\n"););
        return res;
    }

    bool theory_special_relations::extract_equalities(relation& r) {
        switch (r.m_property) {
        case sr_tc:
            return false;
        default:
            break;
        }
        bool new_eq = false;
        int_vector scc_id;
        u_map<unsigned> roots;
        context& ctx = get_context();
        ast_manager& m = get_manager();
        (void)m;
        r.m_graph.compute_zero_edge_scc(scc_id);
        int start = ctx.get_random_value();
        for (unsigned idx = 0, j = 0; !ctx.inconsistent() && idx < scc_id.size(); ++idx) {
            unsigned i = (start + idx) % scc_id.size();
            if (scc_id[i] == -1) {
                continue;
            }
            enode* x = get_enode(i);
            if (roots.find(scc_id[i], j)) {
                enode* y = get_enode(j);
                if (x->get_root() != y->get_root()) {
                    new_eq = true;
                    unsigned timestamp = r.m_graph.get_timestamp();
                    r.m_explanation.reset();
                    r.m_graph.find_shortest_zero_edge_path(i, j, timestamp, r);
                    r.m_graph.find_shortest_zero_edge_path(j, i, timestamp, r);
                    literal_vector const& lits = r.m_explanation;
                    TRACE("special_relations", ctx.display_literals_verbose(tout << mk_pp(x->get_owner(), m) << " = " << mk_pp(y->get_owner(), m) << "\n", lits) << "\n";);
                    IF_VERBOSE(20, ctx.display_literals_verbose(verbose_stream() << mk_pp(x->get_owner(), m) << " = " << mk_pp(y->get_owner(), m) << "\n", lits) << "\n";);
                    eq_justification js(ctx.mk_justification(ext_theory_eq_propagation_justification(get_id(), ctx.get_region(), lits.size(), lits.c_ptr(), 0, nullptr, 
                                                                                                     x, y)));
                    ctx.assign_eq(x, y, js);
                }
            }
            else {
                roots.insert(scc_id[i], i);
            }
        }
        return new_eq;
    }

    /*
      \brief Propagation for piecewise linear orders
    */
    lbool theory_special_relations::propagate_plo(atom& a) {
        lbool res = l_true;
        relation& r = a.get_relation();
        if (a.phase()) {
            r.m_uf.merge(a.v1(), a.v2());
            res = enable(a);
        }
        else if (r.m_uf.find(a.v1()) == r.m_uf.find(a.v2())) {
            res = enable(a);
        }
        return res;
    }
    
    lbool theory_special_relations::propagate_po(atom& a) {
        lbool res = l_true;
        if (a.phase()) {
            relation& r = a.get_relation();
            r.m_uf.merge(a.v1(), a.v2());
            res = enable(a);
        }
        return res;
    }

    lbool theory_special_relations::propagate_tc(atom& a) {
        if (a.phase()) {
            VERIFY(a.enable());
            relation& r = a.get_relation();
            r.m_uf.merge(a.v1(), a.v2());
        }
        return l_true;
    }

    lbool theory_special_relations::final_check_po(relation& r) {
        for (atom* ap : r.m_asserted_atoms) {
            atom& a = *ap;
            if (!a.phase() && r.m_uf.find(a.v1()) == r.m_uf.find(a.v2())) {
                // v1 !-> v2
                // find v1 -> v3 -> v4 -> v2 path
                r.m_explanation.reset();
                unsigned timestamp = r.m_graph.get_timestamp();
                bool found_path = r.m_graph.find_shortest_reachable_path(a.v1(), a.v2(), timestamp, r);
                if (found_path) {
                    TRACE("special_relations", tout << "check po conflict\n";);
                    r.m_explanation.push_back(a.explanation());
                    set_conflict(r);
                    return l_false;
                }
            }
        }
        return l_true;
    }

    void theory_special_relations::propagate() {
        if (m_can_propagate) {
            for (auto const& kv : m_relations) {
                propagate(*kv.m_value);
            }
            m_can_propagate = false;
        }
    }

    lbool theory_special_relations::propagate(relation& r) {
        lbool res = l_true;
        while (res == l_true && r.m_asserted_qhead < r.m_asserted_atoms.size()) {
            atom& a = *r.m_asserted_atoms[r.m_asserted_qhead];
            switch (r.m_property) {
            case sr_lo:
                res = enable(a);
                break;
            case sr_plo:
                res = propagate_plo(a);
                break;
            case sr_po:
                res = propagate_po(a);
                break;
            case sr_tc:
                res = propagate_tc(a);
                break;
            default:
                if (a.phase()) {
                    res = enable(a);
                }
                break;
            }
            ++r.m_asserted_qhead;
        }
        return res;
    }

    void theory_special_relations::reset_eh() {
        for (auto const& kv : m_relations) {
            dealloc(kv.m_value);
        }
        m_relations.reset();
        del_atoms(0);
    }

    void theory_special_relations::assign_eh(bool_var v, bool is_true) {
        TRACE("special_relations", tout << "assign bv" << v << " " << (is_true?" <- true":" <- false") << "\n";);
        atom* a = m_bool_var2atom[v];
        a->set_phase(is_true);
        a->get_relation().m_asserted_atoms.push_back(a);
        m_can_propagate = true;
    }

    void theory_special_relations::push_scope_eh() {
        theory::push_scope_eh();
        for (auto const& kv : m_relations) {
            kv.m_value->push();
        }
        m_atoms_lim.push_back(m_atoms.size());
    }

    void theory_special_relations::pop_scope_eh(unsigned num_scopes) {
        for (auto const& kv : m_relations) {
            kv.m_value->pop(num_scopes);
        }
        unsigned new_lvl = m_atoms_lim.size() - num_scopes;
        del_atoms(m_atoms_lim[new_lvl]);
        m_atoms_lim.shrink(new_lvl);
        theory::pop_scope_eh(num_scopes);
    }

    void theory_special_relations::del_atoms(unsigned old_size) {
        atoms::iterator begin = m_atoms.begin() + old_size;
        atoms::iterator it    = m_atoms.end();
        while (it != begin) {
            --it;
            atom* a = *it;
            m_bool_var2atom.erase(a->var());
            dealloc(a);
        }
        m_atoms.shrink(old_size);
    }


    void theory_special_relations::collect_statistics(::statistics & st) const {
        for (auto const& kv : m_relations) {
            kv.m_value->m_graph.collect_statistics(st);
        }
    }

    model_value_proc * theory_special_relations::mk_value(enode * n, model_generator & mg) {
        UNREACHABLE();
        return nullptr;
    }

    void theory_special_relations::ensure_strict(graph& g) {
        unsigned sz = g.get_num_edges();
        for (unsigned i = 0; i < sz; ++i) {
            if (!g.is_enabled(i)) continue;
            if (g.get_weight(i) != s_integer(0)) continue;
            dl_var src = g.get_source(i);
            dl_var dst = g.get_target(i);
            if (get_enode(src)->get_root() == get_enode(dst)->get_root()) continue;
            VERIFY(g.add_strict_edge(src, dst, literal_vector()));
        }
        TRACE("special_relations", g.display(tout););
    }

    /**
       src1 <= i, src2 <= i, src1 != src2 => src1 !<= src2
     */

    void theory_special_relations::ensure_tree(graph& g) {
        unsigned sz = g.get_num_nodes();
        for (unsigned i = 0; i < sz; ++i) {
            int_vector const& edges = g.get_in_edges(i);
            for (unsigned j = 0; j < edges.size(); ++j) {
                edge_id e1 = edges[j];
                if (!g.is_enabled(e1)) continue;
                SASSERT ((int)i == g.get_target(e1));
                dl_var src1 = g.get_source(e1);
                for (unsigned k = j + 1; k < edges.size(); ++k) {
                    edge_id e2 = edges[k];
                    if (!g.is_enabled(e2)) continue;
                    dl_var src2 = g.get_source(e2);
                    if (get_enode(src1)->get_root() != get_enode(src2)->get_root() && 
                        disconnected(g, src1, src2)) {
                        VERIFY(g.add_strict_edge(src1, src2, literal_vector()));
                    }
                }
            }
        }
        TRACE("special_relations", g.display(tout););
    }

    bool theory_special_relations::disconnected(graph const& g, dl_var u, dl_var v) const {
        s_integer val_u = g.get_assignment(u);
        s_integer val_v = g.get_assignment(v);
        if (val_u == val_v) return u != v;
        if (val_u < val_v) {
            std::swap(u, v);
            std::swap(val_u, val_v);
        }
        SASSERT(val_u > val_v);
        svector<dl_var> todo;
        todo.push_back(u);
        while (!todo.empty()) {
            u = todo.back();
            todo.pop_back();
            if (u == v) {
                return false;
            }
            SASSERT(g.get_assignment(u) <= val_u);
            if (g.get_assignment(u) <= val_v) {
                continue;
            }
            for (edge_id e : g.get_out_edges(u)) {
                if (is_strict_neighbour_edge(g, e)) {
                    todo.push_back(g.get_target(e));
                }
            }
        }
        return true;
    }

    expr_ref theory_special_relations::mk_inj(relation& r, model_generator& mg) {
        ast_manager& m = get_manager();
        r.push();
        ensure_strict(r.m_graph);
        func_decl_ref fn(m);
        expr_ref result(m);
        arith_util arith(m);
        sort* const* ty = r.decl()->get_domain();
        fn = m.mk_fresh_func_decl("inj", 1, ty, arith.mk_int());
        unsigned sz = r.m_graph.get_num_nodes();
        func_interp* fi = alloc(func_interp, m, 1);
        for (unsigned i = 0; i < sz; ++i) {
            s_integer val = r.m_graph.get_assignment(i);
            expr* arg = get_expr(i);
            fi->insert_new_entry(&arg, arith.mk_numeral(val.to_rational(), true));
        }
        TRACE("special_relations", r.m_graph.display(tout););
        r.pop(1);
        fi->set_else(arith.mk_numeral(rational(0), true));
        mg.get_model().register_decl(fn, fi);
        result = arith.mk_le(m.mk_app(fn,m.mk_var(0, *ty)), m.mk_app(fn, m.mk_var(1, *ty)));
        return result;
    }

    expr_ref theory_special_relations::mk_class(relation& r, model_generator& mg) {
        ast_manager& m = get_manager();
        expr_ref result(m);
        func_decl_ref fn(m);
        arith_util arith(m);
        func_interp* fi = alloc(func_interp, m, 1);
        sort* const* ty = r.decl()->get_domain();
        fn = m.mk_fresh_func_decl("class", 1, ty, arith.mk_int());
        unsigned sz = r.m_graph.get_num_nodes();
        for (unsigned i = 0; i < sz; ++i) {
            unsigned val = r.m_uf.find(i);
            expr* arg = get_expr(i);
            fi->insert_new_entry(&arg, arith.mk_numeral(rational(val), true));
        }
        fi->set_else(arith.mk_numeral(rational(0), true));
        mg.get_model().register_decl(fn, fi);
        result = m.mk_eq(m.mk_app(fn, m.mk_var(0, *ty)), m.mk_app(fn, m.mk_var(1, *ty)));
        return result;
    }

    expr_ref theory_special_relations::mk_interval(relation& r, model_generator& mg, unsigned_vector & lo, unsigned_vector& hi) {
        graph const& g = r.m_graph;
        ast_manager& m = get_manager();
        expr_ref result(m);
        func_decl_ref lofn(m), hifn(m);
        arith_util arith(m);
        func_interp* lofi = alloc(func_interp, m, 1);
        func_interp* hifi = alloc(func_interp, m, 1);
        sort* const* ty = r.decl()->get_domain();
        lofn = m.mk_fresh_func_decl("lo", 1, ty, arith.mk_int());
        hifn = m.mk_fresh_func_decl("hi", 1, ty, arith.mk_int());
        unsigned sz = g.get_num_nodes();
        for (unsigned i = 0; i < sz; ++i) {
            expr* arg = get_expr(i);
            lofi->insert_new_entry(&arg, arith.mk_numeral(rational(lo[i]), true));
            hifi->insert_new_entry(&arg, arith.mk_numeral(rational(hi[i]), true));
        }
        lofi->set_else(arith.mk_numeral(rational(0), true));
        hifi->set_else(arith.mk_numeral(rational(0), true));
        mg.get_model().register_decl(lofn, lofi);
        mg.get_model().register_decl(hifn, hifi);
        result = m.mk_and(arith.mk_le(m.mk_app(lofn, m.mk_var(0, *ty)), m.mk_app(lofn, m.mk_var(1, *ty))),
                          arith.mk_le(m.mk_app(hifn, m.mk_var(1, *ty)), m.mk_app(hifn, m.mk_var(0, *ty))));
        return result;
    }

    void theory_special_relations::init_model_lo(relation& r, model_generator& m) {
        expr_ref inj = mk_inj(r, m);
        func_interp* fi = alloc(func_interp, get_manager(), 2);
        fi->set_else(inj);
        m.get_model().register_decl(r.decl(), fi);
    }

    void theory_special_relations::init_model_plo(relation& r, model_generator& mg) {
        expr_ref inj = mk_inj(r, mg);
        expr_ref cls = mk_class(r, mg);
        func_interp* fi = alloc(func_interp, get_manager(), 2);
        fi->set_else(get_manager().mk_and(inj, cls));
        mg.get_model().register_decl(r.decl(), fi);
    }

    /**
       \brief model for a partial order, 
       is a recursive function that evaluates membership in partial order over
       a fixed set of edges. It runs in O(e*n^2) where n is the number of vertices and e 
       number of edges.

       connected(A, dst, S) = 
               let (A',S') = next1(a1, b1, A, next1(a2, b2, A, ... S, (nil, S)))
               if A' = nil then false else
               if member(dst, A') then true else
               connected(A', dst, S')

       next1(a, b, A, S, (A',S')) = 
              if member(a, A) and not member(b, S) then (cons(b, A'), cons(b, S')) else (A',S')
     */


    void theory_special_relations::init_model_po(relation& r, model_generator& mg, bool is_reflexive) {
        ast_manager& m = get_manager();
        sort* s = r.m_decl->get_domain(0);
        datatype_util dt(m);
        recfun::util rf(m);
        recfun::decl::plugin& p = rf.get_plugin();
        func_decl_ref nil(m), is_nil(m), cons(m), is_cons(m), hd(m), tl(m);        
        sort_ref listS(dt.mk_list_datatype(s, symbol("List"), cons, is_cons, hd, tl, nil, is_nil), m);
        func_decl_ref fst(m), snd(m), pair(m);
        expr_ref nilc(m.mk_const(nil), m);

        expr* T = m.mk_true();
        expr* F = m.mk_false();

        func_decl* memf, *nextf, *connectedf;

        {
            sort* dom[2] = { s, listS };
            recfun::promise_def mem = p.ensure_def(symbol("member"), 2, dom, m.mk_bool_sort(), true);
            memf = mem.get_def()->get_decl();
            
            var_ref xV(m.mk_var(1, s), m);
            var_ref SV(m.mk_var(0, listS), m);
            var_ref yV(m), vV(m), wV(m);
            
            expr* x = xV, *S = SV;
            expr_ref mem_body(m);
            mem_body = m.mk_ite(m.mk_app(is_nil, S), 
                                F,
                                m.mk_ite(m.mk_eq(m.mk_app(hd, S), x), 
                                         T,
                                         m.mk_app(memf, x, m.mk_app(tl, S))));            
            recfun_replace rep(m);
            var* vars[2] = { xV, SV };
            p.set_definition(rep, mem, 2, vars, mem_body);
        }

        sort_ref tup(dt.mk_pair_datatype(listS, listS, fst, snd, pair), m);

        {
            sort* dom[5] = { s, s, listS, listS, tup };
            recfun::promise_def nxt = p.ensure_def(symbol("next"), 5, dom, tup, true);
            nextf = nxt.get_def()->get_decl();
            
            expr_ref next_body(m);
            var_ref aV(m.mk_var(4, s), m);
            var_ref bV(m.mk_var(3, s), m);
            var_ref AV(m.mk_var(2, listS), m);
            var_ref SV(m.mk_var(1, listS), m);
            var_ref tupV(m.mk_var(0, tup), m);
            expr* a = aV, *b = bV, *A = AV, *S = SV, *t = tupV;
            next_body = m.mk_ite(m.mk_and(m.mk_app(memf, a, A), m.mk_not(m.mk_app(memf, b, S))), 
                                 m.mk_app(pair, m.mk_app(cons, b, m.mk_app(fst, t)), m.mk_app(cons, b, m.mk_app(snd, t))),
                                 t);

            recfun_replace rep(m);
            var* vars[5] = { aV, bV, AV, SV, tupV };
            p.set_definition(rep, nxt, 5, vars, next_body);
        }

        {
            sort* dom[3] = { listS, s, listS };
            recfun::promise_def connected = p.ensure_def(symbol("connected"), 3, dom, m.mk_bool_sort(), true);
            connectedf = connected.get_def()->get_decl();
            var_ref AV(m.mk_var(2, listS), m);
            var_ref dstV(m.mk_var(1, s), m);
            var_ref SV(m.mk_var(0, listS), m);
            expr* A = AV, *dst = dstV, *S = SV;
            expr_ref connected_body(m);

            connected_body = m.mk_app(pair, nilc.get(), S);

            for (atom* ap : r.m_asserted_atoms) {
                atom& a = *ap;
                if (!a.phase()) continue;
                SASSERT(get_context().get_assignment(a.var()) == l_true);
                expr* x = get_enode(a.v1())->get_root()->get_owner();
                expr* y = get_enode(a.v2())->get_root()->get_owner();
                expr* cb = connected_body;
                expr* args[5] = { x, y, A, S, cb };
                connected_body = m.mk_app(nextf, 5, args);
            }
            expr_ref Ap(m.mk_app(fst, connected_body.get()), m);
            expr_ref Sp(m.mk_app(snd, connected_body.get()), m);

            connected_body = m.mk_ite(m.mk_eq(Ap, nilc), F, 
                                      m.mk_ite(m.mk_app(memf, dst, Ap), T,
                                               m.mk_app(connectedf, Ap, dst, Sp)));
            
            TRACE("special_relations", tout << connected_body << "\n";);
            recfun_replace rep(m);
            var* vars[3] = { AV, dstV, SV };
            p.set_definition(rep, connected, 3, vars, connected_body);            
        }

        {
            var_ref xV(m.mk_var(0, s), m);
            var_ref yV(m.mk_var(1, s), m);
            expr* x = xV, *y = yV;
            
            func_interp* fi = alloc(func_interp, m, 2);
            expr_ref consx(m.mk_app(cons, x, nilc), m);
            expr_ref pred(m.mk_app(connectedf, consx, y, consx), m); 
            if (is_reflexive) {
                pred = m.mk_or(pred, m.mk_eq(x, y));
            }
            fi->set_else(pred);
            mg.get_model().register_decl(r.decl(), fi);
        }        
    }

    /**
       \brief map each node to an interval of numbers, such that
       the children are proper sub-intervals.
       Then the <= relation becomes interval containment.

       1. For each vertex, count the number of nodes below it in the transitive closure.
          Store the result in num_children.
       2. Identify each root.
       3. Process children, assigning unique (and disjoint) intervals.
       4. Extract interpretation.


     */

    void theory_special_relations::init_model_to(relation& r, model_generator& mg) {
        unsigned_vector num_children, lo, hi;
        graph const& g = r.m_graph;
        r.push();
        ensure_strict(r.m_graph);
        ensure_tree(r.m_graph);
        count_children(g, num_children);
        assign_interval(g, num_children, lo, hi);
        expr_ref iv = mk_interval(r, mg, lo, hi);
        r.pop(1);
        func_interp* fi = alloc(func_interp, get_manager(), 2);
        fi->set_else(iv);
        mg.get_model().register_decl(r.decl(), fi);
    }

    bool theory_special_relations::is_neighbour_edge(graph const& g, edge_id edge) const {
        CTRACE("special_relations_verbose", g.is_enabled(edge),
              tout << edge << ": " << g.get_source(edge) << " " << g.get_target(edge) << " ";
              tout << (g.get_assignment(g.get_target(edge)) - g.get_assignment(g.get_source(edge))) << "\n";);

        return
            g.is_enabled(edge) &&
            g.get_assignment(g.get_source(edge)) + s_integer(1) == g.get_assignment(g.get_target(edge));
    }

    bool theory_special_relations::is_strict_neighbour_edge(graph const& g, edge_id e) const {
        return is_neighbour_edge(g, e) && g.get_weight(e) != s_integer(0);
    }

    void theory_special_relations::count_children(graph const& g, unsigned_vector& num_children) {
        unsigned sz = g.get_num_nodes();
        svector<dl_var> nodes;
        num_children.resize(sz, 0);
        svector<bool> processed(sz, false);
        for (unsigned i = 0; i < sz; ++i) nodes.push_back(i);
        while (!nodes.empty()) {
            dl_var v = nodes.back();
            if (processed[v]) {
                nodes.pop_back();
                continue;
            }
            unsigned nc = 1;
            bool all_p = true;
            for (edge_id e : g.get_out_edges(v)) {
                if (is_strict_neighbour_edge(g, e)) {
                    dl_var dst = g.get_target(e);
                    TRACE("special_relations", tout << v << " -> " << dst << "\n";);
                    if (!processed[dst]) {
                        all_p = false;
                        nodes.push_back(dst);
                    }
                    nc += num_children[dst];
                }
            }
            if (all_p) {
                nodes.pop_back();
                num_children[v] = nc;
                processed[v] = true;
            }
        }
        TRACE("special_relations",
              for (unsigned i = 0; i < sz; ++i) {
                  tout << i << ": " << num_children[i] << "\n";
              });
    }

    void theory_special_relations::assign_interval(graph const& g, unsigned_vector const& num_children, unsigned_vector& lo, unsigned_vector& hi) {
        svector<dl_var> nodes;
        unsigned sz = g.get_num_nodes();
        lo.resize(sz, 0);
        hi.resize(sz, 0);
        unsigned offset = 0;
        for (unsigned i = 0; i < sz; ++i) {
            bool is_root = true;
            int_vector const& edges = g.get_in_edges(i);
            for (edge_id e_id : edges) {
                is_root &= !g.is_enabled(e_id);
            }
            if (is_root) {
                lo[i] = offset;
                hi[i] = offset + num_children[i] - 1;
                offset = hi[i] + 1;
                nodes.push_back(i);
            }
        }
        while (!nodes.empty()) {
            dl_var v = nodes.back();
            int_vector const& edges = g.get_out_edges(v);
            unsigned l = lo[v];
            unsigned h = hi[v];
            (void)h;
            nodes.pop_back();
            for (unsigned i = 0; i < edges.size(); ++i) {
                SASSERT(l <= h);
                if (is_strict_neighbour_edge(g, edges[i])) {
                    dl_var dst = g.get_target(edges[i]);
                    lo[dst] = l;
                    hi[dst] = l + num_children[dst] - 1;
                    l = hi[dst] + 1;
                    nodes.push_back(dst);
                }
            }
            SASSERT(l == h);
        }
    }

    void theory_special_relations::init_model(model_generator & m) {
        for (auto const& kv : m_relations) {
            switch (kv.m_value->m_property) {
            case sr_lo:
                init_model_lo(*kv.m_value, m);
                break;
            case sr_plo:
                init_model_plo(*kv.m_value, m);
                break;
            case sr_to:
                init_model_to(*kv.m_value, m);
                break;
            case sr_po:
                init_model_po(*kv.m_value, m, true);
                break;
            case sr_tc:
                init_model_po(*kv.m_value, m, true);                
                break;
            default:
                // other 28 combinations of 0x1F
                NOT_IMPLEMENTED_YET();
            }
        }
    }

    void theory_special_relations::display(std::ostream & out) const {
        if (m_relations.empty()) return;
        out << "Theory Special Relations\n";
        display_var2enode(out);
        for (auto const& kv : m_relations) {
            kv.m_value->display(*this, out);
        }
    }

    void theory_special_relations::collect_asserted_po_atoms(vector<std::pair<bool_var, bool>>& atoms) const {
        for (auto const& kv : m_relations) {
            relation& r = *kv.m_value;
            if (r.m_property != sr_po) continue;
            for (atom* ap : r.m_asserted_atoms) {
                atoms.push_back(std::make_pair(ap->var(), ap->phase()));
            }
        }
    }
    
    void theory_special_relations::display_atom(std::ostream & out, atom& a) const {
        context& ctx = get_context();
        expr* e = ctx.bool_var2expr(a.var());
        out << (a.phase() ? "" : "(not ") << mk_pp(e, get_manager()) << (a.phase() ? "" : ")") << "\n";
    }
    
}
