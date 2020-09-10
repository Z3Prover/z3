/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_solver.cpp

Abstract:

    Solver plugin for EUF

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/

#include "ast/pb_decl_plugin.h"
#include "ast/ast_ll_pp.h"
#include "sat/sat_solver.h"
#include "sat/smt/sat_smt.h"
#include "sat/smt/ba_solver.h"
#include "sat/smt/bv_solver.h"
#include "sat/smt/euf_solver.h"

namespace euf {

    void solver::updt_params(params_ref const& p) {
        m_config.updt_params(p);
    }

    /**
    * retrieve extension that is associated with Boolean variable.
    */
    th_solver* solver::get_solver(sat::bool_var v) {
        if (v >= m_var2expr.size())
            return nullptr;
        expr* e = m_var2expr[v];
        if (!e)
            return nullptr;
        return get_solver(e);
    }

    th_solver* solver::get_solver(expr* e) {
        if (is_app(e)) 
            return get_solver(to_app(e)->get_decl());        
        return nullptr;
    }

    th_solver* solver::get_solver(family_id fid, func_decl* f) {
        if (fid == null_family_id)
            return nullptr;
        auto* ext = m_id2solver.get(fid, nullptr);
        if (ext)
            return ext;
        if (fid == m.get_basic_family_id())
            return nullptr;
        pb_util pb(m);
        bv_util bvu(m);
        if (pb.get_family_id() == fid) {
            ext = alloc(sat::ba_solver, *this, fid);
            if (use_drat())
                s().get_drat().add_theory(fid, symbol("ba"));
        }
        else if (bvu.get_family_id() == fid) {
            ext = alloc(bv::solver, *this, fid);
            if (use_drat())
                s().get_drat().add_theory(fid, symbol("bv"));            
        }
        if (ext) {
            ext->set_solver(m_solver);
            ext->push_scopes(s().num_scopes());
            add_solver(fid, ext);
        }
        else if (f) 
            unhandled_function(f);
        return ext;
    }

    void solver::add_solver(family_id fid, th_solver* th) {
        m_solvers.push_back(th);
        m_id2solver.setx(fid, th, nullptr);
    }

    void solver::unhandled_function(func_decl* f) {
        if (m_unhandled_functions.contains(f))
            return;
        m_unhandled_functions.push_back(f);
        m_trail.push(push_back_vector<solver, func_decl_ref_vector>(m_unhandled_functions));
        IF_VERBOSE(0, verbose_stream() << mk_pp(f, m) << " not handled\n");
    }

    void solver::init_search() {
        TRACE("euf", display(tout););
    }

    bool solver::is_external(bool_var v) {
        if (nullptr != m_var2expr.get(v, nullptr))
            return true;
        for (auto* s : m_solvers)
            if (s->is_external(v))
                return true;
        return false;
    }

    bool solver::propagate(literal l, ext_constraint_idx idx) { 
        auto* ext = sat::constraint_base::to_extension(idx);
        SASSERT(ext != this);
        return ext->propagate(l, idx);
    }

    void solver::get_antecedents(literal l, ext_justification_idx idx, literal_vector& r, bool probing) {
        m_egraph.begin_explain();
        m_explain.reset();
        auto* ext = sat::constraint_base::to_extension(idx);
        if (ext == this)
            get_antecedents(l, constraint::from_idx(idx), r, probing);
        else
            ext->get_antecedents(l, idx, r, probing);
        for (unsigned qhead = 0; qhead < m_explain.size(); ++qhead) {
            size_t* e = m_explain[qhead];
            if (is_literal(e))
                r.push_back(get_literal(e));
            else {
                size_t idx = get_justification(e);
                auto* ext = sat::constraint_base::to_extension(idx);
                SASSERT(ext != this);
                sat::literal lit = sat::null_literal;
                ext->get_antecedents(lit, idx, r, probing);
            }
        }
        m_egraph.end_explain();
        if (!probing)
            log_antecedents(l, r);
    }

    void solver::add_antecedent(enode* a, enode* b) {
        m_egraph.explain_eq<size_t>(m_explain, a, b);
    }

    bool solver::propagate(enode* a, enode* b, ext_justification_idx idx) {
        if (a->get_root() == b->get_root())
            return false;
        m_egraph.merge(a, b, to_ptr(idx));
        return true;
    }


    void solver::get_antecedents(literal l, constraint& j, literal_vector& r, bool probing) {
        expr* e = nullptr;
        euf::enode* n = nullptr;

        init_ackerman();

        switch (j.kind()) {
        case constraint::kind_t::conflict:
            SASSERT(m_egraph.inconsistent());
            m_egraph.explain<size_t>(m_explain);
            break;
        case constraint::kind_t::eq:
            e = m_var2expr[l.var()];
            n = m_egraph.find(e);
            SASSERT(n);
            SASSERT(m_egraph.is_equality(n));
            SASSERT(!l.sign());
            m_egraph.explain_eq<size_t>(m_explain, n->get_arg(0), n->get_arg(1));
            break;
        case constraint::kind_t::lit:
            e = m_var2expr[l.var()];
            n = m_egraph.find(e);
            SASSERT(n);
            SASSERT(m.is_bool(n->get_expr()));
            m_egraph.explain_eq<size_t>(m_explain, n, (l.sign() ? mk_false() : mk_true()));
            break;
        default:
            IF_VERBOSE(0, verbose_stream() << (unsigned)j.kind() << "\n");
            UNREACHABLE();
        }
    }

    void solver::asserted(literal l) {
        expr* e = m_var2expr.get(l.var(), nullptr);
        if (!e) {
            return;
        }

        bool sign = l.sign();        
        TRACE("euf", tout << "asserted: " << l << "@" << s().scope_lvl() << " " << (sign ? "not ": " ") << e->get_id()  << "\n";);
        euf::enode* n = m_egraph.find(e);
        if (!n)
            return;
        for (auto th : enode_th_vars(n))           
            m_id2solver[th.get_id()]->asserted(l);
        if (!n->merge_enabled())
            return;
        size_t* c = to_ptr(l);
        SASSERT(is_literal(c));
        SASSERT(l == get_literal(c));
        if (m.is_eq(e) && !sign && n->num_args() == 2) {
            euf::enode* na = n->get_arg(0);
            euf::enode* nb = n->get_arg(1);
            m_egraph.merge(na, nb, c);
        }
        else {            
            euf::enode* nb = sign ? mk_false() : mk_true();
            m_egraph.merge(n, nb, c);
        }
    }

    bool solver::unit_propagate() {
        bool propagated = false;
        while (!s().inconsistent()) {
            if (m_egraph.inconsistent()) {  
                unsigned lvl = s().scope_lvl();
                s().set_conflict(sat::justification::mk_ext_justification(lvl, conflict_constraint().to_index()));
                return true;
            }
            bool propagated1 = false;
            if (m_egraph.propagate()) {
                propagate_literals();
                propagate_th_eqs();
                propagated1 = true;
            }

            for (auto* s : m_solvers) {
                if (s->unit_propagate())
                    propagated1 = true;
            }
            if (!propagated1)
                break;
            propagated = true;             
        }
        return propagated;
    }

    void solver::propagate_literals() {
        for (; m_egraph.has_literal() && !s().inconsistent() && !m_egraph.inconsistent(); m_egraph.next_literal()) {
            euf::enode_bool_pair p = m_egraph.get_literal();
            euf::enode* n = p.first;
            bool is_eq = p.second;
            expr* e = n->get_expr();
            expr* a = nullptr, *b = nullptr;
            bool_var v = si.to_bool_var(e);
            SASSERT(m.is_bool(e));
            size_t cnstr;
            literal lit;
            if (is_eq) {
                VERIFY(m.is_eq(e, a, b));
                cnstr = eq_constraint().to_index();
                lit = literal(v, false);
            }
            else {
                a = e, b = n->get_root()->get_expr();
                SASSERT(m.is_true(b) || m.is_false(b));
                cnstr = lit_constraint().to_index();
                lit = literal(v, m.is_false(b));
            }
            if (s().value(lit) == l_false && m_ackerman) 
                m_ackerman->cg_conflict_eh(a, b);
            unsigned lvl = s().scope_lvl();
            if (s().value(lit) != l_true)
                s().assign(lit, sat::justification::mk_ext_justification(lvl, cnstr));
        }
    }

    void solver::propagate_th_eqs() {
        for (; m_egraph.has_th_eq() && !s().inconsistent() && !m_egraph.inconsistent(); m_egraph.next_th_eq()) {
            th_eq eq = m_egraph.get_th_eq();
            m_id2solver[eq.m_id]->new_eq_eh(eq);            
        }
    }

    constraint& solver::mk_constraint(constraint*& c, constraint::kind_t k) {
        if (!c) {
            void* mem = memory::allocate(sat::constraint_base::obj_size(sizeof(constraint)));
            c = new (sat::constraint_base::ptr2mem(mem)) constraint(k);
            sat::constraint_base::initialize(mem, this);
        }
        return *c;
    }

    enode* solver::mk_true() {
        VERIFY(visit(m.mk_true()));
        return m_egraph.find(m.mk_true());
    }

    enode* solver::mk_false() {
        VERIFY(visit(m.mk_false()));
        return m_egraph.find(m.mk_false());
    }

    sat::check_result solver::check() { 
        TRACE("euf", s().display(tout););
        bool give_up = false;
        bool cont = false;
        for (auto* e : m_solvers)
            switch (e->check()) {
            case sat::CR_CONTINUE: cont = true; break;
            case sat::CR_GIVEUP: give_up = true; break;
            default: break;
            }
        if (cont)
            return sat::CR_CONTINUE;
        if (give_up)
            return sat::CR_GIVEUP;
        return sat::CR_DONE; 
    }

    void solver::push() {
        si.push();
        scope s;
        s.m_var_lim = m_var_trail.size();
        m_scopes.push_back(s);
        m_trail.push_scope();
        for (auto* e : m_solvers)
            e->push();
        m_egraph.push();
    }

    void solver::pop(unsigned n) {
        start_reinit(n);
        m_egraph.pop(n);
        for (auto* e : m_solvers)
            e->pop(n);
        scope const & s = m_scopes[m_scopes.size() - n];
        for (unsigned i = m_var_trail.size(); i-- > s.m_var_lim; )
            m_var2expr[m_var_trail[i]] = nullptr;
        m_var_trail.shrink(s.m_var_lim);        
        m_trail.pop_scope(n);
        m_scopes.shrink(m_scopes.size() - n);
        si.pop(n);
    }

    void solver::start_reinit(unsigned n) {
        m_reinit_exprs.reset();
        for (sat::bool_var v : s().get_vars_to_reinit()) {
            expr* e = bool_var2expr(v);
            m_reinit_exprs.push_back(e);
        }
    }

    void solver::finish_reinit() {

        SASSERT(s().get_vars_to_reinit().size() == m_reinit_exprs.size());
        if (s().get_vars_to_reinit().empty())
            return;
        unsigned i = 0;
        obj_map<expr, sat::bool_var> expr2var_replay;
        for (sat::bool_var v : s().get_vars_to_reinit()) {
            expr* e = m_reinit_exprs.get(i++);
            if (!e)
                continue;
            expr2var_replay.insert(e, v);
        }
        if (expr2var_replay.empty())
            return;
        si.set_expr2var_replay(&expr2var_replay);
        for (auto const& kv : expr2var_replay)
            si.internalize(kv.m_key, true);
        si.set_expr2var_replay(nullptr);        
    }

    void solver::pre_simplify() {
        for (auto* e : m_solvers)
            e->pre_simplify();
    }

    void solver::simplify() {
        for (auto* e : m_solvers)
            e->simplify();
        if (m_ackerman)
            m_ackerman->propagate();
    }

    void solver::clauses_modifed() {
        for (auto* e : m_solvers)
            e->clauses_modifed();
    }

    lbool solver::get_phase(bool_var v) { 
        auto* ext = get_solver(v);
        if (ext)
            return ext->get_phase(v);
        return l_undef; 
    }

    bool solver::set_root(literal l, literal r) {
        bool ok = true;
        for (auto* s : m_solvers)
            if (!s->set_root(l, r))
                ok = false;
        expr* e = bool_var2expr(l.var());
        if (e) {
            if (m.is_eq(e) && !m.is_iff(e))
                ok = false;
            euf::enode* n = get_enode(e);
            if (n && n->merge_enabled())
                ok = false;
        }
        return ok;
    }

    void solver::flush_roots() {
        for (auto* s : m_solvers)
            s->flush_roots();
    }

    std::ostream& solver::display(std::ostream& out) const {
        m_egraph.display(out);
        out << "bool-vars\n";
        for (unsigned v : m_var_trail) {
            expr* e = m_var2expr[v];
            out << v << ": " << e->get_id() << " " << m_solver->value(v) << " " << mk_bounded_pp(e, m, 1) << "\n";        
        }
        for (auto* e : m_solvers)
            e->display(out);
        return out; 
    }

    std::ostream& solver::display_justification(std::ostream& out, ext_justification_idx idx) const { 
        auto* ext = sat::constraint_base::to_extension(idx);
        if (ext != this)
            return ext->display_justification(out, idx);
        return out; 
    }

    std::ostream& solver::display_constraint(std::ostream& out, ext_constraint_idx idx) const { 
        auto* ext = sat::constraint_base::to_extension(idx);
        if (ext != this)
            return ext->display_constraint(out, idx);
        return out; 
    }

    void solver::collect_statistics(statistics& st) const {
        m_egraph.collect_statistics(st);
        for (auto* e : m_solvers)
            e->collect_statistics(st);
        st.update("euf ackerman", m_stats.m_ackerman);
    }

    sat::extension* solver::copy(sat::solver* s) { 
        auto* r = alloc(solver, *m_to_m, *m_to_si);
        r->m_config = m_config;
        sat::literal true_lit = sat::null_literal;
        if (s->init_trail_size() > 0)
            true_lit = s->trail_literal(0); 
        std::function<void* (void*)> copy_justification = [&](void* x) { 
            SASSERT(true_lit != sat::null_literal); 
            return (void*)(r->to_ptr(true_lit)); 
        };
        r->m_egraph.copy_from(m_egraph, copy_justification);        
        r->set_solver(s);
        for (unsigned i = 0; i < m_id2solver.size(); ++i) {
            auto* e = m_id2solver[i];
            if (e)
                r->add_solver(i, e->fresh(s, *r));
        }
        return r;
    }

    void solver::find_mutexes(literal_vector& lits, vector<literal_vector> & mutexes) {
        for (auto* e : m_solvers)
            e->find_mutexes(lits, mutexes);
    }

    void solver::gc() {
        for (auto* e : m_solvers)
            e->gc();
    }

    void solver::pop_reinit() {
        finish_reinit();
        for (auto* e : m_solvers)
            e->pop_reinit();
    }

    bool solver::validate() { 
        for (auto* e : m_solvers)
            if (!e->validate())
                return false;
        check_eqc_bool_assignment();
        check_missing_bool_enode_propagation();
        m_egraph.invariant();
        return true; 
    }

    void solver::init_use_list(sat::ext_use_list& ul) {
        for (auto* e : m_solvers)
            e->init_use_list(ul);
    }

    bool solver::is_blocked(literal l, ext_constraint_idx idx) { 
        auto* ext = sat::constraint_base::to_extension(idx);
        if (ext != this)
            return ext->is_blocked(l, idx);
        return false; 
    }

    bool solver::check_model(sat::model const& m) const { 
        for (auto* e : m_solvers)
            if (!e->check_model(m))
                return false;
        return true;
    }

    unsigned solver::max_var(unsigned w) const { 
        for (auto* e : m_solvers)
            w = e->max_var(w);
        for (unsigned sz = m_var2expr.size(); sz-- > 0; ) {
            expr* n = m_var2expr[sz];
            if (n && m.is_bool(n)) {
                w = std::max(w, sz);
                break;
            }           
        }
        return w; 
    }

    double solver::get_reward(literal l, ext_constraint_idx idx, sat::literal_occs_fun& occs) const {
        auto* ext = sat::constraint_base::to_extension(idx);
        SASSERT(ext);        
        return (ext == this) ? 0 : ext->get_reward(l, idx, occs);        
    }

    bool solver::is_extended_binary(ext_justification_idx idx, literal_vector& r) {
        auto* ext = sat::constraint_base::to_extension(idx);
        SASSERT(ext);        
        return (ext != this) && ext->is_extended_binary(idx, r);
    }

    void solver::init_ackerman() {
        if (m_ackerman) 
            return;
        if (m_config.m_dack == DACK_DISABLED)
            return;
        m_ackerman = alloc(ackerman, *this, m);
        std::function<void(expr*,expr*,expr*)> used_eq = [&](expr* a, expr* b, expr* lca) {
            m_ackerman->used_eq_eh(a, b, lca);
        };
        std::function<void(app*,app*)> used_cc = [&](app* a, app* b) {
            m_ackerman->used_cc_eh(a, b);
        };
        m_egraph.set_used_eq(used_eq);
        m_egraph.set_used_cc(used_cc);
    }

    bool solver::to_formulas(std::function<expr_ref(sat::literal)>& l2e, expr_ref_vector& fmls) {
        for (auto* th : m_solvers) {            
            if (!th->to_formulas(l2e, fmls))
                return false;
        }
        for (euf::enode* n : m_egraph.nodes()) {
            if (!n->is_root()) 
                fmls.push_back(m.mk_eq(n->get_expr(), n->get_root()->get_expr()));
        }
        return true;
    }

    bool solver::extract_pb(std::function<void(unsigned sz, literal const* c, unsigned k)>& card,
                            std::function<void(unsigned sz, literal const* c, unsigned const* coeffs, unsigned k)>& pb) {
        for (auto* e : m_solvers)
            if (!e->extract_pb(card, pb))
                return false;
        return true;
    }

}
