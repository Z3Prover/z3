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
#include "tactic/tactic_exception.h"
#include "sat/sat_solver.h"
#include "sat/smt/sat_smt.h"
#include "sat/smt/ba_solver.h"
#include "sat/smt/euf_solver.h"

namespace euf {

    void solver::updt_params(params_ref const& p) {
        m_config.updt_params(p);
    }

    /**
    * retrieve extension that is associated with Boolean variable.
    */
    sat::th_solver* solver::get_solver(sat::bool_var v) {
        if (v >= m_var2node.size())
            return nullptr;
        euf::enode* n = m_var2node[v].first;
        if (!n)
            return nullptr;
        return get_solver(n->get_owner());
    }

    sat::th_solver* solver::get_solver(expr* e) {
        if (is_app(e)) 
            return get_solver(to_app(e)->get_decl());        
        return nullptr;
    }

    sat::th_solver* solver::get_solver(func_decl* f) {
        family_id fid = f->get_family_id();
        if (fid == null_family_id)
            return nullptr;
        auto* ext = m_id2solver.get(fid, nullptr);
        if (ext)
            return ext;
        pb_util pb(m);
        if (pb.get_family_id() == fid) {
            ext = alloc(sat::ba_solver, m, si);
        }
        if (ext) {
            ext->set_solver(m_solver);
            ext->push_scopes(s().num_scopes());
            add_solver(fid, ext);
        }
        else {
            unhandled_function(f);
        }
        return ext;
    }

    void solver::add_solver(family_id fid, sat::th_solver* th) {
        m_solvers.push_back(th);
        m_id2solver.setx(fid, th, nullptr);
    }

    void solver::unhandled_function(func_decl* f) {
        IF_VERBOSE(0, verbose_stream() << mk_pp(f, m) << " not handled\n");
        // TBD: set some state with the unhandled function.
    }

    bool solver::propagate(literal l, ext_constraint_idx idx) { 
        force_push();
        auto* ext = sat::constraint_base::to_extension(idx);
        SASSERT(ext != this);
        return ext->propagate(l, idx);
    }

    void solver::get_antecedents(literal l, ext_justification_idx idx, literal_vector& r) {
        auto* ext = sat::constraint_base::to_extension(idx);
        if (ext == this)
            get_antecedents(l, *constraint::from_idx(idx), r);
        else
            ext->get_antecedents(l, idx, r);
    }

    void solver::get_antecedents(literal l, constraint& j, literal_vector& r) {
        m_explain.reset();
        euf::enode* n = nullptr;
        bool sign = false;
        enode_bool_pair p;

        // init_ackerman();

        switch (j.kind()) {
        case constraint::kind_t::conflict:
            SASSERT(m_egraph.inconsistent());
            m_egraph.explain<unsigned>(m_explain);
            break;
        case constraint::kind_t::eq:
            n = m_var2node[l.var()].first;
            SASSERT(n);
            SASSERT(m_egraph.is_equality(n));
            m_egraph.explain_eq<unsigned>(m_explain, n->get_arg(0), n->get_arg(1), n->commutative());
            break;
        case constraint::kind_t::lit:
            p = m_var2node[l.var()];
            n = p.first;
            sign = l.sign() != p.second;
            SASSERT(n);
            SASSERT(m.is_bool(n->get_owner()));
            m_egraph.explain_eq<unsigned>(m_explain, n, (sign ? mk_false() : mk_true()), false);
            break;
        default:
            UNREACHABLE();
        }
        for (unsigned* idx : m_explain) 
            r.push_back(sat::to_literal((unsigned)(idx - base_ptr())));
    }

    void solver::asserted(literal l) {
        auto* ext = get_solver(l.var());
        if (ext) {
            force_push();
            ext->asserted(l);
            return;
        }

        auto p = m_var2node.get(l.var(), enode_bool_pair(nullptr, false));
        if (!p.first)
            return;
        force_push();
        bool sign = p.second != l.sign();
        euf::enode* n = p.first;
        expr* e = n->get_owner();
        if (m.is_eq(e) && !sign) {
            euf::enode* na = n->get_arg(0);
            euf::enode* nb = n->get_arg(1);
            m_egraph.merge(na, nb, base_ptr() + l.index());
        }
        else {
            euf::enode* nb = sign ? mk_false() : mk_true();
            m_egraph.merge(n, nb, base_ptr() + l.index());
        }
        // TBD: delay propagation?
        propagate();
    }

    void solver::propagate() {     
        m_egraph.propagate();
        if (m_egraph.inconsistent()) {       
            s().set_conflict(sat::justification::mk_ext_justification(s().scope_lvl(), conflict_constraint().to_index()));
            return;
        }
        for (euf::enode* eq : m_egraph.new_eqs()) {
            bool_var v = m_expr2var.to_bool_var(eq->get_owner());
            expr* a = nullptr, *b = nullptr;
            if (s().value(v) == l_false && m_ackerman && m.is_eq(eq->get_owner(), a, b))
                m_ackerman->cg_conflict_eh(a, b);
            s().assign(literal(v, false), sat::justification::mk_ext_justification(s().scope_lvl(), eq_constraint().to_index()));
        }
        for (euf::enode* p : m_egraph.new_lits()) {
            expr* e = p->get_owner();
            bool sign = m.is_false(p->get_root()->get_owner());
            SASSERT(m.is_bool(e));
            SASSERT(m.is_true(p->get_root()->get_owner()) || sign);
            bool_var v = m_expr2var.to_bool_var(e);
            literal lit(v, sign);
            if (s().value(lit) == l_false && m_ackerman) 
                m_ackerman->cg_conflict_eh(p->get_owner(), p->get_root()->get_owner());
            s().assign(lit, sat::justification::mk_ext_justification(s().scope_lvl(), lit_constraint().to_index()));
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
        return visit(m.mk_true());
    }

    enode* solver::mk_false() {
        return visit(m.mk_false());
    }

    sat::check_result solver::check() { 
        force_push();
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
        ++m_num_scopes;
    }

    void solver::force_push() {
        for (; m_num_scopes > 0; --m_num_scopes) {
            scope s;
            s.m_bool_var_lim = m_bool_var_trail.size();
            s.m_trail_lim = m_trail.size();
            m_scopes.push_back(s);
            for (auto* e : m_solvers)
                e->push();
            m_egraph.push();
        }
    }

    void solver::pop(unsigned n) {
        if (n <= m_num_scopes) {
            m_num_scopes -= n;
            return;
        }
        n -= m_num_scopes;
        m_egraph.pop(n);
        for (auto* e : m_solvers)
            e->pop(n);

        scope & s = m_scopes[m_scopes.size() - n];

        for (unsigned i = m_bool_var_trail.size(); i-- > s.m_bool_var_lim; )
            m_var2node[m_bool_var_trail[i]] = enode_bool_pair(nullptr, false);
        m_bool_var_trail.shrink(s.m_bool_var_lim);
        
        undo_trail_stack(*this, m_trail, s.m_trail_lim);
        
        m_scopes.shrink(m_scopes.size() - n);
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

    std::ostream& solver::display(std::ostream& out) const {
        m_egraph.display(out);
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
        st.update("euf dynack", m_stats.m_num_dynack);
    }

    sat::extension* solver::copy(sat::solver* s) { 
        auto* r = alloc(solver, *m_to_m, *m_to_expr2var, *m_to_si);
        r->m_config = m_config;
        std::function<void* (void*)> copy_justification = [&](void* x) { return (void*)(r->base_ptr() + ((unsigned*)x - base_ptr())); };
        r->m_egraph.copy_from(m_egraph, copy_justification);        
        r->set_solver(s);
        for (unsigned i = 0; i < m_id2solver.size(); ++i) {
            auto* e = m_id2solver[i];
            if (e)
                r->add_solver(i, e->fresh(s, *m_to_m, *m_to_si));
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
        force_push();
        for (auto* e : m_solvers)
            e->pop_reinit();
    }

    bool solver::validate() { 
        for (auto* e : m_solvers)
            if (!e->validate())
                return false;
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
        for (unsigned sz = m_var2node.size(); sz-- > 0; ) {
            euf::enode* n = m_var2node[sz].first;
            if (n && m.is_bool(n->get_owner())) {
                w = std::max(w, sz);
                break;
            }           
        }
        return w; 
    }

    double solver::get_reward(literal l, ext_constraint_idx idx, sat::literal_occs_fun& occs) const {
        double r = 0;
        for (auto* e : m_solvers) {
            r = e->get_reward(l, idx, occs);
            if (r != 0)
                return r;
        }
        return r;
    }

    bool solver::is_extended_binary(ext_justification_idx idx, literal_vector& r) {
        for (auto* e : m_solvers) {
            if (e->is_extended_binary(idx, r))
                return true;
        }
        return false;
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

    sat::literal solver::internalize(expr* e, bool sign, bool root) {
        force_push();
        auto* ext = get_solver(e);
        if (ext)
            return ext->internalize(e, sign, root);
        IF_VERBOSE(0, verbose_stream() << "internalize: " << mk_pp(e, m) << "\n");
        SASSERT(!si.is_bool_op(e));
        sat::scoped_stack _sc(m_stack);
        unsigned sz = m_stack.size();
        euf::enode* n = visit(e);
        while (m_stack.size() > sz) {
        loop:
            if (!m.inc())
                throw tactic_exception(m.limit().get_cancel_msg());
            sat::frame & fr = m_stack.back();
            expr* e = fr.m_e;
            if (m_egraph.find(e)) {
                m_stack.pop_back();
                continue;
            }
            unsigned num = is_app(e) ? to_app(e)->get_num_args() : 0;
            
            while (fr.m_idx < num) {
                expr* arg = to_app(e)->get_arg(fr.m_idx);
                fr.m_idx++;
                n = visit(arg);
                if (!n)
                    goto loop;
            }
            m_args.reset();
            for (unsigned i = 0; i < num; ++i)
                m_args.push_back(m_egraph.find(to_app(e)->get_arg(i)));
            n = m_egraph.mk(e, num, m_args.c_ptr());
            attach_bool_var(n);
        }        
        SASSERT(m_egraph.find(e));
        return literal(m_expr2var.to_bool_var(e), sign);
    }

    euf::enode* solver::visit(expr* e) {
        euf::enode* n = m_egraph.find(e);
        if (n)
            return n;
        if (si.is_bool_op(e)) {
            sat::literal lit = si.internalize(e);
            enode_bool_pair bp(nullptr, false);
            n = m_var2node.get(lit.var(), bp).first;
            if (n)
                return n;
            
            n = m_egraph.mk(e, 0, nullptr);
            attach_bool_var(lit.var(), lit.sign(), n);
            if (!m.is_true(e) && !m.is_false(e)) 
                s().set_external(lit.var());
            return n;
        }
        if (is_app(e) && to_app(e)->get_num_args() > 0) {
            m_stack.push_back(sat::frame(e));
            return nullptr;
        }
        n = m_egraph.mk(e, 0, nullptr);
        attach_bool_var(n);
        return n;
    }

    void solver::attach_bool_var(euf::enode* n) {
        expr* e = n->get_owner();
        if (m.is_bool(e)) {
            sat::bool_var v = si.add_bool_var(e);
            attach_bool_var(v, false, n);
        }
    }

    void solver::attach_bool_var(sat::bool_var v, bool sign, euf::enode* n) {
        m_var2node.reserve(v + 1, enode_bool_pair(nullptr, false));
        SASSERT(m_var2node[v].first == nullptr);
        m_var2node[v] = euf::enode_bool_pair(n, sign);
        m_bool_var_trail.push_back(v);
    }

    bool solver::to_formulas(std::function<expr_ref(sat::literal)>& l2e, expr_ref_vector& fmls) {
        for (auto* th : m_solvers) {            
            if (!th->to_formulas(l2e, fmls))
                return false;
        }
        for (euf::enode* n : m_egraph.nodes()) {
            if (!n->is_root()) 
                fmls.push_back(m.mk_eq(n->get_owner(), n->get_root()->get_owner()));            
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
