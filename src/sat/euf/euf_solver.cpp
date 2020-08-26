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
#include "sat/smt/sat_smt.h"
#include "sat/ba/ba_solver.h"
#include "sat/ba/ba_internalize.h"
#include "sat/euf/euf_solver.h"
#include "sat/sat_solver.h"
#include "tactic/tactic_exception.h"

namespace euf {

    /**
    * retrieve extension that is associated with Boolean variable.
    */
    sat::extension* solver::get_extension(sat::bool_var v) {
        if (v >= m_var2node.size())
            return nullptr;
        euf::enode* n = m_var2node[v].first;
        if (!n)
            return nullptr;
        return get_extension(n->get_owner());
    }

    void solver::add_extension(family_id fid, sat::extension* e) {
        m_extensions.push_back(e);
        m_id2extension.setx(fid, e, nullptr);
    }

    sat::extension* solver::get_extension(expr* e) {
        if (is_app(e)) {
            auto fid = to_app(e)->get_family_id();
            if (fid == null_family_id)
                return nullptr;
            auto* ext = m_id2extension.get(fid, nullptr);
            if (ext)
                return ext;
            pb_util pb(m);
            if (pb.is_pb(e)) {
                auto* ba = alloc(sat::ba_solver);
                ba->set_solver(m_solver);
                add_extension(pb.get_family_id(), ba);
                auto* bai = alloc(sat::ba_internalize, *ba, s(), m);
                m_id2internalize.setx(pb.get_family_id(), bai, nullptr);
                m_internalizers.push_back(bai);
                ba->push_scopes(s().num_scopes());
                return ba;
            }
        }
        return nullptr;
    }

    bool solver::propagate(literal l, ext_constraint_idx idx) { 
        auto* ext = sat::index_base::to_extension(idx);
        SASSERT(ext != this);
        return ext->propagate(l, idx);
    }

    void solver::get_antecedents(literal l, ext_justification_idx idx, literal_vector& r) {
        auto* ext = sat::index_base::to_extension(idx);
        if (ext == this)
            get_antecedents(l, *euf_base::from_idx(idx), r);
        else
            ext->get_antecedents(l, idx, r);
    }

    void solver::get_antecedents(literal l, euf_base& j, literal_vector& r) {
        m_explain.reset();
        euf::enode* n = nullptr;
        bool sign = false;
        if (j.id() != 0) {
            auto p = m_var2node[l.var()];
            n = p.first;  
            SASSERT(n);
            sign = l.sign() != p.second;
        }

        switch (j.id()) {
        case 0:
            SASSERT(m_egraph.inconsistent());
            m_egraph.explain<unsigned>(m_explain);
            break;
        case 1:
            SASSERT(m_egraph.is_equality(n));
            m_egraph.explain_eq<unsigned>(m_explain, n->get_arg(0), n->get_arg(1), n->commutative());
            break;
        case 2:
            SASSERT(m.is_bool(n->get_owner()));
            m_egraph.explain_eq<unsigned>(m_explain, n, (sign ? m_false : m_true), false);
            break;
        default:
            UNREACHABLE();
        }
        for (unsigned* idx : m_explain) 
            r.push_back(sat::to_literal((unsigned)(idx - base_ptr())));
    }

    void solver::asserted(literal l) {
        auto* ext = get_extension(l.var());
        if (ext) {
            ext->asserted(l);
            return;
        }

        auto p = m_var2node.get(l.var(), enode_bool_pair(nullptr, false));
        if (!p.first)
            return;
        bool sign = p.second != l.sign();
        euf::enode* n = p.first;
        expr* e = n->get_owner();
        if (m.is_eq(e) && !sign) {
            euf::enode* na = n->get_arg(0);
            euf::enode* nb = n->get_arg(1);
            m_egraph.merge(na, nb, base_ptr() + l.index());
        }
        else {
            euf::enode* nb = sign ? m_false : m_true;
            m_egraph.merge(n, nb, base_ptr() + l.index());
        }
        // TBD: delay propagation?
        propagate();
    }

    void solver::propagate() {        
        m_egraph.propagate();
        if (m_egraph.inconsistent()) {       
            s().set_conflict(sat::justification::mk_ext_justification(s().scope_lvl(), m_conflict_idx.to_index()));
            return;
        }
        for (euf::enode* eq : m_egraph.new_eqs()) {
            bool_var v = m_expr2var.to_bool_var(eq->get_owner());
            s().assign(literal(v, false), sat::justification::mk_ext_justification(s().scope_lvl(), m_eq_idx.to_index()));
        }
        for (euf::enode* p : m_egraph.new_lits()) {
            expr* e = p->get_owner();
            bool sign = m.is_false(p->get_root()->get_owner());
            SASSERT(m.is_bool(e));
            SASSERT(m.is_true(p->get_root()->get_owner()) || sign);
            bool_var v = m_expr2var.to_bool_var(e);
            s().assign(literal(v, sign), sat::justification::mk_ext_justification(s().scope_lvl(), m_lit_idx.to_index()));
        }
    }

    sat::check_result solver::check() { 
        bool give_up = false;
        bool cont = false;
        for (auto* e : m_extensions)
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
        for (auto* e : m_extensions)
            e->push();
        m_egraph.push();
        ++m_num_scopes;
    }

    void solver::pop(unsigned n) {
        m_egraph.pop(n);
        for (auto* e : m_extensions)
            e->pop(n);
        if (n <= m_num_scopes) {
            m_num_scopes -= n;
            return;
        }
        n -= m_num_scopes;
        unsigned old_lim = m_bool_var_lim.size() - n;
        unsigned old_sz = m_bool_var_lim[old_lim];
        for (unsigned i = m_bool_var_trail.size(); i-- > old_sz; )
            m_var2node[m_bool_var_trail[i]] = enode_bool_pair(nullptr, false);
        m_bool_var_trail.shrink(old_sz);
        m_bool_var_lim.shrink(old_lim);
    }

    void solver::pre_simplify() {
        for (auto* e : m_extensions)
            e->pre_simplify();
    }

    void solver::simplify() {
        for (auto* e : m_extensions)
            e->simplify();
    }

    void solver::clauses_modifed() {
        for (auto* e : m_extensions)
            e->clauses_modifed();
    }

    lbool solver::get_phase(bool_var v) { 
        auto* ext = get_extension(v);
        if (ext)
            return ext->get_phase(v);
        return l_undef; 
    }

    std::ostream& solver::display(std::ostream& out) const {
        m_egraph.display(out);
        for (auto* e : m_extensions)
            e->display(out);
        return out; 
    }

    std::ostream& solver::display_justification(std::ostream& out, ext_justification_idx idx) const { 
        auto* ext = sat::index_base::to_extension(idx);
        if (ext != this)
            return ext->display_justification(out, idx);
        return out; 
    }

    std::ostream& solver::display_constraint(std::ostream& out, ext_constraint_idx idx) const { 
        auto* ext = sat::index_base::to_extension(idx);
        if (ext != this)
            return ext->display_constraint(out, idx);
        return out; 
    }

    void solver::collect_statistics(statistics& st) const {
        m_egraph.collect_statistics(st);
        for (auto* e : m_extensions)
            e->collect_statistics(st);
    }

    solver* solver::copy_core() {
        ast_manager& to = m_translate ? m_translate->to() : m;
        atom2bool_var& a2b = m_translate_expr2var ? *m_translate_expr2var : m_expr2var;
        auto* r = alloc(solver, to, a2b);
        std::function<void*(void*)> copy_justification = [&](void* x) { return (void*)(r->base_ptr() + ((unsigned*)x - base_ptr())); };
        r->m_egraph.copy_from(m_egraph, copy_justification);
        return r;
    }

    sat::extension* solver::copy(sat::solver* s) { 
        auto* r = copy_core();
        r->set_solver(s);
        for (auto* e : m_extensions)
            r->m_extensions.push_back(e->copy(s));
        return r;
    }

    sat::extension* solver::copy(sat::lookahead* s, bool learned) { 
        (void) learned;
        auto* r = copy_core();
        r->set_lookahead(s);
        for (auto* e : m_extensions)
            r->m_extensions.push_back(e->copy(s, learned));
        return r;
    }

    void solver::find_mutexes(literal_vector& lits, vector<literal_vector> & mutexes) {
        for (auto* e : m_extensions)
            e->find_mutexes(lits, mutexes);
    }

    void solver::gc() {
        for (auto* e : m_extensions)
            e->gc();
    }

    void solver::pop_reinit() {
        for (auto* e : m_extensions)
            e->pop_reinit();
    }

    bool solver::validate() { 
        for (auto* e : m_extensions)
            if (!e->validate())
                return false;
        return true; 
    }

    void solver::init_use_list(sat::ext_use_list& ul) {
        for (auto* e : m_extensions)
            e->init_use_list(ul);
    }

    bool solver::is_blocked(literal l, ext_constraint_idx idx) { 
        auto* ext = sat::index_base::to_extension(idx);
        if (ext != this)
            return is_blocked(l, idx);
        return false; 
    }

    bool solver::check_model(sat::model const& m) const { 
        for (auto* e : m_extensions)
            if (!e->check_model(m))
                return false;
        return true;
    }

    unsigned solver::max_var(unsigned w) const { 
        for (auto* e : m_extensions)
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

    sat::th_internalizer* solver::get_internalizer(expr* e) {
        if (is_app(e))
            return m_id2internalize.get(to_app(e)->get_family_id(), nullptr);
        if (m.is_iff(e)) {
            pb_util pb(m);
            return m_id2internalize.get(pb.get_family_id(), nullptr);
        }
        return nullptr;
    }
   
    sat::literal solver::internalize(sat::sat_internalizer& si, expr* e, bool sign, bool root) {
        auto* ext = get_internalizer(e);
        if (ext)
            return ext->internalize(si, e, sign, root);
        if (!m_true) {
            m_true = visit(si, m.mk_true());
            m_false = visit(si, m.mk_false());
        }
        SASSERT(!si.is_bool_op(e));
        sat::scoped_stack _sc(m_stack);
        unsigned sz = m_stack.size();
        euf::enode* n = visit(si, e);
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
                n = visit(si, arg);
                if (!n)
                    goto loop;
            }
            m_args.reset();
            for (unsigned i = 0; i < num; ++i)
                m_args.push_back(m_egraph.find(to_app(e)->get_arg(i)));
            n = m_egraph.mk(e, num, m_args.c_ptr());
            attach_bool_var(si, n);
        }        
        SASSERT(m_egraph.find(e));
        return literal(m_expr2var.to_bool_var(e), sign);
    }

    euf::enode* solver::visit(sat::sat_internalizer& si, expr* e) {
        euf::enode* n = m_egraph.find(e);
        if (n)
            return n;
        if (si.is_bool_op(e)) {
            sat::literal lit = si.internalize(e);
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
        attach_bool_var(si, n);
        return n;
    }

    void solver::attach_bool_var(sat::sat_internalizer& si, euf::enode* n) {
        expr* e = n->get_owner();
        if (m.is_bool(e)) {
            sat::bool_var v = si.add_bool_var(e);
            attach_bool_var(v, false, n);
        }
    }

    void solver::attach_bool_var(sat::bool_var v, bool sign, euf::enode* n) {
        m_var2node.reserve(v + 1, enode_bool_pair(nullptr, false));
        for (; m_num_scopes > 0; --m_num_scopes) 
            m_bool_var_lim.push_back(m_bool_var_trail.size());   
        SASSERT(m_var2node[v].first == nullptr);
        m_var2node[v] = euf::enode_bool_pair(n, sign);
        m_bool_var_trail.push_back(v);
    }

    model_converter* solver::get_model() {
        NOT_IMPLEMENTED_YET();
        return nullptr;
    }
 
}
