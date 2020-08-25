/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_solver.cpp

Abstract:

    Solver plugin for EUF

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/
#include "sat/euf/euf_solver.h"
#include "sat/sat_solver.h"
#include "tactic/tactic_exception.h"

namespace euf_sat {

    bool solver::propagate(literal l, ext_constraint_idx idx) { 
        UNREACHABLE();
        return true;
    }

    void solver::get_antecedents(literal l, ext_justification_idx idx, literal_vector & r) {
        m_explain.reset();
        euf::enode* n = nullptr;
        bool sign = false;
        if (idx != 0) {
            auto p = m_var2node[l.var()];
            n = p.first;  
            sign = l.sign() != p.second;
        }

        switch (idx) {
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
        auto p = m_var2node[l.var()];
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
        m_egraph.propagate();
        if (m_egraph.inconsistent()) {       
            s().set_conflict(sat::justification::mk_ext_justification(s().scope_lvl(), 0));
            return;
        }
        for (euf::enode* eq : m_egraph.new_eqs()) {
            bool_var v = m_expr2var.to_bool_var(eq->get_owner());
            s().assign(literal(v, false), sat::justification::mk_ext_justification(s().scope_lvl(), 1));
        }
        for (euf::enode* p : m_egraph.new_lits()) {
            expr* e = p->get_owner();
            bool sign = m.is_false(p->get_root()->get_owner());
            SASSERT(m.is_bool(e));
            SASSERT(m.is_true(p->get_root()->get_owner()) || sign);
            bool_var v = m_expr2var.to_bool_var(e);
            s().assign(literal(v, sign), sat::justification::mk_ext_justification(s().scope_lvl(), 2));
        }
    }

    sat::check_result solver::check() { 
        return sat::CR_DONE; 
    }
    void solver::push() {
        m_egraph.push();
    }
    void solver::pop(unsigned n) {
        m_egraph.pop(n);
    }
    void solver::pre_simplify() {}
    void solver::simplify() {}
    // have a way to replace l by r in all constraints
    void solver::clauses_modifed() {}
    lbool solver::get_phase(bool_var v) { return l_undef; }
    std::ostream& solver::display(std::ostream& out) const {
        m_egraph.display(out);
        return out; 
    }
    std::ostream& solver::display_justification(std::ostream& out, ext_justification_idx idx) const { return out; }
    std::ostream& solver::display_constraint(std::ostream& out, ext_constraint_idx idx) const { return out; }
    void solver::collect_statistics(statistics& st) const {}
    sat::extension* solver::copy(sat::solver* s) { return nullptr; }       
    sat::extension* solver::copy(sat::lookahead* s, bool learned) { return nullptr; }       
    void solver::find_mutexes(literal_vector& lits, vector<literal_vector> & mutexes) {}
    void solver::gc() {}
    void solver::pop_reinit() {}
    bool solver::validate() { return true; }
    void solver::init_use_list(sat::ext_use_list& ul) {}
    bool solver::is_blocked(literal l, ext_constraint_idx) { return false; }
    bool solver::check_model(sat::model const& m) const { return true;}
    unsigned solver::max_var(unsigned w) const { return w; }
   
    void solver::internalize(sat_internalizer& si, expr* e) {
        SASSERT(!si.is_bool_op(e));
        unsigned sz = m_stack.size();
        euf::enode* n = visit(si, e);
        while (m_stack.size() > sz) {
        loop:
            if (!m.inc())
                throw tactic_exception(m.limit().get_cancel_msg());
            frame & fr = m_stack.back();
            expr* e = fr.m_e;
            if (m_egraph.find(e)) {
                m_stack.pop_back();
                continue;
            }
            unsigned num = is_app(e) ? to_app(e)->get_num_args() : 0;
            m_args.reset();
            while (fr.m_idx < num) {
                expr* arg = to_app(e)->get_arg(fr.m_idx);
                fr.m_idx++;
                n = visit(si, arg);
                if (!n)
                    goto loop;
                m_args.push_back(n);
            }
            n = m_egraph.mk(e, num, m_args.c_ptr());
            attach_bool_var(si, n);
        }        
        SASSERT(m_egraph.find(e));
    }

    euf::enode* solver::visit(sat_internalizer& si, expr* e) {
        euf::enode* n = m_egraph.find(e);
        if (n)
            return n;
        if (si.is_bool_op(e)) {
            sat::literal lit = si.internalize(e);
            n = m_egraph.mk(e, 0, nullptr);
            attach_bool_var(lit.var(), lit.sign(), n);
            s().set_external(lit.var());
            return n;
        }
        if (is_app(e) && to_app(e)->get_num_args() > 0)
            return nullptr;
        n = m_egraph.mk(e, 0, nullptr);
        attach_bool_var(si, n);
        return n;
    }

    void solver::attach_bool_var(sat_internalizer& si, euf::enode* n) {
        expr* e = n->get_owner();
        if (m.is_bool(e)) {
            sat::bool_var v = si.add_bool_var(e);
            attach_bool_var(v, false, n);
        }
    }

    void solver::attach_bool_var(sat::bool_var v, bool sign, euf::enode* n) {
        m_var2node.reserve(v + 1);
        m_var2node[v] = euf::enode_bool_pair(n, sign);
    }
 
}
