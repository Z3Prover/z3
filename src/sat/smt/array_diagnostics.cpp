/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    array_diagnostics.cpp

Abstract:

    Theory plugin for arrays, diagnostics functions

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

*/

#include "sat/smt/array_solver.h"
#include "sat/smt/euf_solver.h"

namespace array {
    std::ostream& solver::display(std::ostream& out) const {
        if (get_num_vars() > 0)
            out << "array\n";
        for (unsigned i = 0; i < get_num_vars(); ++i) {
            auto& d = get_var_data(i);
            out << var2enode(i)->get_expr_id() << " " << (d.m_prop_upward?"up":"fx") << " " << mk_bounded_pp(var2expr(i), m, 2) << "\n";
            display_info(out, "parent lambdas", d.m_parent_lambdas);
            display_info(out, "parent select", d.m_parent_selects);
            display_info(out, "lambdas", d.m_lambdas);
        }
        return out;
    }

    std::ostream& solver::display_info(std::ostream& out, char const* id, euf::enode_vector const& v) const {
        if (v.empty())
            return out;
        out << id << ":\n";
        for (euf::enode* p : v)
            out << "   " << ctx.bpp(p) << "\n";
        return out;
    }

    std::ostream& solver::display(std::ostream& out, axiom_record const& r) const {
        if (r.is_delayed())
            out << "delay ";
        switch (r.m_kind) {
        case axiom_record::kind_t::is_store:
            return out << "store " << ctx.bpp(r.n);            
        case axiom_record::kind_t::is_select:
            return out << "select " << ctx.bpp(r.n) << " " << ctx.bpp(r.select);
        case axiom_record::kind_t::is_default:
            return out << "default " << ctx.bpp(r.n);
        case axiom_record::kind_t::is_extensionality:
            return out << "extensionality " << ctx.bpp(r.n) << " " << ctx.bpp(r.select);
        case axiom_record::kind_t::is_congruence:
            return out << "congruence " << ctx.bpp(r.n) << " " << ctx.bpp(r.select);
        default:
            UNREACHABLE();
        }
        return out;
    }


    std::ostream& solver::display_justification(std::ostream& out, sat::ext_justification_idx idx) const { return out; }
    std::ostream& solver::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const { return out; }

    void solver::collect_statistics(statistics& st) const {
        st.update("array store",        m_stats.m_num_store_axiom);
        st.update("array sel/store",    m_stats.m_num_select_store_axiom);
        st.update("array sel/const",    m_stats.m_num_select_const_axiom);
        st.update("array sel/map",      m_stats.m_num_select_map_axiom);
        st.update("array sel/as array", m_stats.m_num_select_as_array_axiom);
        st.update("array sel/lambda",   m_stats.m_num_select_lambda_axiom);
        st.update("array def/map",      m_stats.m_num_default_map_axiom);
        st.update("array def/const",    m_stats.m_num_default_const_axiom);
        st.update("array def/store",    m_stats.m_num_default_store_axiom);
        st.update("array ext ax",       m_stats.m_num_extensionality_axiom);
        st.update("array cong ax",      m_stats.m_num_congruence_axiom);        
        st.update("array exp ax2",      m_stats.m_num_select_store_axiom_delayed);
        st.update("array splits",       m_stats.m_num_eq_splits);
    }

    void solver::validate_check() const {
        for (euf::enode* n : ctx.get_egraph().nodes()) {
            if (!ctx.is_relevant(n)) 
                continue;
            if (a.is_select(n->get_expr()) && a.is_store(n->get_arg(0)->get_expr()))
                validate_select_store(n);
            if (is_array(n) && n->is_root() && ctx.is_shared(n)) {
                for (euf::enode* k : ctx.get_egraph().nodes())
                    if (k->get_expr_id() > n->get_expr_id() && k->is_root() && is_array(k) && ctx.is_shared(k))
                        validate_extensionality(n, k);
            }
            expr* x = nullptr, *y = nullptr;
            if (m.is_eq(n->get_expr(), x, y) && a.is_array(x))
                std::cout << ctx.bpp(n) << " " << s().value(n->bool_var()) << "\n";
            if (m.is_eq(n->get_expr(), x, y) && a.is_array(x) && s().value(n->bool_var()) == l_false)
                validate_extensionality(expr2enode(x), expr2enode(y));
        }        
    }


    void solver::validate_select_store(euf::enode* n) const {
        SASSERT(a.is_select(n->get_expr()));
        SASSERT(a.is_store(n->get_arg(0)->get_expr()));
        bool same_args = true;
        for (unsigned i = 1; same_args && i < n->num_args(); ++i) 
            same_args = n->get_arg(i)->get_root() == n->get_arg(0)->get_arg(i)->get_root(); 
        if (same_args) {
            VERIFY(n->get_arg(0)->get_arg(n->num_args())->get_root() == n->get_root());
            return;
        }
        euf::enode_vector args;
        ptr_vector<expr> eargs;
        args.push_back(n->get_arg(0)->get_arg(0));
        for (unsigned i = 1; i < n->num_args(); ++i)
            args.push_back(n->get_arg(i));
        for (euf::enode* n : args)
            eargs.push_back(n->get_expr());
        expr_ref sel(a.mk_select(eargs.size(), eargs.data()), m);
        euf::enode* n1 = ctx.get_egraph().find(sel, args.size(), args.data());
        if (n1 && n1->get_root() == n->get_root())
            return;
        IF_VERBOSE(0, 
                   verbose_stream() << ctx.bpp(n) << "\n";
                   verbose_stream() << sel << "\n";
                   verbose_stream() << n1 << " " << n->get_root() << "\n";);
    }

    void solver::validate_extensionality(euf::enode* s, euf::enode* t) const {
        if (s->get_sort() != t->get_sort())
            return;
        IF_VERBOSE(0, 
                   verbose_stream() << "extensionality " << ctx.bpp(s) << " " << ctx.bpp(t) << "\n";);
    }

}
