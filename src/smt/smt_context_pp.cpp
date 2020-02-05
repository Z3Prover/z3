/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_context_pp.cpp

Abstract:

    SMT logical context: pretty printing

Author:

    Leonardo de Moura (leonardo) 2008-02-21.

Revision History:

--*/
#include "smt/smt_context.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "ast/ast_pp_util.h"
#include "util/stats.h"

namespace smt {


    std::ostream& context::display_last_failure(std::ostream& out) const {
        switch(m_last_search_failure) {
        case OK:
            return out << "OK";
        case UNKNOWN:
            return out << "UNKNOWN";
        case MEMOUT:
            return out << "MEMOUT";
        case CANCELED:
            return out << "CANCELED";
        case NUM_CONFLICTS:
            return out << "NUM_CONFLICTS";
        case RESOURCE_LIMIT:
            return out << "RESOURCE_LIMIT";
        case THEORY:
            if (!m_incomplete_theories.empty()) {
                bool first = true;
                for (theory* th : m_incomplete_theories) {
                    if (first) first = false; else out << " ";
                    out << th->get_name();
                }
            }
            else {
                out << "THEORY";
            }
            return out;
        case QUANTIFIERS:
            return out << "QUANTIFIERS";
        }
        UNREACHABLE();
        return out << "?";
    }

    std::string context::last_failure_as_string() const {
        std::string r;
        switch(m_last_search_failure) {
        case OK: r = m_unknown; break;
        case MEMOUT: r = "memout"; break;
        case CANCELED: r = "canceled"; break;
        case NUM_CONFLICTS: r = "max-conflicts-reached"; break;
        case THEORY: {
            r = "(incomplete (theory";
            for (theory* t : m_incomplete_theories) {
                r += " ";
                r += t->get_name();
            }
            r += "))";
            break;
        }
        case RESOURCE_LIMIT: r = "(resource limits reached)"; break;
        case QUANTIFIERS: r = "(incomplete quantifiers)"; break;
        case UNKNOWN: r = m_unknown; break;
        }
        return r;
    }

    void context::display_asserted_formulas(std::ostream & out) const {
        m_asserted_formulas.display_ll(out, get_pp_visited());
    }

    std::ostream& context::display_literal(std::ostream & out, literal l) const {
        l.display_compact(out, m_bool_var2expr.c_ptr()); return out;
    }

    std::ostream& context::display_literals(std::ostream & out, unsigned num_lits, literal const * lits) const {
        display_compact(out, num_lits, lits, m_bool_var2expr.c_ptr()); return out;
    }

    std::ostream& context::display_literal_verbose(std::ostream & out, literal lit) const {
        return display_literals_verbose(out, 1, &lit);
    }

    std::ostream& context::display_literals_verbose(std::ostream & out, unsigned num_lits, literal const * lits) const {
        display_verbose(out, m, num_lits, lits, m_bool_var2expr.c_ptr(), "\n"); return out;
    }

    std::ostream& context::display_literal_smt2(std::ostream& out, literal l) const {
        if (l.sign())
            out << "(not " << mk_pp(bool_var2expr(l.var()), m) << ") ";
        else
            out << mk_pp(bool_var2expr(l.var()), m) << " ";
        return out;
    }

    std::ostream& context::display_literals_smt2(std::ostream& out, unsigned num_lits, literal const* lits) const {
        for (unsigned i = 0; i < num_lits; ++i) {
            display_literal_smt2(out, lits[i]) << "\n";
        }
        return out;
    }

    void context::display_literal_info(std::ostream & out, literal l) const {
        l.display_compact(out, m_bool_var2expr.c_ptr());
        display_literal_smt2(out, l);
        out << "relevant: " << is_relevant(bool_var2expr(l.var())) << ", val: " << get_assignment(l) << "\n";
    }

    void context::display_watch_list(std::ostream & out, literal l) const {
        display_literal(out, l); out << " watch_list:\n";
        watch_list & wl = const_cast<watch_list &>(m_watches[l.index()]);
        watch_list::clause_iterator it  = wl.begin_clause();
        watch_list::clause_iterator end = wl.end_clause();
        for (; it != end; ++it) {
            display_clause(out, *it); out << "\n";
        }
    }

    void context::display_watch_lists(std::ostream & out) const {
        unsigned s = m_watches.size();
        for (unsigned l_idx = 0; l_idx < s; l_idx++) {
            literal l = to_literal(l_idx);
            display_watch_list(out, l);
            out << "\n";
        }
    }

    void context::display_enode_defs(std::ostream & out) const {
        for (enode * x : m_enodes) {
            expr * n = x->get_owner();
            ast_def_ll_pp(out, m, n, get_pp_visited(), true, false);
        }
    }

    void context::display_bool_var_defs(std::ostream & out) const {
        unsigned num = get_num_bool_vars();
        for (unsigned v = 0; v < num; v++) {
            expr * n = m_bool_var2expr[v];
            ast_def_ll_pp(out, m, n, get_pp_visited(), true, false);
        }
    }

    std::ostream& context::display_clause_detail(std::ostream & out, clause const * cls) const {
        out << "lemma: " << cls->is_lemma() << "\n";
        for (literal l : *cls) {
            display_literal(out, l);
            out << ", val: " << get_assignment(l) << ", lvl: " << get_assign_level(l)
                << ", ilvl: " << get_intern_level(l.var()) << ", var: " << l.var() << "\n"
                << mk_bounded_pp(bool_var2expr(l.var()), m, 2) << "\n\n";
        }
        return out;
    }

    std::ostream& context::display_clause(std::ostream & out, clause const * cls) const {
        cls->display_compact(out, m, m_bool_var2expr.c_ptr());
        return out;
    }

    std::ostream& context::display_clause_smt2(std::ostream & out, clause const& cls) const {
        return display_literals_smt2(out, cls.get_num_literals(), cls.begin());
    }

    std::ostream& context::display_clauses(std::ostream & out, ptr_vector<clause> const & v) const {
        for (clause* cp : v) {
            display_clause_smt2(out, *cp);
            out << "\n";
        }
        return out;
    }

    std::ostream& context::display_binary_clauses(std::ostream & out) const {
        bool first = true;
        unsigned l_idx = 0;
        for (watch_list const& wl : m_watches) {
            literal l1 = to_literal(l_idx++);
            literal neg_l1 = ~l1;
            literal const * it2  = wl.begin_literals();
            literal const * end2 = wl.end_literals();
            for (; it2 != end2; ++it2) {
                literal l2 = *it2;
                if (l1.index() < l2.index()) {
                    if (first) {
                        out << "binary clauses:\n";
                        first = false;
                    }
                    expr_ref t1(m), t2(m);
                    literal2expr(neg_l1, t1);
                    literal2expr(l2, t2);
                    expr_ref disj(m.mk_or(t1, t2), m);
                    out << mk_bounded_pp(disj, m, 3) << "\n";
#if 0
                    out << "(clause ";
                    display_literal(out, neg_l1);
                    out << " ";
                    display_literal(out, l2);
                    out << ")\n";
#endif
                }
            }
        }
        return out;
    }

    void context::display_assignment(std::ostream & out) const {
        if (!m_assigned_literals.empty()) {
            out << "current assignment:\n";
            for (literal lit : m_assigned_literals) {
                display_literal(out, lit);
                if (!is_relevant(lit)) out << " n ";
                out << ": ";
                display_verbose(out, m, 1, &lit, m_bool_var2expr.c_ptr());
                out << "\n";
            }
        }
    }

    void context::display_assignment_as_smtlib2(std::ostream& out, symbol const&  logic) const {
        ast_smt_pp pp(m);
        pp.set_benchmark_name("lemma");
        pp.set_status("unknown");
        pp.set_logic(logic);
        for (literal lit : m_assigned_literals) {
            expr_ref n(m);
            literal2expr(lit, n);
            pp.add_assumption(n);
        }
        pp.display_smt2(out, m.mk_true());
    }

    void context::display_eqc(std::ostream & out) const {
        bool first = true;
        for (enode * x : m_enodes) {
            expr * n = x->get_owner();
            expr * r = x->get_root()->get_owner();
            if (n != r) {
                if (first) {
                    out << "equivalence classes:\n";
                    first = false;
                }
                out << "#" << n->get_id() << " -> #" << r->get_id() << ": ";
                out << mk_pp(n, m) << " -> " << mk_pp(r, m) << "\n";
            }
        }
    }

    void context::display_app_enode_map(std::ostream & out) const {
        if (!m_e_internalized_stack.empty()) {
            out << "expression -> enode:\n";
            unsigned sz = m_e_internalized_stack.size();
            for (unsigned i = 0; i < sz; i++) {
                expr *  n = m_e_internalized_stack.get(i);
                out << "(#" << n->get_id() << " -> e!" << i << ") ";
            }
            out << "\n";
        }
    }

    void context::display_expr_bool_var_map(std::ostream & out) const {
        if (!m_b_internalized_stack.empty()) {
            out << "expression -> bool_var:\n";
            unsigned sz = m_b_internalized_stack.size();
            for (unsigned i = 0; i < sz; i++) {
                expr *  n  = m_b_internalized_stack.get(i);
                bool_var v = get_bool_var_of_id(n->get_id());
                out << "(#" << n->get_id() << " -> " << literal(v, false) << ") ";
            }
            out << "\n";
        }
    }

    void context::display_hot_bool_vars(std::ostream & out) const {
        out << "hot bool vars:\n";
        int num = get_num_bool_vars();
        for (bool_var v = 0; v < num; v++) {
            double val = get_activity(v)/m_bvar_inc;
            if (val > 10.00) {
                expr * n = m_b_internalized_stack.get(v);
                out << "#";
                out.width(5);
                out << std::left;
                out << n->get_id();
                out << "  ";
                out.width(12);
                out << std::right;
                out << get_activity(v) << "  ";
                out.width(12);
                out << val;
                out << "\n";
            }
        }
    }

    void context::display_relevant_exprs(std::ostream & out) const {
        m_relevancy_propagator->display(out);
    }

    void context::display_theories(std::ostream & out) const {
        for (theory* th : m_theory_set) {
            th->display(out);
        }
    }

    void context::display(std::ostream & out) const {
        get_pp_visited().reset();
        out << "Logical context:\n";
        out << "scope-lvl: " << m_scope_lvl << "\n";
        out << "base-lvl:  " << m_base_lvl  << "\n";
        out << "search-lvl:  " << m_search_lvl  << "\n";
        out << "inconsistent(): " << inconsistent() << "\n";
        out << "m_asserted_formulas.inconsistent(): " << m_asserted_formulas.inconsistent() << "\n";
        display_bool_var_defs(out);
        display_enode_defs(out);
        display_asserted_formulas(out);
        if (!m_aux_clauses.empty()) {
            out << "auxiliary clauses:\n";
            display_clauses(out, m_aux_clauses);
        }
        if (!m_lemmas.empty()) {
            out << "lemmas:\n";
            display_clauses(out, m_lemmas);
        }
        display_binary_clauses(out);
        display_assignment(out);
        display_eqc(out);
        m_cg_table.display_compact(out);
        m_case_split_queue->display(out);
        display_expr_bool_var_map(out);
        display_app_enode_map(out);
        display_relevant_exprs(out);
        display_theories(out);
        display_decl2enodes(out);
        display_hot_bool_vars(out);
    }

    void context::display_eq_detail(std::ostream & out, enode * n) const {
        SASSERT(n->is_eq());
        out << "#" << n->get_owner_id()
            << ", root: #" << n->get_root()->get_owner_id()
            << ", cg: #" << n->m_cg->get_owner_id()
            << ", val: " << get_assignment(enode2bool_var(n))
            << ", lhs: #" << n->get_arg(0)->get_owner_id()
            << ", rhs: #" << n->get_arg(1)->get_owner_id()
            << ", lhs->root: #" << n->get_arg(0)->get_root()->get_owner_id()
            << ", rhs->root: #" << n->get_arg(1)->get_root()->get_owner_id()
            << ", is_marked: " << n->is_marked()
            << ", is_relevant: " << is_relevant(n)
            << ", iscope_lvl: " << n->get_iscope_lvl() << "\n";
    }

    void context::display_parent_eqs(std::ostream & out, enode * n) const {
        for (enode* parent : n->get_parents()) {
            if (parent->is_eq())
                display_eq_detail(out, parent);
        }
    }

    void context::display_unsat_core(std::ostream & out) const {
        for (expr* c : m_unsat_core) {
            out << mk_pp(c, m) << "\n";
        }
    }

    void context::collect_statistics(::statistics & st) const {
        st.copy(m_aux_stats);
        st.update("conflicts", m_stats.m_num_conflicts);
        st.update("decisions", m_stats.m_num_decisions);
        st.update("propagations", m_stats.m_num_propagations + m_stats.m_num_bin_propagations);
        st.update("binary propagations", m_stats.m_num_bin_propagations);
        st.update("restarts", m_stats.m_num_restarts);
        st.update("final checks", m_stats.m_num_final_checks);
        st.update("added eqs", m_stats.m_num_add_eq);
        st.update("mk clause", m_stats.m_num_mk_clause);
        st.update("del clause", m_stats.m_num_del_clause);
        st.update("dyn ack", m_stats.m_num_dyn_ack);
        st.update("interface eqs", m_stats.m_num_interface_eqs);
        st.update("max generation", m_stats.m_max_generation);
        st.update("minimized lits", m_stats.m_num_minimized_lits);
        st.update("num checks", m_stats.m_num_checks);
        st.update("mk bool var", m_stats.m_num_mk_bool_var);

#if 0
        // missing?
        st.update("mk lit", m_stats.m_num_mk_lits);
        st.update("sat conflicts", m_stats.m_num_sat_conflicts);
        st.update("del bool var", m_stats.m_num_del_bool_var);
        st.update("mk enode", m_stats.m_num_mk_enode);
        st.update("del enode", m_stats.m_num_del_enode);
        st.update("mk bin clause", m_stats.m_num_mk_bin_clause);
        st.update("backwd subs", m_stats.m_num_bs);
        st.update("backwd subs res", m_stats.m_num_bsr);
        st.update("frwrd subs res", m_stats.m_num_fsr);
#endif
        m_qmanager->collect_statistics(st);
        m_asserted_formulas.collect_statistics(st);
        for (theory* th : m_theory_set) {
            th->collect_statistics(st);
        }
    }

    void context::display_statistics(std::ostream & out) const {
        ::statistics st;
        collect_statistics(st);
        st.display(out);
    }

    void context::display_istatistics(std::ostream & out) const {
        ::statistics st;
        collect_statistics(st);
        st.display_internal(out);
    }

    void context::display_lemma_as_smt_problem(std::ostream & out, unsigned num_antecedents, literal const * antecedents, literal consequent, symbol const& logic) const {
        ast_pp_util visitor(m);
        expr_ref_vector fmls(m);
        visitor.collect(fmls);
        expr_ref n(m);
        for (unsigned i = 0; i < num_antecedents; i++) {
            literal l = antecedents[i];
            literal2expr(l, n);
            fmls.push_back(std::move(n));
        }
        if (consequent != false_literal) {
            literal2expr(~consequent, n);
            fmls.push_back(std::move(n));
        }
        if (logic != symbol::null) out << "(set-logic " << logic << ")\n";
        visitor.collect(fmls);
        visitor.display_decls(out);
        visitor.display_asserts(out, fmls, true);
        out << "(check-sat)\n";
    }

    unsigned context::display_lemma_as_smt_problem(unsigned num_antecedents, literal const * antecedents, literal consequent, symbol const& logic) const {
        std::stringstream strm;
        strm << "lemma_" << (++m_lemma_id) << ".smt2";
        std::ofstream out(strm.str());
        TRACE("lemma", tout << strm.str() << "\n";);
        display_lemma_as_smt_problem(out, num_antecedents, antecedents, consequent, logic);
        TRACE("non_linear", display_lemma_as_smt_problem(tout, num_antecedents, antecedents, consequent, logic););
        out.close();
        return m_lemma_id;
    }

    void context::display_lemma_as_smt_problem(std::ostream & out, unsigned num_antecedents, literal const * antecedents,
                                               unsigned num_eq_antecedents, enode_pair const * eq_antecedents,
                                               literal consequent, symbol const& logic) const {
        ast_pp_util visitor(m);
        expr_ref_vector fmls(m);
        visitor.collect(fmls);
        expr_ref n(m);
        for (unsigned i = 0; i < num_antecedents; i++) {
            literal l = antecedents[i];
            literal2expr(l, n);
            fmls.push_back(n);
        }
        for (unsigned i = 0; i < num_eq_antecedents; i++) {
            enode_pair const & p = eq_antecedents[i];
            n = m.mk_eq(p.first->get_owner(), p.second->get_owner());
            fmls.push_back(n);
        }
        if (consequent != false_literal) {
            literal2expr(~consequent, n);
            fmls.push_back(n);
        }

        if (logic != symbol::null) out << "(set-logic " << logic << ")\n";
        visitor.collect(fmls);
        visitor.display_decls(out);
        visitor.display_asserts(out, fmls, true);
        out << "(check-sat)\n";
    }

    unsigned context::display_lemma_as_smt_problem(unsigned num_antecedents, literal const * antecedents,
                                               unsigned num_eq_antecedents, enode_pair const * eq_antecedents,
                                               literal consequent, symbol const& logic) const {
        std::stringstream strm;
        strm << "lemma_" << (++m_lemma_id) << ".smt2";
        std::ofstream out(strm.str());
        TRACE("lemma", tout << strm.str() << "\n";
              display_lemma_as_smt_problem(tout, num_antecedents, antecedents, num_eq_antecedents, eq_antecedents, consequent, logic);
);
        display_lemma_as_smt_problem(out, num_antecedents, antecedents, num_eq_antecedents, eq_antecedents, consequent, logic);
        out.close();
        return m_lemma_id;
    }

    /**
       \brief Display enode definitions #n := (f #i_1 ... #i_n), where #i_k is the root
       of the k-th argument of the enode #n.
     */
    void context::display_normalized_enodes(std::ostream & out) const {
        out << "normalized enodes:\n";
        for (enode * n : m_enodes) {
            out << "#";
            out.width(5);
            out << std::left << n->get_owner_id() << " #";
            out.width(5);
            out << n->get_root()->get_owner_id() << " := " << std::right;
            unsigned num = n->get_owner()->get_num_args();
            if (num > 0)
                out << "(";
            out << n->get_decl()->get_name();
            if (!n->get_decl()->private_parameters())
                display_parameters(out, n->get_decl()->get_num_parameters(), n->get_decl()->get_parameters());
            for (unsigned i = 0; i < num; i++) {
                expr * arg = n->get_owner()->get_arg(i);
                if (e_internalized(arg)) {
                    enode * n = get_enode(arg)->get_root();
                    out << " #" << n->get_owner_id();
                }
                else {
                    out << " #" << arg->get_id();
                }
            }
            if (num > 0)
                out << ")";
            if (is_relevant(n))
                out << "\t*";
            out << "\n";
        }
    }

    void context::display_enodes_lbls(std::ostream & out) const {
        for (enode* n : m_enodes) {
            n->display_lbls(out);
        }
    }

    void context::display_decl2enodes(std::ostream & out) const {
        out << "decl2enodes:\n";
        unsigned id = 0;
        for (enode_vector const& v : m_decl2enodes) {
            if (!v.empty()) {
                out << "id " << id << " ->";
                for (enode* n : v) {
                    out << " #" << n->get_owner_id();
                }
                out << "\n";
            }
            ++id;
        }
    }

    void context::display_subexprs_info(std::ostream & out, expr * n) const {
        ptr_buffer<expr> todo;
        todo.push_back(n);
        while (!todo.empty()) {
            expr * n = todo.back();
            todo.pop_back();
            out << "#";
            out.width(6);
            out << std::left << n->get_id();
            out << ", relevant: " << is_relevant(n);
            if (m.is_bool(n)) {
                out << ", val: ";
                out.width(7);
                out << std::right;
                if (lit_internalized(n))
                    out << get_assignment(n);
                else
                    out << "l_undef";
            }
            if (e_internalized(n)) {
                enode * e = get_enode(n);
                out << ", root: #" << e->get_root()->get_owner_id();
            }
            out << "\n";
            if (is_app(n)) {
                for (expr* arg : *to_app(n)) {
                    todo.push_back(arg);
                }
            }
        }
    }

    std::ostream& context::display(std::ostream& out, b_justification j) const {
        switch (j.get_kind()) {
        case b_justification::AXIOM:
            out << "axiom";
            break;
        case b_justification::BIN_CLAUSE: 
            out << "bin " << j.get_literal();
            break;
        case b_justification::CLAUSE: {
            clause * cls = j.get_clause();
            out << "clause ";
            if (cls) out << literal_vector(cls->get_num_literals(), cls->begin());
            if (cls) display_literals_smt2(out << "\n", cls->get_num_literals(), cls->begin());
            break;
        }
        case b_justification::JUSTIFICATION: {
            literal_vector lits;
            const_cast<conflict_resolution&>(*m_conflict_resolution).justification2literals(j.get_justification(), lits);
            out << "justification " << j.get_justification()->get_from_theory() << ": ";
            display_literals_smt2(out, lits);
            break;
        }
        default:
            UNREACHABLE();
            break;
        }
        return out << "\n";
    }

    void context::trace_assign(literal l, b_justification j, bool decision) const {
        SASSERT(m.has_trace_stream());
        std::ostream & out = m.trace_stream();
        out << "[assign] ";
        display_literal(out, l);
        if (decision)
            out << " decision";
        out << " ";
        display(out, j);
    }

    std::ostream& operator<<(std::ostream& out, enode_pp const& p) {
        ast_manager& m = p.ctx.get_manager();
        enode* n = p.n;
        return out << "[#" << n->get_owner_id() << " " << mk_bounded_pp(n->get_owner(), m) << "]";
    }

    std::ostream& operator<<(std::ostream& out, enode_eq_pp const& p) {
        return out << enode_pp(p.p.first, p.ctx) << " = " << enode_pp(p.p.second, p.ctx) << "\n";
    }



};

