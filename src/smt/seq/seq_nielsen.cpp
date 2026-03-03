/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_nielsen.cpp

Abstract:

    Nielsen graph implementation for string constraint solving.

    Ports the constraint types and Nielsen graph structures from
    ZIPT (https://github.com/CEisenhofer/ZIPT/tree/parikh/ZIPT/Constraints)

Author:

    Nikolaj Bjorner (nbjorner) 2026-03-02
    Clemens Eisenhofer 2026-03-02

--*/

#include "smt/seq/seq_nielsen.h"
#include "ast/ast_pp.h"

namespace seq {

    // -----------------------------------------------
    // dep_tracker
    // -----------------------------------------------

    dep_tracker::dep_tracker(unsigned num_bits) {
        unsigned words = (num_bits + 31) / 32;
        m_bits.resize(words, 0);
    }

    dep_tracker::dep_tracker(unsigned num_bits, unsigned set_bit) {
        unsigned words = (num_bits + 31) / 32;
        m_bits.resize(words, 0);
        if (set_bit < num_bits) {
            unsigned word_idx = set_bit / 32;
            unsigned bit_idx = set_bit % 32;
            m_bits[word_idx] = 1u << bit_idx;
        }
    }

    void dep_tracker::merge(dep_tracker const& other) {
        if (other.m_bits.empty())
            return;
        if (m_bits.size() < other.m_bits.size())
            m_bits.resize(other.m_bits.size(), 0);
        for (unsigned i = 0; i < other.m_bits.size(); ++i)
            m_bits[i] |= other.m_bits[i];
    }

    bool dep_tracker::is_superset(dep_tracker const& other) const {
        for (unsigned i = 0; i < other.m_bits.size(); ++i) {
            unsigned my_bits = (i < m_bits.size()) ? m_bits[i] : 0;
            if ((my_bits & other.m_bits[i]) != other.m_bits[i])
                return false;
        }
        return true;
    }

    bool dep_tracker::empty() const {
        for (unsigned b : m_bits)
            if (b != 0) return false;
        return true;
    }

    // -----------------------------------------------
    // str_eq
    // -----------------------------------------------

    void str_eq::sort() {
        if (m_lhs && m_rhs && m_lhs->id() > m_rhs->id())
            std::swap(m_lhs, m_rhs);
    }

    bool str_eq::is_trivial() const {
        return m_lhs == m_rhs ||
               (m_lhs && m_rhs && m_lhs->is_empty() && m_rhs->is_empty());
    }

    bool str_eq::contains_var(euf::snode* var) const {
        if (!var) return false;
        // check if var appears in the token list of lhs or rhs
        if (m_lhs) {
            euf::snode_vector tokens;
            m_lhs->collect_tokens(tokens);
            for (euf::snode* t : tokens)
                if (t == var) return true;
        }
        if (m_rhs) {
            euf::snode_vector tokens;
            m_rhs->collect_tokens(tokens);
            for (euf::snode* t : tokens)
                if (t == var) return true;
        }
        return false;
    }

    // -----------------------------------------------
    // str_mem
    // -----------------------------------------------

    bool str_mem::is_primitive() const {
        return m_str && m_str->length() == 1 && m_str->is_var();
    }

    bool str_mem::contains_var(euf::snode* var) const {
        if (!var) return false;
        if (m_str) {
            euf::snode_vector tokens;
            m_str->collect_tokens(tokens);
            for (euf::snode* t : tokens)
                if (t == var) return true;
        }
        return false;
    }

    // -----------------------------------------------
    // nielsen_subst
    // -----------------------------------------------

    bool nielsen_subst::is_eliminating() const {
        if (!m_var || !m_replacement) return true;
        // check if var appears in replacement
        euf::snode_vector tokens;
        m_replacement->collect_tokens(tokens);
        for (euf::snode* t : tokens)
            if (t == m_var) return false;
        return true;
    }

    // -----------------------------------------------
    // nielsen_edge
    // -----------------------------------------------

    nielsen_edge::nielsen_edge(nielsen_node* src, nielsen_node* tgt, bool is_progress):
        m_src(src), m_tgt(tgt), m_is_progress(is_progress) {
    }

    // -----------------------------------------------
    // nielsen_node
    // -----------------------------------------------

    nielsen_node::nielsen_node(nielsen_graph* graph, unsigned id):
        m_id(id), m_graph(graph), m_is_progress(true) {
    }

    void nielsen_node::clone_from(nielsen_node const& parent) {
        m_str_eq.reset();
        m_str_mem.reset();
        for (auto const& eq : parent.m_str_eq)
            m_str_eq.push_back(str_eq(eq.m_lhs, eq.m_rhs, eq.m_dep));
        for (auto const& mem : parent.m_str_mem)
            m_str_mem.push_back(str_mem(mem.m_str, mem.m_regex, mem.m_history, mem.m_id, mem.m_dep));
    }

    void nielsen_node::apply_subst(euf::sgraph& sg, nielsen_subst const& s) {
        if (!s.m_var) return;
        for (unsigned i = 0; i < m_str_eq.size(); ++i) {
            str_eq& eq = m_str_eq[i];
            eq.m_lhs = sg.subst(eq.m_lhs, s.m_var, s.m_replacement);
            eq.m_rhs = sg.subst(eq.m_rhs, s.m_var, s.m_replacement);
            eq.m_dep.merge(s.m_dep);
            eq.sort();
        }
        for (unsigned i = 0; i < m_str_mem.size(); ++i) {
            str_mem& mem = m_str_mem[i];
            mem.m_str = sg.subst(mem.m_str, s.m_var, s.m_replacement);
            // regex is typically ground, but apply subst for generality
            mem.m_regex = sg.subst(mem.m_regex, s.m_var, s.m_replacement);
            mem.m_dep.merge(s.m_dep);
        }
    }

    // -----------------------------------------------
    // nielsen_graph
    // -----------------------------------------------

    nielsen_graph::nielsen_graph(euf::sgraph& sg):
        m_sg(sg) {
    }

    nielsen_graph::~nielsen_graph() {
        reset();
    }

    nielsen_node* nielsen_graph::mk_node() {
        unsigned id = m_nodes.size();
        nielsen_node* n = alloc(nielsen_node, this, id);
        m_nodes.push_back(n);
        return n;
    }

    nielsen_node* nielsen_graph::mk_child(nielsen_node* parent) {
        nielsen_node* child = mk_node();
        child->clone_from(*parent);
        return child;
    }

    nielsen_edge* nielsen_graph::mk_edge(nielsen_node* src, nielsen_node* tgt, bool is_progress) {
        nielsen_edge* e = alloc(nielsen_edge, src, tgt, is_progress);
        m_edges.push_back(e);
        src->add_outgoing(e);
        return e;
    }

    void nielsen_graph::add_str_eq(euf::snode* lhs, euf::snode* rhs) {
        if (!m_root)
            m_root = mk_node();
        dep_tracker dep(m_root->str_eqs().size() + m_root->str_mems().size() + 1,
                        m_root->str_eqs().size());
        str_eq eq(lhs, rhs, dep);
        eq.sort();
        m_root->add_str_eq(eq);
    }

    void nielsen_graph::add_str_mem(euf::snode* str, euf::snode* regex) {
        if (!m_root)
            m_root = mk_node();
        dep_tracker dep(m_root->str_eqs().size() + m_root->str_mems().size() + 1,
                        m_root->str_eqs().size() + m_root->str_mems().size());
        euf::snode* history = m_sg.mk_empty();
        unsigned id = next_mem_id();
        m_root->add_str_mem(str_mem(str, regex, history, id, dep));
    }

    void nielsen_graph::inc_run_idx() {
        if (m_run_idx == UINT_MAX) {
            for (nielsen_node* n : m_nodes)
                n->reset_counter();
            m_run_idx = 1;
        }
        else
            ++m_run_idx;
    }

    void nielsen_graph::reset() {
        for (nielsen_node* n : m_nodes)
            dealloc(n);
        for (nielsen_edge* e : m_edges)
            dealloc(e);
        m_nodes.reset();
        m_edges.reset();
        m_root = nullptr;
        m_run_idx = 0;
        m_depth_bound = 0;
        m_next_mem_id = 0;
    }

    std::ostream& nielsen_graph::display(std::ostream& out) const {
        out << "nielsen_graph with " << m_nodes.size() << " nodes, "
            << m_edges.size() << " edges\n";

        for (nielsen_node const* n : m_nodes) {
            out << "  node[" << n->id() << "]";
            if (n == m_root)
                out << " (root)";
            if (n->is_general_conflict())
                out << " CONFLICT";
            if (n->is_extended())
                out << " EXTENDED";
            out << "\n";

            // display string equalities
            for (auto const& eq : n->str_eqs()) {
                out << "    str_eq: ";
                if (eq.m_lhs) out << "lhs[id=" << eq.m_lhs->id() << ",len=" << eq.m_lhs->length() << "]";
                else out << "null";
                out << " = ";
                if (eq.m_rhs) out << "rhs[id=" << eq.m_rhs->id() << ",len=" << eq.m_rhs->length() << "]";
                else out << "null";
                out << "\n";
            }

            // display regex memberships
            for (auto const& mem : n->str_mems()) {
                out << "    str_mem[" << mem.m_id << "]: ";
                if (mem.m_str) out << "str[id=" << mem.m_str->id() << ",len=" << mem.m_str->length() << "]";
                else out << "null";
                out << " in ";
                if (mem.m_regex) out << "re[id=" << mem.m_regex->id() << "]";
                else out << "null";
                out << "\n";
            }

            // display outgoing edges
            for (nielsen_edge const* e : n->outgoing()) {
                out << "    -> node[" << e->tgt()->id() << "]";
                if (e->is_progress()) out << " (progress)";
                for (auto const& s : e->subst()) {
                    out << " {";
                    if (s.m_var) out << "var[" << s.m_var->id() << "]";
                    out << " -> ";
                    if (s.m_replacement) out << "repl[" << s.m_replacement->id() << ",len=" << s.m_replacement->length() << "]";
                    else out << "eps";
                    out << "}";
                }
                out << "\n";
            }

            if (n->backedge())
                out << "    backedge -> node[" << n->backedge()->id() << "]\n";
        }

        return out;
    }

    // -----------------------------------------------------------------------
    // nielsen_node: simplify_and_init
    // -----------------------------------------------------------------------

    simplify_result nielsen_node::simplify_and_init(nielsen_graph& g) {
        euf::sgraph& sg = g.sg();
        bool changed = true;

        while (changed) {
            changed = false;

            // pass 1: remove trivially satisfied equalities
            unsigned wi = 0;
            for (unsigned i = 0; i < m_str_eq.size(); ++i) {
                str_eq& eq = m_str_eq[i];
                if (eq.is_trivial())
                    continue;
                m_str_eq[wi++] = eq;
            }
            if (wi < m_str_eq.size()) {
                m_str_eq.shrink(wi);
                changed = true;
            }

            // pass 2: detect symbol clashes and empty-propagation
            for (str_eq& eq : m_str_eq) {
                if (!eq.m_lhs || !eq.m_rhs)
                    continue;

                // both sides start with a concrete character: check match
                if (eq.m_lhs->is_char() && eq.m_rhs->is_char()) {
                    if (eq.m_lhs->id() != eq.m_rhs->id()) {
                        // symbol clash
                        m_is_general_conflict = true;
                        m_reason = backtrack_reason::symbol_clash;
                        return simplify_result::conflict;
                    }
                    // same char: drop from both sides
                    eq.m_lhs = sg.drop_first(eq.m_lhs);
                    eq.m_rhs = sg.drop_first(eq.m_rhs);
                    changed = true;
                    continue;
                }

                // one side empty, the other not empty => conflict or substitution
                if (eq.m_lhs->is_empty() && !eq.m_rhs->is_empty()) {
                    // rhs must also be empty; if it is a concrete non-empty string => conflict
                    if (eq.m_rhs->is_char() || eq.m_rhs->is_concat()) {
                        // check if rhs has any non-variable tokens
                        euf::snode_vector tokens;
                        eq.m_rhs->collect_tokens(tokens);
                        bool all_vars = true;
                        for (euf::snode* t : tokens)
                            if (!t->is_var()) { all_vars = false; break; }
                        if (!all_vars) {
                            m_is_general_conflict = true;
                            m_reason = backtrack_reason::symbol_clash;
                            return simplify_result::conflict;
                        }
                        // substitute: every variable in rhs -> empty
                        for (euf::snode* t : tokens) {
                            if (t->is_var()) {
                                nielsen_subst s(t, sg.mk_empty(), eq.m_dep);
                                apply_subst(sg, s);
                                changed = true;
                            }
                        }
                    }
                    continue;
                }
                if (eq.m_rhs->is_empty() && !eq.m_lhs->is_empty()) {
                    euf::snode_vector tokens;
                    eq.m_lhs->collect_tokens(tokens);
                    bool all_vars = true;
                    for (euf::snode* t : tokens)
                        if (!t->is_var()) { all_vars = false; break; }
                    if (!all_vars) {
                        m_is_general_conflict = true;
                        m_reason = backtrack_reason::symbol_clash;
                        return simplify_result::conflict;
                    }
                    for (euf::snode* t : tokens) {
                        if (t->is_var()) {
                            nielsen_subst s(t, sg.mk_empty(), eq.m_dep);
                            apply_subst(sg, s);
                            changed = true;
                        }
                    }
                    continue;
                }

                // prefix matching: lhs and rhs both start with the same char => cancel
                {
                    euf::snode_vector lhs_toks, rhs_toks;
                    eq.m_lhs->collect_tokens(lhs_toks);
                    eq.m_rhs->collect_tokens(rhs_toks);
                    unsigned prefix = 0;
                    while (prefix < lhs_toks.size() && prefix < rhs_toks.size() &&
                           lhs_toks[prefix]->is_char() && rhs_toks[prefix]->is_char()) {
                        if (lhs_toks[prefix]->id() != rhs_toks[prefix]->id()) {
                            m_is_general_conflict = true;
                            m_reason = backtrack_reason::symbol_clash;
                            return simplify_result::conflict;
                        }
                        ++prefix;
                    }
                    if (prefix > 0) {
                        eq.m_lhs = sg.drop_left(eq.m_lhs, prefix);
                        eq.m_rhs = sg.drop_left(eq.m_rhs, prefix);
                        changed = true;
                    }
                }
            }
        }

        // check for regex memberships that are immediately infeasible
        for (str_mem& mem : m_str_mem) {
            if (!mem.m_str || !mem.m_regex)
                continue;
            if (mem.m_str->is_empty() && !mem.m_regex->is_nullable()) {
                m_is_general_conflict = true;
                m_reason = backtrack_reason::regex;
                return simplify_result::conflict;
            }
        }

        if (is_satisfied())
            return simplify_result::satisfied;

        return simplify_result::proceed;
    }

    bool nielsen_node::is_satisfied() const {
        for (str_eq const& eq : m_str_eq)
            if (!eq.is_trivial()) return false;
        return m_str_mem.empty();
    }

    bool nielsen_node::is_subsumed_by(nielsen_node const& other) const {
        // check if every constraint in 'other' also appears in 'this'
        for (str_eq const& oeq : other.m_str_eq) {
            bool found = false;
            for (str_eq const& teq : m_str_eq)
                if (teq == oeq) { found = true; break; }
            if (!found) return false;
        }
        for (str_mem const& omem : other.m_str_mem) {
            bool found = false;
            for (str_mem const& tmem : m_str_mem)
                if (tmem == omem) { found = true; break; }
            if (!found) return false;
        }
        return true;
    }

    // -----------------------------------------------------------------------
    // nielsen_graph: search
    // -----------------------------------------------------------------------

    nielsen_graph::search_result nielsen_graph::solve() {
        if (!m_root)
            return search_result::sat;

        m_depth_bound = 10;
        for (unsigned iter = 0; iter < 6; ++iter, m_depth_bound *= 2) {
            inc_run_idx();
            search_result r = search_dfs(m_root, 0);
            if (r != search_result::unknown)
                return r;
            // depth limit hit – increase bound
        }
        return search_result::unknown;
    }

    nielsen_graph::search_result nielsen_graph::search_dfs(nielsen_node* node, unsigned depth) {
        simplify_result sr = node->simplify_and_init(*this);

        if (sr == simplify_result::conflict)
            return search_result::unsat;
        if (sr == simplify_result::satisfied || node->is_satisfied())
            return search_result::sat;

        if (depth >= m_depth_bound)
            return search_result::unknown;

        if (!generate_extensions(node, depth))
            return search_result::unsat;

        bool any_unknown = false;
        for (nielsen_edge* e : node->outgoing()) {
            nielsen_node* child = e->tgt();
            search_result r = search_dfs(child, depth + 1);
            if (r == search_result::sat)
                return search_result::sat;
            if (r == search_result::unknown)
                any_unknown = true;
        }
        return any_unknown ? search_result::unknown : search_result::unsat;
    }

    simplify_result nielsen_graph::simplify_node(nielsen_node* node) {
        return node->simplify_and_init(*this);
    }

    bool nielsen_graph::generate_extensions(nielsen_node* node, unsigned /*depth*/) {
        // find the first non-trivial string equality to split on
        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial())
                continue;
            if (!eq.m_lhs || !eq.m_rhs)
                continue;

            euf::snode_vector lhs_toks, rhs_toks;
            eq.m_lhs->collect_tokens(lhs_toks);
            eq.m_rhs->collect_tokens(rhs_toks);

            if (lhs_toks.empty() || rhs_toks.empty())
                continue;

            euf::snode* lhead = lhs_toks[0];
            euf::snode* rhead = rhs_toks[0];

            // Det modifier: if one side starts with a variable whose other side is empty
            if (lhead->is_var() && eq.m_rhs->is_empty()) {
                // substitute lhead -> empty
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                nielsen_subst s(lhead, m_sg.mk_empty(), eq.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
                return true;
            }
            if (rhead->is_var() && eq.m_lhs->is_empty()) {
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                nielsen_subst s(rhead, m_sg.mk_empty(), eq.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
                return true;
            }

            // Const Nielsen modifier: lhs starts with char, rhs starts with var
            // -> substitute rhs_var = char . fresh_var
            if (lhead->is_char() && rhead->is_var()) {
                std::string fresh_str = "v!" + std::to_string(node->id());
                symbol fresh_name(fresh_str.c_str());
                euf::snode* fresh = m_sg.mk_var(fresh_name);
                euf::snode* replacement = m_sg.mk_concat(lhead, fresh);

                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                nielsen_subst s(rhead, replacement, eq.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
                return true;
            }

            if (rhead->is_char() && lhead->is_var()) {
                std::string fresh_str = "v!" + std::to_string(node->id());
                symbol fresh_name(fresh_str.c_str());
                euf::snode* fresh = m_sg.mk_var(fresh_name);
                euf::snode* replacement = m_sg.mk_concat(rhead, fresh);

                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                nielsen_subst s(lhead, replacement, eq.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
                return true;
            }

            // Eq split modifier: both sides start with variables x.A = y.B
            // Produce three children:
            //   1) x = eps, A = y.B
            //   2) x = y, A = B  (when len(x) = len(y))
            //   3) y = eps, x.A = B
            if (lhead->is_var() && rhead->is_var()) {
                // child 1: lhead -> eps
                {
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, true);
                    nielsen_subst s(lhead, m_sg.mk_empty(), eq.m_dep);
                    e->add_subst(s);
                    child->apply_subst(m_sg, s);
                }
                // child 2: lhead = rhead (if different vars, substitute lhead -> rhead)
                if (lhead->id() != rhead->id()) {
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, false);
                    nielsen_subst s(lhead, rhead, eq.m_dep);
                    e->add_subst(s);
                    child->apply_subst(m_sg, s);
                }
                // child 3: rhead -> eps
                {
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, true);
                    nielsen_subst s(rhead, m_sg.mk_empty(), eq.m_dep);
                    e->add_subst(s);
                    child->apply_subst(m_sg, s);
                }
                return true;
            }

            // no applicable modifier for this equality; try next
        }

        // no extension was generated
        return false;
    }

    void nielsen_graph::collect_conflict_deps(dep_tracker& deps) const {
        for (nielsen_node const* n : m_nodes) {
            if (!n->is_currently_conflict())
                continue;
            for (str_eq const& eq : n->str_eqs())
                deps.merge(eq.m_dep);
            for (str_mem const& mem : n->str_mems())
                deps.merge(mem.m_dep);
        }
    }

}

