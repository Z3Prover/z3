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
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "util/bit_util.h"
#include "util/hashtable.h"
#include <sstream>

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

    void dep_tracker::get_set_bits(unsigned_vector& indices) const {
        for (unsigned i = 0; i < m_bits.size(); ++i) {
            unsigned word = m_bits[i];
            while (word != 0) {
                unsigned bit = i * 32 + ntz_core(word);
                indices.push_back(bit);
                word &= word - 1; // clear lowest set bit
            }
        }
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
        ++m_num_input_eqs;
    }

    void nielsen_graph::add_str_mem(euf::snode* str, euf::snode* regex) {
        if (!m_root)
            m_root = mk_node();
        dep_tracker dep(m_root->str_eqs().size() + m_root->str_mems().size() + 1,
                        m_root->str_eqs().size() + m_root->str_mems().size());
        euf::snode* history = m_sg.mk_empty();
        unsigned id = next_mem_id();
        m_root->add_str_mem(str_mem(str, regex, history, id, dep));
        ++m_num_input_mems;
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
        m_sat_node = nullptr;
        m_sat_path.reset();
        m_run_idx = 0;
        m_depth_bound = 0;
        m_next_mem_id = 0;
        m_fresh_cnt = 0;
        m_num_input_eqs = 0;
        m_num_input_mems = 0;
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
    // nielsen_node: display_html
    // Render constraint set as an HTML fragment for DOT labels.
    // Mirrors ZIPT's NielsenNode.ToHtmlString().
    // -----------------------------------------------------------------------

    // Helper: HTML-escape a string and replace literal \n with <br/>.
    static std::string dot_html_escape(std::string const& s) {
        std::string r;
        r.reserve(s.size());
        for (char c : s) {
            switch (c) {
            case '&': r += "&amp;"; break;
            case '<': r += "&lt;";  break;
            case '>': r += "&gt;";  break;
            default:  r += c;       break;
            }
        }
        // replace literal "\n" two-char sequence with <br/>
        std::string result;
        result.reserve(r.size());
        for (std::size_t i = 0; i < r.size(); ) {
            if (i + 1 < r.size() && r[i] == '\\' && r[i+1] == 'n') {
                result += "<br/>";
                i += 2;
            } else {
                result += r[i++];
            }
        }
        return result;
    }

    // Helper: render an snode as a short label (expression text or id).
    static std::string snode_label(euf::snode const* n, ast_manager& m) {
        if (!n) return "null";
        if (n->get_expr()) {
            std::ostringstream os;
            os << mk_pp(n->get_expr(), m);
            return os.str();
        }
        return "#" + std::to_string(n->id());
    }

    std::ostream& nielsen_node::display_html(std::ostream& out, ast_manager& m) const {
        bool any = false;

        // string equalities
        for (auto const& eq : m_str_eq) {
            if (!any) { out << "Cnstr:<br/>"; any = true; }
            out << dot_html_escape(snode_label(eq.m_lhs, m))
                << " = "
                << dot_html_escape(snode_label(eq.m_rhs, m))
                << "<br/>";
        }
        // regex memberships
        for (auto const& mem : m_str_mem) {
            if (!any) { out << "Cnstr:<br/>"; any = true; }
            out << dot_html_escape(snode_label(mem.m_str, m))
                << " &#8712; "
                << dot_html_escape(snode_label(mem.m_regex, m))
                << "<br/>";
        }

        if (!any)
            out << "&#8868;"; // ⊤ (trivially satisfied)
        return out;
    }

    // -----------------------------------------------------------------------
    // nielsen_graph: to_dot
    // Output the graph in graphviz DOT format, optionally colour-highlighting
    // the satisfying path.  Mirrors ZIPT's NielsenGraph.ToDot().
    // -----------------------------------------------------------------------

    // Convert a backtrack_reason to a short display string.
    static char const* reason_to_str(backtrack_reason r) {
        switch (r) {
        case backtrack_reason::unevaluated:      return "Unevaluated";
        case backtrack_reason::extended:         return "Extended";
        case backtrack_reason::symbol_clash:     return "Symbol Clash";
        case backtrack_reason::parikh_image:     return "Parikh Image";
        case backtrack_reason::subsumption:      return "Subsumption";
        case backtrack_reason::arithmetic:       return "Arithmetic";
        case backtrack_reason::regex:            return "Regex";
        case backtrack_reason::regex_widening:   return "RegexWidening";
        case backtrack_reason::character_range:  return "Character Range";
        case backtrack_reason::smt:              return "SMT";
        case backtrack_reason::children_failed:  return "Children Failed";
        default:                                 return "?";
        }
    }

    // Returns true when the reason is a direct (non-propagated) conflict.
    // Mirrors ZIPT's NielsenNode.IsActualConflict(): all conflicts except ChildrenFailed.
    static bool is_actual_conflict(backtrack_reason r) {
        return r == backtrack_reason::symbol_clash
            || r == backtrack_reason::parikh_image
            || r == backtrack_reason::subsumption
            || r == backtrack_reason::arithmetic
            || r == backtrack_reason::regex
            || r == backtrack_reason::regex_widening
            || r == backtrack_reason::character_range
            || r == backtrack_reason::smt;
    }

    std::ostream& nielsen_graph::to_dot(std::ostream& out) const {
        ast_manager& m = m_sg.get_manager();

        // collect sat-path nodes and edges for green highlighting
        ptr_addr_hashtable<nielsen_node> sat_nodes;
        ptr_addr_hashtable<nielsen_edge> sat_edges;
        for (nielsen_edge* e : m_sat_path) {
            if (e->src()) sat_nodes.insert(e->src());
            if (e->tgt()) sat_nodes.insert(e->tgt());
            sat_edges.insert(e);
        }

        out << "digraph G {\n";

        // --- nodes ---
        for (nielsen_node const* n : m_nodes) {
            out << "\t" << n->id() << " [label=<"
                << n->id() << ": ";
            n->display_html(out, m);
            // append conflict reason if this is a direct conflict
            if (is_actual_conflict(n->reason()))
                out << "<br/>" << reason_to_str(n->reason());
            out << ">";

            // colour
            if (sat_nodes.contains(const_cast<nielsen_node*>(n)))
                out << ", color=green";
            else if (n->is_general_conflict())
                out << ", color=darkred";
            else if (n->eval_idx() != m_run_idx)  // inactive (not visited this run)
                out << ", color=blue";
            else if (n->is_currently_conflict())
                out << ", color=red";

            out << "];\n";
        }

        // --- edges ---
        for (nielsen_node const* n : m_nodes) {
            for (nielsen_edge const* e : n->outgoing()) {
                out << "\t" << n->id() << " -> " << e->tgt()->id() << " [label=<";

                // edge label: substitutions joined by <br/>
                bool first = true;
                for (auto const& s : e->subst()) {
                    if (!first) out << "<br/>";
                    first = false;
                    out << dot_html_escape(snode_label(s.m_var, m))
                        << " &#8594; "          // →
                        << dot_html_escape(snode_label(s.m_replacement, m));
                }
                out << ">";

                // colour
                nielsen_edge* ep = const_cast<nielsen_edge*>(e);
                if (sat_edges.contains(ep))
                    out << ", color=green";
                else if (e->tgt()->eval_idx() != m_run_idx)
                    out << ", color=blue";
                else if (e->tgt()->is_currently_conflict())
                    out << ", color=red";

                out << "];\n";
            }

            // backedge as dotted arrow
            if (n->backedge())
                out << "\t" << n->id() << " -> " << n->backedge()->id()
                    << " [style=dotted];\n";
        }

        out << "}\n";
        return out;
    }

    // -----------------------------------------------------------------------
    // nielsen_node: simplify_and_init
    // -----------------------------------------------------------------------

    bool nielsen_node::handle_empty_side(euf::sgraph& sg, euf::snode* non_empty_side,
                                         dep_tracker const& dep, bool& changed) {
        euf::snode_vector tokens;
        non_empty_side->collect_tokens(tokens);
        bool all_vars_or_opaque = true;
        bool has_char = false;
        for (euf::snode* t : tokens) {
            if (t->is_char()) has_char = true;
            else if (!t->is_var() && t->kind() != euf::snode_kind::s_other) {
                all_vars_or_opaque = false; break;
            }
        }
        if (has_char || !all_vars_or_opaque) {
            m_is_general_conflict = true;
            m_reason = backtrack_reason::symbol_clash;
            return true;
        }
        for (euf::snode* t : tokens) {
            if (t->is_var()) {
                nielsen_subst s(t, sg.mk_empty(), dep);
                apply_subst(sg, s);
                changed = true;
            }
        }
        return false;
    }

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
                    if (handle_empty_side(sg, eq.m_rhs, eq.m_dep, changed))
                        return simplify_result::conflict;
                    continue;
                }
                if (eq.m_rhs->is_empty() && !eq.m_lhs->is_empty()) {
                    if (handle_empty_side(sg, eq.m_lhs, eq.m_dep, changed))
                        return simplify_result::conflict;
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

        // consume leading concrete characters from str_mem via Brzozowski derivatives
        for (str_mem& mem : m_str_mem) {
            if (!mem.m_str || !mem.m_regex)
                continue;
            while (mem.m_str && !mem.m_str->is_empty()) {
                euf::snode* first = mem.m_str->first();
                if (!first || !first->is_char())
                    break;
                euf::snode* deriv = sg.brzozowski_deriv(mem.m_regex, first);
                if (!deriv) break;
                if (deriv->is_fail()) {
                    m_is_general_conflict = true;
                    m_reason = backtrack_reason::regex;
                    return simplify_result::conflict;
                }
                mem.m_str = sg.drop_first(mem.m_str);
                mem.m_regex = deriv;
                changed = true;
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

        // remove satisfied str_mem constraints (ε ∈ nullable regex)
        {
            unsigned wi = 0;
            for (unsigned i = 0; i < m_str_mem.size(); ++i) {
                str_mem& mem = m_str_mem[i];
                if (mem.m_str && mem.m_str->is_empty() && mem.m_regex && mem.m_regex->is_nullable())
                    continue;  // satisfied, drop
                m_str_mem[wi++] = mem;
            }
            if (wi < m_str_mem.size()) {
                m_str_mem.shrink(wi);
                changed = true;
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

    bool nielsen_node::has_opaque_terms() const {
        auto is_opaque = [](euf::snode* n) { return n && n->kind() == euf::snode_kind::s_other; };
        for (str_eq const& eq : m_str_eq) {
            if (eq.is_trivial()) continue;
            if (is_opaque(eq.m_lhs) || is_opaque(eq.m_rhs)) return true;
            euf::snode_vector toks;
            if (eq.m_lhs) { eq.m_lhs->collect_tokens(toks); for (auto* t : toks) if (is_opaque(t)) return true; toks.reset(); }
            if (eq.m_rhs) { eq.m_rhs->collect_tokens(toks); for (auto* t : toks) if (is_opaque(t)) return true; }
        }
        for (str_mem const& mem : m_str_mem) {
            if (!mem.m_str) continue;
            if (is_opaque(mem.m_str)) return true;
            euf::snode_vector toks;
            mem.m_str->collect_tokens(toks);
            for (auto* t : toks) if (is_opaque(t)) return true;
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // nielsen_graph: search
    // -----------------------------------------------------------------------

    nielsen_graph::search_result nielsen_graph::solve() {
        if (!m_root)
            return search_result::sat;

        ++m_stats.m_num_solve_calls;
        m_sat_node = nullptr;
        m_sat_path.reset();

        // Iterative deepening: start at depth 3, increment by 1 on each failure.
        // m_max_search_depth == 0 means unlimited; otherwise stop when bound exceeds it.
        m_depth_bound = 3;
        while (true) {
            if (m_max_search_depth > 0 && m_depth_bound > m_max_search_depth)
                break;
            inc_run_idx();
            svector<nielsen_edge*> cur_path;
            search_result r = search_dfs(m_root, 0, cur_path);
            if (r == search_result::sat) {
                ++m_stats.m_num_sat;
                return r;
            }
            if (r == search_result::unsat) {
                ++m_stats.m_num_unsat;
                return r;
            }
            // depth limit hit – increment bound by 1 and retry
            if (m_max_search_depth > 0 && m_depth_bound >= m_max_search_depth)
                break;
            ++m_depth_bound;
        }
        ++m_stats.m_num_unknown;
        return search_result::unknown;
    }

    nielsen_graph::search_result nielsen_graph::search_dfs(nielsen_node* node, unsigned depth, svector<nielsen_edge*>& cur_path) {
        ++m_stats.m_num_dfs_nodes;
        if (depth > m_stats.m_max_depth)
            m_stats.m_max_depth = depth;

        // cycle/revisit detection: if already visited this run, return cached status.
        // mirrors ZIPT's NielsenNode.GraphExpansion() evalIdx check.
        if (node->eval_idx() == m_run_idx) {
            if (node->is_satisfied()) {
                m_sat_node = node;
                m_sat_path = cur_path;
                return search_result::sat;
            }
            if (node->is_currently_conflict())
                return search_result::unsat;
            return search_result::unknown;
        }
        node->set_eval_idx(m_run_idx);

        // simplify constraints (idempotent after first call)
        simplify_result sr = node->simplify_and_init(*this);

        if (sr == simplify_result::conflict) {
            ++m_stats.m_num_simplify_conflict;
            node->set_general_conflict(true);
            return search_result::unsat;
        }
        if (sr == simplify_result::satisfied || node->is_satisfied()) {
            m_sat_node = node;
            m_sat_path = cur_path;
            return search_result::sat;
        }

        // depth bound check
        if (depth >= m_depth_bound)
            return search_result::unknown;

        // generate extensions only once per node; children persist across runs
        if (!node->is_extended()) {
            bool ext = generate_extensions(node);
            if (!ext) {
                node->set_extended(true);
                // No extensions could be generated. If the node still has
                // unsatisfied constraints with opaque (s_other) terms that
                // we cannot decompose, report unknown rather than unsat
                // to avoid unsoundness.
                if (node->has_opaque_terms())
                    return search_result::unknown;
                node->set_reason(backtrack_reason::children_failed);
                return search_result::unsat;
            }
            node->set_extended(true);
            ++m_stats.m_num_extensions;
        }

        // explore children
        bool any_unknown = false;
        for (nielsen_edge* e : node->outgoing()) {
            cur_path.push_back(e);
            search_result r = search_dfs(e->tgt(), depth + 1, cur_path);
            if (r == search_result::sat)
                return search_result::sat;
            cur_path.pop_back();
            if (r == search_result::unknown)
                any_unknown = true;
        }

        // If no children exist and the node has opaque terms, report unknown
        if (node->outgoing().empty() && node->has_opaque_terms())
            return search_result::unknown;

        if (!any_unknown) {
            node->set_reason(backtrack_reason::children_failed);
            return search_result::unsat;
        }
        return search_result::unknown;
    }

    simplify_result nielsen_graph::simplify_node(nielsen_node* node) {
        return node->simplify_and_init(*this);
    }

    bool nielsen_graph::apply_det_modifier(nielsen_node* node) {
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

            // same-head variable cancellation: x·A = x·B → A = B
            if (lhead->is_var() && lhead->id() == rhead->id()) {
                euf::snode* ltail = m_sg.drop_first(eq.m_lhs);
                euf::snode* rtail = m_sg.drop_first(eq.m_rhs);
                nielsen_node* child = mk_child(node);
                // replace the equation with the tails
                for (str_eq& ceq : child->str_eqs()) {
                    if (ceq.m_lhs == eq.m_lhs && ceq.m_rhs == eq.m_rhs) {
                        ceq.m_lhs = ltail;
                        ceq.m_rhs = rtail;
                        break;
                    }
                }
                mk_edge(node, child, true);
                return true;
            }

            // variable definition: x = t where x ∉ vars(t) → subst x → t
            if (lhead->is_var() && eq.m_rhs->is_empty()) {
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
        }
        return false;
    }

    bool nielsen_graph::apply_const_nielsen(nielsen_node* node) {
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

            // char·A = y·B → branch 1: y→ε, branch 2: y→char·fresh
            if (lhead->is_char() && rhead->is_var()) {
                // branch 1: y → ε (progress)
                {
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, true);
                    nielsen_subst s(rhead, m_sg.mk_empty(), eq.m_dep);
                    e->add_subst(s);
                    child->apply_subst(m_sg, s);
                }
                // branch 2: y → char·fresh (progress)
                {
                    euf::snode* fresh = mk_fresh_var();
                    euf::snode* replacement = m_sg.mk_concat(lhead, fresh);
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, true);
                    nielsen_subst s(rhead, replacement, eq.m_dep);
                    e->add_subst(s);
                    child->apply_subst(m_sg, s);
                }
                return true;
            }

            // x·A = char·B → branch 1: x→ε, branch 2: x→char·fresh
            if (rhead->is_char() && lhead->is_var()) {
                // branch 1: x → ε (progress)
                {
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, true);
                    nielsen_subst s(lhead, m_sg.mk_empty(), eq.m_dep);
                    e->add_subst(s);
                    child->apply_subst(m_sg, s);
                }
                // branch 2: x → char·fresh (progress)
                {
                    euf::snode* fresh = mk_fresh_var();
                    euf::snode* replacement = m_sg.mk_concat(rhead, fresh);
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, true);
                    nielsen_subst s(lhead, replacement, eq.m_dep);
                    e->add_subst(s);
                    child->apply_subst(m_sg, s);
                }
                return true;
            }
        }
        return false;
    }

    bool nielsen_graph::apply_var_nielsen(nielsen_node* node) {
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

            if (!lhead->is_var() || !rhead->is_var())
                continue;
            if (lhead->id() == rhead->id())
                continue;

            // x·A = y·B where x,y are distinct variables (classic Nielsen)
            // child 1: x → ε (progress)
            {
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                nielsen_subst s(lhead, m_sg.mk_empty(), eq.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
            }
            // child 2: x → y·x' (progress)
            {
                euf::snode* fresh = mk_fresh_var();
                euf::snode* replacement = m_sg.mk_concat(rhead, fresh);
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                nielsen_subst s(lhead, replacement, eq.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
            }
            // child 3: y → x·y' (progress)
            {
                euf::snode* fresh = mk_fresh_var();
                euf::snode* replacement = m_sg.mk_concat(lhead, fresh);
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                nielsen_subst s(rhead, replacement, eq.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
            }
            return true;
        }
        return false;
    }

    bool nielsen_graph::apply_eq_split(nielsen_node* node) {
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

            if (!lhead->is_var() || !rhead->is_var())
                continue;

            // x·A = y·B where x,y are distinct variables
            // child 1: x → ε (progress)
            {
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                nielsen_subst s(lhead, m_sg.mk_empty(), eq.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
            }
            // child 2: x → y·z_fresh (non-progress, x starts with y)
            if (lhead->id() != rhead->id()) {
                euf::snode* fresh = mk_fresh_var();
                euf::snode* replacement = m_sg.mk_concat(rhead, fresh);
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, false);
                nielsen_subst s(lhead, replacement, eq.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
            }
            // child 3: y → x·z_fresh (non-progress, y starts with x)
            if (lhead->id() != rhead->id()) {
                euf::snode* fresh = mk_fresh_var();
                euf::snode* replacement = m_sg.mk_concat(lhead, fresh);
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, false);
                nielsen_subst s(rhead, replacement, eq.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
            }
            return true;
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // nielsen_graph: mk_fresh_var
    // -----------------------------------------------------------------------

    euf::snode* nielsen_graph::mk_fresh_var() {
        ++m_stats.m_num_fresh_vars;
        std::string name = "v!" + std::to_string(m_fresh_cnt++);
        return m_sg.mk_var(symbol(name.c_str()));
    }

    // -----------------------------------------------------------------------
    // nielsen_graph: apply_regex_char_split
    // -----------------------------------------------------------------------

    void nielsen_graph::collect_first_chars(euf::snode* re, euf::snode_vector& chars) {
        if (!re)
            return;

        // to_re(s): the first character of the string s
        if (re->is_to_re()) {
            euf::snode* body = re->arg(0);
            if (body && !body->is_empty()) {
                euf::snode* first = body->first();
                if (first && first->is_char()) {
                    bool dup = false;
                    for (euf::snode* c : chars)
                        if (c == first) { dup = true; break; }
                    if (!dup)
                        chars.push_back(first);
                }
                // Handle string literals (classified as s_other in sgraph):
                // extract the first character from the zstring and create a char snode.
                else if (first && first->get_expr()) {
                    seq_util& seq = m_sg.get_seq_util();
                    zstring s;
                    if (seq.str.is_string(first->get_expr(), s) && s.length() > 0) {
                        euf::snode* ch = m_sg.mk_char(s[0]);
                        bool dup = false;
                        for (euf::snode* c : chars)
                            if (c == ch) { dup = true; break; }
                        if (!dup)
                            chars.push_back(ch);
                    }
                }
            }
            return;
        }

        // full character set (.): use 'a' as representative
        if (re->is_full_char()) {
            euf::snode* ch = m_sg.mk_char('a');
            bool dup = false;
            for (euf::snode* c : chars)
                if (c == ch) { dup = true; break; }
            if (!dup)
                chars.push_back(ch);
            return;
        }

        // re.range(lo, hi): use lo as representative
        if (re->get_expr()) {
            seq_util& seq = m_sg.get_seq_util();
            expr* lo = nullptr, *hi = nullptr;
            if (seq.re.is_range(re->get_expr(), lo, hi) && lo) {
                unsigned ch_val = 'a';
                if (seq.is_const_char(lo, ch_val)) {
                    euf::snode* ch = m_sg.mk_char(ch_val);
                    bool dup = false;
                    for (euf::snode* c : chars)
                        if (c == ch) { dup = true; break; }
                    if (!dup)
                        chars.push_back(ch);
                }
                return;
            }
        }

        // fail, full_seq: no concrete first chars to extract
        if (re->is_fail() || re->is_full_seq())
            return;

        // recurse into children (handles union, concat, star, loop, etc.)
        for (unsigned i = 0; i < re->num_args(); ++i)
            collect_first_chars(re->arg(i), chars);
    }

    bool nielsen_graph::apply_regex_char_split(nielsen_node* node) {
        for (str_mem const& mem : node->str_mems()) {
            if (!mem.m_str || !mem.m_regex)
                continue;

            // find the first token of the string side
            euf::snode* first = mem.m_str->first();
            if (!first || !first->is_var())
                continue;

            // collect concrete characters from the regex
            euf::snode_vector chars;
            collect_first_chars(mem.m_regex, chars);

            // If no concrete characters found, fall through to apply_regex_var_split
            if (chars.empty())
                continue;

            bool created = false;

            // for each character c with non-fail derivative:
            //   child: x → c · fresh_var
            for (euf::snode* ch : chars) {
                euf::snode* deriv = m_sg.brzozowski_deriv(mem.m_regex, ch);
                if (!deriv || deriv->is_fail())
                    continue;

                euf::snode* fresh = mk_fresh_var();
                euf::snode* replacement = m_sg.mk_concat(ch, fresh);
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                nielsen_subst s(first, replacement, mem.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
                created = true;
            }

            // x → ε branch (variable is empty)
            {
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                nielsen_subst s(first, m_sg.mk_empty(), mem.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
                created = true;
            }

            if (created)
                return true;
        }
        return false;
    }

    bool nielsen_graph::generate_extensions(nielsen_node *node) {
        // Modifier priority chain mirrors ZIPT's ModifierBase.TypeOrder.
        // The first modifier that produces edges is used and returned immediately.

        // Priority 1: deterministic modifiers (single child, always progress)
        if (apply_det_modifier(node))
            return ++m_stats.m_mod_det, true;

        // Priority 2: PowerEpsilon - power → ε via base=ε or n=0
        if (apply_power_epsilon(node))
            return ++m_stats.m_mod_power_epsilon, true;

        // Priority 3: NumCmp - length comparison branching for power tokens
        if (apply_num_cmp(node))
            return ++m_stats.m_mod_num_cmp, true;

        // Priority 4: ConstNumUnwinding - power vs constant: n=0 or peel
        if (apply_const_num_unwinding(node))
            return ++m_stats.m_mod_const_num_unwinding, true;

        // Priority 5: EqSplit - var vs var (branching, 3 children)
        if (apply_eq_split(node))
            return ++m_stats.m_mod_eq_split, true;

        // Priority 6: StarIntr - stabilizer introduction for regex cycles
        if (apply_star_intr(node))
            return ++m_stats.m_mod_star_intr, true;

        // Priority 7: GPowerIntr - generalized power introduction
        if (apply_gpower_intr(node))
            return ++m_stats.m_mod_gpower_intr, true;

        // Priority 8: ConstNielsen - char vs var (2 children)
        if (apply_const_nielsen(node))
            return ++m_stats.m_mod_const_nielsen, true;

        // Priority 9: RegexCharSplit - split str_mem by first-position chars
        if (apply_regex_char_split(node))
            return ++m_stats.m_mod_regex_char_split, true;

        // Priority 10: RegexVarSplit - split str_mem by minterms
        if (apply_regex_var_split(node))
            return ++m_stats.m_mod_regex_var_split, true;

        // Priority 11: PowerSplit - power unwinding with bounded prefix
        if (apply_power_split(node))
            return ++m_stats.m_mod_power_split, true;

        // Priority 12: VarNielsen - var vs var, all progress (classic Nielsen)
        if (apply_var_nielsen(node))
            return ++m_stats.m_mod_var_nielsen, true;

        // Priority 13: VarNumUnwinding - variable power unwinding
        if (apply_var_num_unwinding(node))
            return ++m_stats.m_mod_var_num_unwinding, true;

        return false;
    }

    // -----------------------------------------------------------------------
    // Helper: find a power token in any str_eq
    // -----------------------------------------------------------------------

    euf::snode* nielsen_graph::find_power_token(nielsen_node* node) const {
        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial()) continue;
            if (!eq.m_lhs || !eq.m_rhs) continue;
            euf::snode_vector toks;
            eq.m_lhs->collect_tokens(toks);
            for (euf::snode* t : toks)
                if (t->is_power()) return t;
            toks.reset();
            eq.m_rhs->collect_tokens(toks);
            for (euf::snode* t : toks)
                if (t->is_power()) return t;
        }
        return nullptr;
    }

    // -----------------------------------------------------------------------
    // Helper: find a power token facing a constant (char) head
    // Returns true if found, sets power, other_head, eq_out.
    // -----------------------------------------------------------------------

    bool nielsen_graph::find_power_vs_const(nielsen_node* node,
                                            euf::snode*& power,
                                            euf::snode*& other_head,
                                            str_eq const*& eq_out) const {
        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial()) continue;
            if (!eq.m_lhs || !eq.m_rhs) continue;
            euf::snode* lhead = eq.m_lhs->first();
            euf::snode* rhead = eq.m_rhs->first();
            if (lhead && lhead->is_power() && rhead && rhead->is_char()) {
                power = lhead; other_head = rhead; eq_out = &eq; return true;
            }
            if (rhead && rhead->is_power() && lhead && lhead->is_char()) {
                power = rhead; other_head = lhead; eq_out = &eq; return true;
            }
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Helper: find a power token facing a variable head
    // -----------------------------------------------------------------------

    bool nielsen_graph::find_power_vs_var(nielsen_node* node,
                                          euf::snode*& power,
                                          euf::snode*& var_head,
                                          str_eq const*& eq_out) const {
        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial()) continue;
            if (!eq.m_lhs || !eq.m_rhs) continue;
            euf::snode* lhead = eq.m_lhs->first();
            euf::snode* rhead = eq.m_rhs->first();
            if (lhead && lhead->is_power() && rhead && rhead->is_var()) {
                power = lhead; var_head = rhead; eq_out = &eq; return true;
            }
            if (rhead && rhead->is_power() && lhead && lhead->is_var()) {
                power = rhead; var_head = lhead; eq_out = &eq; return true;
            }
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_power_epsilon
    // For a power token u^n in an equation, branch:
    //   (1) base u → ε (base is empty, so u^n = ε)
    //   (2) u^n → ε (the power is zero, replace power with empty)
    // mirrors ZIPT's PowerEpsilonModifier
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_power_epsilon(nielsen_node* node) {
        euf::snode* power = find_power_token(node);
        if (!power)
            return false;

        SASSERT(power->is_power() && power->num_args() >= 1);
        euf::snode* base = power->arg(0);
        dep_tracker dep;
        for (str_eq const& eq : node->str_eqs())
            if (!eq.is_trivial()) { dep = eq.m_dep; break; }

        // Branch 1: base → ε (if base is a variable, substitute it to empty)
        // This makes u^n = ε^n = ε for any n.
        if (base->is_var()) {
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, true);
            nielsen_subst s(base, m_sg.mk_empty(), dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
        }

        // Branch 2: replace the power token itself with ε (n = 0 semantics)
        {
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, true);
            nielsen_subst s(power, m_sg.mk_empty(), dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
        }

        return true;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_num_cmp
    // For equations involving two power tokens u^m and u^n with the same base,
    // branch on the numeric relationship: m < n vs n <= m.
    // Approximated as: (1) replace u^m with ε, (2) replace u^n with ε.
    // mirrors ZIPT's NumCmpModifier
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_num_cmp(nielsen_node* node) {
        // Look for two power tokens with the same base on opposite sides
        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial()) continue;
            if (!eq.m_lhs || !eq.m_rhs) continue;
            euf::snode* lhead = eq.m_lhs->first();
            euf::snode* rhead = eq.m_rhs->first();
            if (!lhead || !rhead) continue;
            if (!lhead->is_power() || !rhead->is_power()) continue;
            if (lhead->num_args() < 1 || rhead->num_args() < 1) continue;
            // same base: compare the two powers
            if (lhead->arg(0)->id() != rhead->arg(0)->id()) continue;

            // Branch 1: m < n → peel from lhs power (replace lhead with ε)
            {
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                nielsen_subst s(lhead, m_sg.mk_empty(), eq.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
            }
            // Branch 2: n <= m → peel from rhs power (replace rhead with ε)
            {
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                nielsen_subst s(rhead, m_sg.mk_empty(), eq.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
            }
            return true;
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_const_num_unwinding
    // For a power token u^n facing a constant (char) head,
    // branch: (1) n = 0 → u^n = ε, (2) n >= 1 → peel one u from power.
    // mirrors ZIPT's ConstNumUnwindingModifier
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_const_num_unwinding(nielsen_node* node) {
        euf::snode* power = nullptr;
        euf::snode* other_head = nullptr;
        str_eq const* eq = nullptr;
        if (!find_power_vs_const(node, power, other_head, eq))
            return false;

        SASSERT(power->is_power() && power->num_args() >= 1);
        euf::snode* base = power->arg(0);

        // Branch 1: n = 0 → replace power with ε (progress)
        {
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, true);
            nielsen_subst s(power, m_sg.mk_empty(), eq->m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
        }

        // Branch 2: n >= 1 → peel one u: replace u^n with u · u^n'
        // Approximated by prepending the base and keeping a fresh power variable
        {
            euf::snode* fresh_power = mk_fresh_var();
            euf::snode* replacement = m_sg.mk_concat(base, fresh_power);
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, false);
            nielsen_subst s(power, replacement, eq->m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
        }

        return true;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_star_intr
    // Star introduction: for a str_mem x·s ∈ R where a cycle is detected
    // (backedge exists), introduce a stabilizer constraint x ∈ base*.
    // Creates a child that adds x ∈ base* membership and constrains
    // the remainder not to start with base.
    // mirrors ZIPT's StarIntrModifier
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_star_intr(nielsen_node* node) {
        // Only fire if a backedge was set (cycle detected)
        if (!node->backedge())
            return false;

        // Look for a str_mem with a variable-headed string
        for (unsigned mi = 0; mi < node->str_mems().size(); ++mi) {
            str_mem const& mem = node->str_mems()[mi];
            if (!mem.m_str || !mem.m_regex) continue;
            euf::snode* first = mem.m_str->first();
            if (!first || !first->is_var()) continue;

            // Introduce a fresh variable z constrained by z ∈ R*,
            // replacing x → z·fresh_post. This breaks the cycle because
            // z is a new variable that won't trigger star_intr again.
            euf::snode* x = first;
            euf::snode* z = mk_fresh_var();
            euf::snode* fresh_post = mk_fresh_var();
            euf::snode* str_tail = m_sg.drop_first(mem.m_str);

            // Build z ∈ R* membership: the star of the current regex
            seq_util& seq = m_sg.get_seq_util();
            expr* re_expr = mem.m_regex->get_expr();
            if (!re_expr)
                continue;
            expr_ref star_re(seq.re.mk_star(re_expr), seq.get_manager());
            euf::snode* star_sn = m_sg.mk(star_re);
            if (!star_sn)
                continue;

            nielsen_node* child = mk_child(node);

            // Add membership: z ∈ R* (stabilizer constraint)
            child->add_str_mem(str_mem(z, star_sn, mem.m_history, next_mem_id(), mem.m_dep));

            // Add remaining membership: fresh_post · tail ∈ R
            euf::snode* post_tail = str_tail->is_empty() ? fresh_post : m_sg.mk_concat(fresh_post, str_tail);
            child->add_str_mem(str_mem(post_tail, mem.m_regex, mem.m_history, next_mem_id(), mem.m_dep));

            // Substitute x → z · fresh_post
            nielsen_edge* e = mk_edge(node, child, false);
            euf::snode* replacement = m_sg.mk_concat(z, fresh_post);
            nielsen_subst s(x, replacement, mem.m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);

            // Do not re-set backedge — z is fresh, so star_intr won't fire again
            return true;
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_gpower_intr
    // Generalized power introduction: for a variable x matched against a
    // ground repeated pattern, introduce x = base^n · prefix with fresh n.
    // Approximated: for each non-trivial equation with a variable head vs
    // a ground concatenation, introduce power decomposition.
    // mirrors ZIPT's GPowerIntrModifier
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_gpower_intr(nielsen_node* node) {
        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial()) continue;
            if (!eq.m_lhs || !eq.m_rhs) continue;

            euf::snode* var_side = nullptr;
            euf::snode* ground_side = nullptr;

            // One side must be a single variable, other side must be ground
            euf::snode* lhead = eq.m_lhs->first();
            euf::snode* rhead = eq.m_rhs->first();

            if (lhead && lhead->is_var() && eq.m_lhs->length() == 1 && eq.m_rhs->is_ground()) {
                var_side = lhead;
                ground_side = eq.m_rhs;
            }
            else if (rhead && rhead->is_var() && eq.m_rhs->length() == 1 && eq.m_lhs->is_ground()) {
                var_side = rhead;
                ground_side = eq.m_lhs;
            }
            else continue;

            if (!ground_side || ground_side->is_empty()) continue;
            if (ground_side->length() < 2) continue; // need a repeated pattern

            // Extract the first token as the "base" for power introduction
            euf::snode* base_char = ground_side->first();
            if (!base_char || !base_char->is_char()) continue;

            // Check if the ground side has a repeated leading character
            euf::snode_vector toks;
            ground_side->collect_tokens(toks);
            unsigned repeat_len = 0;
            for (unsigned i = 0; i < toks.size(); ++i) {
                if (toks[i]->id() == base_char->id())
                    ++repeat_len;
                else break;
            }
            if (repeat_len < 2) continue; // need at least 2 repetitions

            // Introduce: x = base^n · fresh_suffix
            // Branch with side constraint n >= 0
            euf::snode* fresh_suffix = mk_fresh_var();
            euf::snode* fresh_power = mk_fresh_var(); // represents base^n
            euf::snode* replacement = m_sg.mk_concat(fresh_power, fresh_suffix);

            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, true);
            nielsen_subst s(var_side, replacement, eq.m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);

            return true;
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_regex_var_split
    // For str_mem x·s ∈ R where x is a variable, split using minterms:
    //   (1) x → ε (empty)
    //   (2) x → c · x' for each minterm character class c
    // More general than regex_char_split; uses minterm partitioning rather
    // than just extracting concrete characters.
    // mirrors ZIPT's RegexVarSplitModifier
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_regex_var_split(nielsen_node* node) {
        for (str_mem const& mem : node->str_mems()) {
            if (!mem.m_str || !mem.m_regex) continue;
            euf::snode* first = mem.m_str->first();
            if (!first || !first->is_var()) continue;

            // Compute minterms from the regex
            euf::snode_vector minterms;
            m_sg.compute_minterms(mem.m_regex, minterms);
            if (minterms.empty()) continue;

            bool created = false;

            // Branch 1: x → ε (progress)
            {
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                nielsen_subst s(first, m_sg.mk_empty(), mem.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
                created = true;
            }

            // Branch 2+: for each minterm m_i, x → fresh_char · x'
            // where fresh_char is constrained by the minterm
            for (euf::snode* mt : minterms) {
                if (mt->is_fail()) continue;

                // Try Brzozowski derivative with respect to this minterm
                // If the derivative is fail (empty language), skip this minterm
                euf::snode* deriv = m_sg.brzozowski_deriv(mem.m_regex, mt);
                if (deriv && deriv->is_fail()) continue;

                euf::snode* fresh_var = mk_fresh_var();
                euf::snode* fresh_char = mk_fresh_var();
                euf::snode* replacement = m_sg.mk_concat(fresh_char, fresh_var);
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                nielsen_subst s(first, replacement, mem.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
                created = true;
            }

            if (created)
                return true;
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_power_split
    // For a variable x facing a power token u^n, branch:
    //   (1) x = u^m · prefix(u) with m < n (bounded power prefix)
    //   (2) x = u^n · x (the variable extends past the full power)
    // Approximated since we lack integer constraint infrastructure.
    // mirrors ZIPT's PowerSplitModifier
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_power_split(nielsen_node* node) {
        euf::snode* power = nullptr;
        euf::snode* var_head = nullptr;
        str_eq const* eq = nullptr;
        if (!find_power_vs_var(node, power, var_head, eq))
            return false;

        SASSERT(power->is_power() && power->num_args() >= 1);
        euf::snode* base = power->arg(0);

        // Branch 1: x = base^m · prefix where m < n
        // Approximated: x = fresh_power_var · fresh_suffix
        {
            euf::snode* fresh_power = mk_fresh_var();
            euf::snode* fresh_suffix = mk_fresh_var();
            euf::snode* replacement = m_sg.mk_concat(fresh_power, fresh_suffix);
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, true);
            nielsen_subst s(var_head, replacement, eq->m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
        }

        // Branch 2: x = u^n · x (variable extends past full power, non-progress)
        {
            euf::snode* replacement = m_sg.mk_concat(base, var_head);
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, false);
            nielsen_subst s(var_head, replacement, eq->m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
        }

        return true;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_var_num_unwinding
    // For a power token u^n facing a variable, branch:
    //   (1) n = 0 → u^n = ε (replace power with empty)
    //   (2) n >= 1 → peel one u from the power
    // mirrors ZIPT's VarNumUnwindingModifier
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_var_num_unwinding(nielsen_node* node) {
        euf::snode* power = nullptr;
        euf::snode* var_head = nullptr;
        str_eq const* eq = nullptr;
        if (!find_power_vs_var(node, power, var_head, eq))
            return false;

        SASSERT(power->is_power() && power->num_args() >= 1);
        euf::snode* base = power->arg(0);

        // Branch 1: n = 0 → replace u^n with ε (progress)
        {
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, true);
            nielsen_subst s(power, m_sg.mk_empty(), eq->m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
        }

        // Branch 2: n >= 1 → peel one u: u^n → u · u^(n-1)
        // Approximated: replace u^n with base · fresh_var
        {
            euf::snode* fresh = mk_fresh_var();
            euf::snode* replacement = m_sg.mk_concat(base, fresh);
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, false);
            nielsen_subst s(power, replacement, eq->m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
        }

        return true;
    }

    void nielsen_graph::collect_conflict_deps(dep_tracker& deps) const {
        for (nielsen_node const* n : m_nodes) {
            if (n->eval_idx() != m_run_idx)
                continue;
            if (!n->is_currently_conflict())
                continue;
            for (str_eq const& eq : n->str_eqs())
                deps.merge(eq.m_dep);
            for (str_mem const& mem : n->str_mems())
                deps.merge(mem.m_dep);
        }
    }

    void nielsen_graph::explain_conflict(unsigned_vector& eq_indices, unsigned_vector& mem_indices) const {
        SASSERT(m_root);
        dep_tracker deps;
        collect_conflict_deps(deps);
        unsigned_vector bits;
        deps.get_set_bits(bits);
        for (unsigned b : bits) {
            if (b < m_num_input_eqs)
                eq_indices.push_back(b);
            else
                mem_indices.push_back(b - m_num_input_eqs);
        }
    }

    // -----------------------------------------------------------------------
    // nielsen_graph: length constraint generation
    // -----------------------------------------------------------------------

    expr_ref nielsen_graph::compute_length_expr(euf::snode* n) {
        ast_manager& m = m_sg.get_manager();
        seq_util& seq = m_sg.get_seq_util();
        arith_util arith(m);

        if (n->is_empty())
            return expr_ref(arith.mk_int(0), m);

        if (n->is_char() || n->is_unit())
            return expr_ref(arith.mk_int(1), m);

        if (n->is_concat()) {
            expr_ref left = compute_length_expr(n->arg(0));
            expr_ref right = compute_length_expr(n->arg(1));
            return expr_ref(arith.mk_add(left, right), m);
        }

        // for variables and other terms, use symbolic (str.len expr)
        return expr_ref(seq.str.mk_length(n->get_expr()), m);
    }

    void nielsen_graph::generate_length_constraints(vector<length_constraint>& constraints) {
        if (!m_root)
            return;

        ast_manager& m = m_sg.get_manager();
        uint_set seen_vars;

        seq_util& seq = m_sg.get_seq_util();
        arith_util arith(m);

        for (str_eq const& eq : m_root->str_eqs()) {
            if (eq.is_trivial())
                continue;

            expr_ref len_lhs = compute_length_expr(eq.m_lhs);
            expr_ref len_rhs = compute_length_expr(eq.m_rhs);
            expr_ref len_eq(m.mk_eq(len_lhs, len_rhs), m);
            constraints.push_back(length_constraint(len_eq, eq.m_dep, length_kind::eq, m));

            // collect variables for non-negativity constraints
            euf::snode_vector tokens;
            eq.m_lhs->collect_tokens(tokens);
            eq.m_rhs->collect_tokens(tokens);
            for (euf::snode* tok : tokens) {
                if (tok->is_var() && !seen_vars.contains(tok->id())) {
                    seen_vars.insert(tok->id());
                    expr_ref len_var(seq.str.mk_length(tok->get_expr()), m);
                    expr_ref ge_zero(arith.mk_ge(len_var, arith.mk_int(0)), m);
                    constraints.push_back(length_constraint(ge_zero, eq.m_dep, length_kind::nonneg, m));
                }
            }
        }

        // Parikh interval reasoning for regex memberships:
        // for each str_mem constraint str in regex, compute length bounds
        // from the regex structure and generate arithmetic constraints.
        for (str_mem const& mem : m_root->str_mems()) {
            expr* re_expr = mem.m_regex->get_expr();
            if (!re_expr || !seq.is_re(re_expr))
                continue;

            unsigned min_len = 0, max_len = UINT_MAX;
            compute_regex_length_interval(mem.m_regex, min_len, max_len);

            expr_ref len_str = compute_length_expr(mem.m_str);

            // generate len(str) >= min_len when min_len > 0
            if (min_len > 0) {
                expr_ref bound(arith.mk_ge(len_str, arith.mk_int(min_len)), m);
                constraints.push_back(length_constraint(bound, mem.m_dep, length_kind::bound, m));
            }

            // generate len(str) <= max_len when bounded
            if (max_len < UINT_MAX) {
                expr_ref bound(arith.mk_le(len_str, arith.mk_int(max_len)), m);
                constraints.push_back(length_constraint(bound, mem.m_dep, length_kind::bound, m));
            }

            // generate len(x) >= 0 for variables in the string side
            euf::snode_vector tokens;
            mem.m_str->collect_tokens(tokens);
            for (euf::snode* tok : tokens) {
                if (tok->is_var() && !seen_vars.contains(tok->id())) {
                    seen_vars.insert(tok->id());
                    expr_ref len_var(seq.str.mk_length(tok->get_expr()), m);
                    expr_ref ge_zero(arith.mk_ge(len_var, arith.mk_int(0)), m);
                    constraints.push_back(length_constraint(ge_zero, mem.m_dep, length_kind::nonneg, m));
                }
            }
        }
    }

    void nielsen_graph::compute_regex_length_interval(euf::snode* regex, unsigned& min_len, unsigned& max_len) {
        seq_util& seq = m_sg.get_seq_util();
        expr* e = regex->get_expr();
        if (!e || !seq.is_re(e)) {
            min_len = 0;
            max_len = UINT_MAX;
            return;
        }
        min_len = seq.re.min_length(e);
        max_len = seq.re.max_length(e);
        // for empty language, min_length may be UINT_MAX (vacuously true);
        // normalize to avoid generating bogus constraints
        if (min_len > max_len) {
            min_len = 0;
            max_len = 0;
        }
    }

}

