/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_nielsen.cpp

Abstract:

    Nielsen graph implementation for string constraint solving.

    Ports the constraint types and Nielsen graph structures from
    ZIPT (https://github.com/CEisenhofer/ZIPT/tree/parikh/ZIPT/Constraints)

Author:

    Clemens Eisenhofer 2026-03-02
    Nikolaj Bjorner (nbjorner) 2026-03-02

--*/

#include "smt/seq/seq_nielsen.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "math/lp/lar_solver.h"
#include "util/bit_util.h"
#include "util/hashtable.h"
#include <algorithm>
#include <cstdlib>
#include <sstream>

namespace seq {

    // -----------------------------------------------
    // dep_tracker
    // -----------------------------------------------

    dep_tracker::dep_tracker(unsigned num_bits) {
        unsigned words = (num_bits + 31) / 32;
        m_bits.resize(words, 0);
    }

    dep_tracker::dep_tracker(unsigned num_bits, unsigned set_bit) : dep_tracker(num_bits) {
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
    // char_set
    // -----------------------------------------------

    unsigned char_set::char_count() const {
        unsigned count = 0;
        for (auto const& r : m_ranges)
            count += r.length();
        return count;
    }

    bool char_set::contains(unsigned c) const {
        // binary search over sorted non-overlapping ranges
        int lo = 0, hi = static_cast<int>(m_ranges.size()) - 1;
        while (lo <= hi) {
            int mid = lo + (hi - lo) / 2;
            if (c < m_ranges[mid].m_lo)
                hi = mid - 1;
            else if (c >= m_ranges[mid].m_hi)
                lo = mid + 1;
            else
                return true;
        }
        return false;
    }

    void char_set::add(unsigned c) {
        if (m_ranges.empty()) {
            m_ranges.push_back(char_range(c));
            return;
        }
        // binary search for insertion point
        int lo = 0, hi = static_cast<int>(m_ranges.size()) - 1;
        while (lo <= hi) {
            int mid = lo + (hi - lo) / 2;
            if (c < m_ranges[mid].m_lo)
                hi = mid - 1;
            else if (c >= m_ranges[mid].m_hi)
                lo = mid + 1;
            else
                return; // already contained
        }
        // lo is the insertion point
        unsigned idx = static_cast<unsigned>(lo);
        bool merge_left  = idx > 0 && m_ranges[idx - 1].m_hi == c;
        bool merge_right = idx < m_ranges.size() && m_ranges[idx].m_lo == c + 1;
        if (merge_left && merge_right) {
            m_ranges[idx - 1].m_hi = m_ranges[idx].m_hi;
            m_ranges.erase(m_ranges.begin() + idx);
        } else if (merge_left) {
            m_ranges[idx - 1].m_hi = c + 1;
        } else if (merge_right) {
            m_ranges[idx].m_lo = c;
        } else {
            // positional insert: shift elements right and place new element
            m_ranges.push_back(char_range());
            for (unsigned k = m_ranges.size() - 1; k > idx; --k)
                m_ranges[k] = m_ranges[k - 1];
            m_ranges[idx] = char_range(c);
        }
    }

    void char_set::add(char_set const& other) {
        for (auto const& r : other.m_ranges) {
            for (unsigned c = r.m_lo; c < r.m_hi; ++c)
                add(c);
        }
    }

    char_set char_set::intersect_with(char_set const& other) const {
        char_set result;
        unsigned i = 0, j = 0;
        while (i < m_ranges.size() && j < other.m_ranges.size()) {
            unsigned lo = std::max(m_ranges[i].m_lo, other.m_ranges[j].m_lo);
            unsigned hi = std::min(m_ranges[i].m_hi, other.m_ranges[j].m_hi);
            if (lo < hi)
                result.m_ranges.push_back(char_range(lo, hi));
            if (m_ranges[i].m_hi < other.m_ranges[j].m_hi)
                ++i;
            else
                ++j;
        }
        return result;
    }

    char_set char_set::complement(unsigned max_char) const {
        char_set result;
        if (m_ranges.empty()) {
            result.m_ranges.push_back(char_range(0, max_char + 1));
            return result;
        }
        unsigned from = 0;
        for (auto const& r : m_ranges) {
            if (from < r.m_lo)
                result.m_ranges.push_back(char_range(from, r.m_lo));
            from = r.m_hi;
        }
        if (from <= max_char)
            result.m_ranges.push_back(char_range(from, max_char + 1));
        return result;
    }

    bool char_set::is_disjoint(char_set const& other) const {
        unsigned i = 0, j = 0;
        while (i < m_ranges.size() && j < other.m_ranges.size()) {
            if (m_ranges[i].m_hi <= other.m_ranges[j].m_lo)
                ++i;
            else if (other.m_ranges[j].m_hi <= m_ranges[i].m_lo)
                ++j;
            else
                return false;
        }
        return true;
    }

    std::ostream& char_set::display(std::ostream& out) const {
        if (m_ranges.empty()) {
            out << "{}";
            return out;
        }
        out << "{ ";
        bool first = true;
        for (auto const& r : m_ranges) {
            if (!first) out << ", ";
            first = false;
            if (r.is_unit()) {
                unsigned c = r.m_lo;
                if (c >= 'a' && c <= 'z')
                    out << (char)c;
                else if (c >= 'A' && c <= 'Z')
                    out << (char)c;
                else if (c >= '0' && c <= '9')
                    out << (char)c;
                else
                    out << "#[" << c << "]";
            } else {
                out << "[" << r.m_lo << "-" << (r.m_hi - 1) << "]";
            }
        }
        out << " }";
        return out;
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
        m_int_constraints.reset();
        m_char_diseqs.reset();
        m_char_ranges.reset();
        for (auto const& eq : parent.m_str_eq)
            m_str_eq.push_back(str_eq(eq.m_lhs, eq.m_rhs, eq.m_dep));
        for (auto const& mem : parent.m_str_mem)
            m_str_mem.push_back(str_mem(mem.m_str, mem.m_regex, mem.m_history, mem.m_id, mem.m_dep));
        for (auto const& ic : parent.m_int_constraints)
            m_int_constraints.push_back(ic);
        // clone character disequalities
        for (auto const& kv : parent.m_char_diseqs) {
            ptr_vector<euf::snode> diseqs;
            for (euf::snode* s : kv.m_value)
                diseqs.push_back(s);
            m_char_diseqs.insert(kv.m_key, diseqs);
        }
        // clone character ranges
        for (auto const& kv : parent.m_char_ranges) {
            m_char_ranges.insert(kv.m_key, kv.m_value.clone());
        }
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

    void nielsen_node::add_char_range(euf::snode* sym_char, char_set const& range) {
        SASSERT(sym_char && sym_char->is_unit());
        unsigned id = sym_char->id();
        if (m_char_ranges.contains(id)) {
            char_set& existing = m_char_ranges.find(id);
            char_set inter = existing.intersect_with(range);
            existing = inter;
            if (inter.is_empty()) {
                m_is_general_conflict = true;
                m_reason = backtrack_reason::character_range;
            }
        } else {
            m_char_ranges.insert(id, range.clone());
        }
    }

    void nielsen_node::add_char_diseq(euf::snode* sym_char, euf::snode* other) {
        SASSERT(sym_char && sym_char->is_unit());
        SASSERT(other && other->is_unit());
        unsigned id = sym_char->id();
        if (!m_char_diseqs.contains(id))
            m_char_diseqs.insert(id, ptr_vector<euf::snode>());
        ptr_vector<euf::snode>& existing = m_char_diseqs.find(id);
        // check for duplicates
        for (euf::snode* s : existing)
            if (s == other) return;
        existing.push_back(other);
    }

    void nielsen_node::apply_char_subst(euf::sgraph& sg, char_subst const& s) {
        if (!s.m_var) return;

        // replace occurrences of s.m_var with s.m_val in all string constraints
        for (unsigned i = 0; i < m_str_eq.size(); ++i) {
            str_eq& eq = m_str_eq[i];
            eq.m_lhs = sg.subst(eq.m_lhs, s.m_var, s.m_val);
            eq.m_rhs = sg.subst(eq.m_rhs, s.m_var, s.m_val);
            eq.sort();
        }
        for (unsigned i = 0; i < m_str_mem.size(); ++i) {
            str_mem& mem = m_str_mem[i];
            mem.m_str = sg.subst(mem.m_str, s.m_var, s.m_val);
            mem.m_regex = sg.subst(mem.m_regex, s.m_var, s.m_val);
        }

        unsigned var_id = s.m_var->id();

        if (s.m_val->is_unit()) {
            // symbolic char → symbolic char: check disequalities
            if (m_char_diseqs.contains(var_id)) {
                ptr_vector<euf::snode>& diseqs = m_char_diseqs.find(var_id);
                for (euf::snode* d : diseqs) {
                    if (d == s.m_val) {
                        m_is_general_conflict = true;
                        m_reason = backtrack_reason::character_range;
                        return;
                    }
                }
                m_char_diseqs.remove(var_id);
                m_char_ranges.remove(var_id);
            }
        } else {
            SASSERT(s.m_val->is_char());
            // symbolic char → concrete char: check range constraints
            if (m_char_ranges.contains(var_id)) {
                char_set& range = m_char_ranges.find(var_id);
                // extract the concrete char value from the s_char snode
                unsigned ch_val = 0;
                seq_util& seq = sg.get_seq_util();
                expr* unit_expr = s.m_val->get_expr();
                expr* ch_expr = nullptr;
                if (unit_expr && seq.str.is_unit(unit_expr, ch_expr))
                    seq.is_const_char(ch_expr, ch_val);
                if (!range.contains(ch_val)) {
                    m_is_general_conflict = true;
                    m_reason = backtrack_reason::character_range;
                    return;
                }
                m_char_diseqs.remove(var_id);
                m_char_ranges.remove(var_id);
            }
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

    // Helper: render an snode as a human-readable label.
    // Groups consecutive s_char tokens into quoted strings, renders s_var by name,
    // and falls back to mk_pp for other token kinds.
    static std::string snode_label(euf::snode const* n, ast_manager& m) {
        if (!n) return "null";
        seq_util seq(m);

        // collect all leaf tokens left-to-right
        euf::snode_vector tokens;
        n->collect_tokens(tokens);

        if (tokens.empty())
            return "\"\""; // empty string

        std::string result;
        std::string char_acc;   // accumulator for consecutive printable chars
        bool first = true;

        // flush accumulated chars as a quoted string
        auto flush_chars = [&]() {
            if (char_acc.empty()) return;
            if (!first) result += " + ";
            result += "\"" + char_acc + "\"";
            first = false;
            char_acc.clear();
        };

        for (euf::snode const* tok : tokens) {
            expr* e = tok->get_expr();

            // s_char: seq.unit(const_char) – extract char code and accumulate
            if (tok->is_char() && e) {
                expr* ch_expr = to_app(e)->get_arg(0);
                unsigned code = 0;
                if (seq.is_const_char(ch_expr, code)) {
                    if (code >= 32 && code < 127 && code != '"' && code != '\\') {
                        char_acc += static_cast<char>(code);
                    } else {
                        flush_chars();
                        char buf[16];
                        snprintf(buf, sizeof(buf), "'\\x%x'", code);
                        if (!first) result += " + ";
                        result += buf;
                        first = false;
                    }
                    continue;
                }
            }

            flush_chars();
            if (!first) result += " + ";
            first = false;

            if (!e) {
                result += "#" + std::to_string(tok->id());
            } else if (tok->is_var()) {
                result += to_app(e)->get_decl()->get_name().str();
            } else {
                std::ostringstream os;
                os << mk_pp(e, m);
                result += os.str();
            }
        }
        flush_chars();
        return result;
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
        // character ranges
        for (auto const& kv : m_char_ranges) {
            if (!any) { out << "Cnstr:<br/>"; any = true; }
            out << "?" << kv.m_key << " &#8712; ";
            kv.m_value.display(out);
            out << "<br/>";
        }
        // character disequalities
        for (auto const& kv : m_char_diseqs) {
            if (!any) { out << "Cnstr:<br/>"; any = true; }
            for (euf::snode* d : kv.m_value) {
                out << "?" << kv.m_key << " &#8800; ?" << d->id() << "<br/>";
            }
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

    // gives a graphviz graph representation of the Nielsen graph (for debugging)
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
                        << " &#8594; " // mapping arrow
                        << dot_html_escape(snode_label(s.m_replacement, m));
                }
                for (auto const& cs : e->char_substs()) {
                    if (!first) out << "<br/>";
                    first = false;
                    out << "?" << cs.m_var->id()
                        << " &#8594; ?" << cs.m_val->id();
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

    std::string nielsen_graph::to_dot() const {
        std::stringstream ss;
        to_dot(ss);
        return ss.str();
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

            // pass 2: detect symbol clashes, empty-propagation, and prefix cancellation
            for (str_eq& eq : m_str_eq) {
                if (!eq.m_lhs || !eq.m_rhs)
                    continue;

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

                // prefix/suffix cancellation: strip common leading and trailing tokens.
                // Same char or same variable on both sides can always be cancelled.
                // Two different concrete characters is a symbol clash.
                {
                    euf::snode_vector lhs_toks, rhs_toks;
                    eq.m_lhs->collect_tokens(lhs_toks);
                    eq.m_rhs->collect_tokens(rhs_toks);

                    // --- prefix ---
                    unsigned prefix = 0;
                    while (prefix < lhs_toks.size() && prefix < rhs_toks.size()) {
                        euf::snode* lt = lhs_toks[prefix];
                        euf::snode* rt = rhs_toks[prefix];
                        if (lt->id() == rt->id() && (lt->is_char() || lt->is_var())) {
                            ++prefix;
                        } else if (lt->is_char() && rt->is_char()) {
                            m_is_general_conflict = true;
                            m_reason = backtrack_reason::symbol_clash;
                            return simplify_result::conflict;
                        } else {
                            break;
                        }
                    }

                    // --- suffix (only among the tokens not already consumed by prefix) ---
                    unsigned lsz = lhs_toks.size(), rsz = rhs_toks.size();
                    unsigned suffix = 0;
                    while (suffix < lsz - prefix && suffix < rsz - prefix) {
                        euf::snode* lt = lhs_toks[lsz - 1 - suffix];
                        euf::snode* rt = rhs_toks[rsz - 1 - suffix];
                        if (lt->id() == rt->id() && (lt->is_char() || lt->is_var())) {
                            ++suffix;
                        } else if (lt->is_char() && rt->is_char()) {
                            m_is_general_conflict = true;
                            m_reason = backtrack_reason::symbol_clash;
                            return simplify_result::conflict;
                        } else {
                            break;
                        }
                    }

                    if (prefix > 0 || suffix > 0) {
                        eq.m_lhs = sg.drop_left(sg.drop_right(eq.m_lhs, suffix), prefix);
                        eq.m_rhs = sg.drop_left(sg.drop_right(eq.m_rhs, suffix), prefix);
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
                mem.m_history = sg.mk_concat(mem.m_history, first);
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
        unsigned wi = 0;
        for (unsigned i = 0; i < m_str_mem.size(); ++i) {
            str_mem& mem = m_str_mem[i];
            if (mem.m_str && mem.m_str->is_empty() && mem.m_regex && mem.m_regex->is_nullable())
                continue;  // satisfied, drop
            m_str_mem[wi++] = mem;
        }
        if (wi < m_str_mem.size())
            m_str_mem.shrink(wi);

        if (is_satisfied())
            return simplify_result::satisfied;

        return simplify_result::proceed;
    }

    bool nielsen_node::is_satisfied() const {
        for (str_eq const& eq : m_str_eq) {
            if (!eq.is_trivial())
                return false;
        }
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

        // Iterative deepening: increment by 1 on each failure.
        // m_max_search_depth == 0 means unlimited; otherwise stop when bound exceeds it.
        m_depth_bound = 3;
        while (true) {
            if (m_cancel_fn && m_cancel_fn()) {
#ifdef Z3DEBUG
                // Examining the Nielsen graph is probably the best way of debugging
                std::string dot = to_dot();
#endif
                break;
            }
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
        m_stats.m_max_depth = std::max(m_stats.m_max_depth, depth);

        // check for external cancellation (timeout, user interrupt)
        if (m_cancel_fn && m_cancel_fn())
            return search_result::unknown;

        // revisit detection: if already visited this run, return cached status.
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

        // integer feasibility check: collect side constraints along the path
        // and verify they are jointly satisfiable using the LP solver
        if (!cur_path.empty() && !check_int_feasibility(node, cur_path)) {
            node->set_reason(backtrack_reason::arithmetic);
            return search_result::unsat;
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

    // Returns true if variable snode `var` appears anywhere in the token list of `n`.
    static bool snode_contains_var(euf::snode const* n, euf::snode const* var) {
        if (!n || !var)
            return false;
        euf::snode_vector tokens;
        n->collect_tokens(tokens);
        for (const euf::snode* t : tokens) {
            if (t == var)
                return true;
        }
        return false;
    }

    bool nielsen_graph::apply_det_modifier(nielsen_node* node) {
        for (str_eq const& eq : node->str_eqs()) {
            SASSERT(!eq.is_trivial()); // We should have simplified it away before
            if (!eq.m_lhs || !eq.m_rhs)
                continue;

            // variable definition: x = t where x is a single var and x ∉ vars(t)
            // → deterministically substitute x → t throughout the node
            euf::snode* var = nullptr;
            euf::snode* def;
            if (eq.m_lhs->is_var() && !snode_contains_var(eq.m_rhs, eq.m_lhs)) {
                var = eq.m_lhs;
                def = eq.m_rhs;
            }
            else if (eq.m_rhs->is_var() && !snode_contains_var(eq.m_lhs, eq.m_rhs)) {
                var = eq.m_rhs;
                def = eq.m_lhs;
            }

            if (var) {
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                nielsen_subst s(var, def, eq.m_dep);
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

    // -----------------------------------------------------------------------
    // EqSplit helpers: token length classification
    // -----------------------------------------------------------------------

    bool nielsen_graph::token_has_variable_length(euf::snode* tok) const {
        // Chars and units have known constant length 1.
        if (tok->is_char() || tok->is_unit())
            return false;
        // Variables and powers have symbolic/unknown length.
        if (tok->is_var() || tok->is_power())
            return true;
        // For s_other: check if it's a string literal (known constant length).
        if (tok->get_expr()) {
            seq_util& seq = m_sg.get_seq_util();
            zstring s;
            if (seq.str.is_string(tok->get_expr(), s))
                return false;
        }
        // Everything else is treated as variable length.
        return true;
    }

    unsigned nielsen_graph::token_const_length(euf::snode* tok) const {
        if (tok->is_char() || tok->is_unit())
            return 1;
        if (tok->get_expr()) {
            seq_util& seq = m_sg.get_seq_util();
            zstring s;
            if (seq.str.is_string(tok->get_expr(), s))
                return s.length();
        }
        return 0;
    }

    // -----------------------------------------------------------------------
    // EqSplit: find_eq_split_point
    // Port of ZIPT's StrEq.SplitEq algorithm.
    //
    // Walks tokens from each side tracking two accumulators:
    //   - lhs_has_symbolic / rhs_has_symbolic : whether a variable-length token
    //     has been consumed on that side since the last reset
    //   - const_diff : net constant-length difference (LHS constants − RHS constants)
    //
    // A potential split point arises when both accumulators are "zero"
    // (no outstanding symbolic contributions on either side), meaning
    // the prefix lengths are determined up to a constant offset (const_diff).
    //
    // Among all such split points, we pick the one minimising |const_diff|
    // (the padding amount). We also require having seen at least one variable-
    // length token before accepting a split, so that the split is non-trivial.
    // -----------------------------------------------------------------------

    bool nielsen_graph::find_eq_split_point(
            euf::snode_vector const& lhs_toks,
            euf::snode_vector const& rhs_toks,
            unsigned& out_lhs_idx,
            unsigned& out_rhs_idx,
            int& out_padding) const {

        unsigned lhs_len = lhs_toks.size();
        unsigned rhs_len = rhs_toks.size();
        if (lhs_len <= 1 || rhs_len <= 1)
            return false;

        // Initialize accumulators with the first token on each side (index 0).
        bool lhs_has_symbolic = token_has_variable_length(lhs_toks[0]);
        bool rhs_has_symbolic = token_has_variable_length(rhs_toks[0]);
        int const_diff = 0;
        if (!lhs_has_symbolic)
            const_diff += (int)token_const_length(lhs_toks[0]);
        if (!rhs_has_symbolic)
            const_diff -= (int)token_const_length(rhs_toks[0]);

        bool seen_variable = lhs_has_symbolic || rhs_has_symbolic;

        // Best confirmed split point.
        bool has_best = false;
        unsigned best_lhs = 0, best_rhs = 0;
        int best_padding = 0;

        // Pending split (needs confirmation by a subsequent variable token).
        bool has_pending = false;
        unsigned pending_lhs = 0, pending_rhs = 0;
        int pending_padding = 0;

        unsigned li = 1, ri = 1;

        while (li < lhs_len || ri < rhs_len) {
            bool lhs_zero = !lhs_has_symbolic;
            bool rhs_zero = !rhs_has_symbolic;

            // Potential split point: both symbolic accumulators are zero.
            if (seen_variable && lhs_zero && rhs_zero) {
                if (!has_pending || std::abs(const_diff) < std::abs(pending_padding)) {
                    has_pending = true;
                    pending_padding = const_diff;
                    pending_lhs = li;
                    pending_rhs = ri;
                }
            }

            // Decide which side to consume from.
            // Prefer consuming from the side whose symbolic accumulator is zero
            // (i.e., that side has no outstanding variable contributions).
            bool consume_lhs;
            if (lhs_zero && !rhs_zero)
                consume_lhs = true;
            else if (!lhs_zero && rhs_zero)
                consume_lhs = false;
            else if (lhs_zero && rhs_zero)
                consume_lhs = (const_diff <= 0);  // consume from side with less accumulated constant
            else
                consume_lhs = (li <= ri);  // both non-zero: round-robin

            if (consume_lhs) {
                if (li >= lhs_len) break;
                euf::snode* tok = lhs_toks[li++];
                bool is_var = token_has_variable_length(tok);
                if (is_var) {
                    // Confirm any pending split point.
                    if (has_pending && (!has_best || std::abs(pending_padding) < std::abs(best_padding))) {
                        has_best = true;
                        best_padding = pending_padding;
                        best_lhs = pending_lhs;
                        best_rhs = pending_rhs;
                        has_pending = false;
                    }
                    seen_variable = true;
                    lhs_has_symbolic = true;
                } else {
                    const_diff += (int)token_const_length(tok);
                }
            } else {
                if (ri >= rhs_len) break;
                euf::snode* tok = rhs_toks[ri++];
                bool is_var = token_has_variable_length(tok);
                if (is_var) {
                    if (has_pending && (!has_best || std::abs(pending_padding) < std::abs(best_padding))) {
                        has_best = true;
                        best_padding = pending_padding;
                        best_lhs = pending_lhs;
                        best_rhs = pending_rhs;
                        has_pending = false;
                    }
                    seen_variable = true;
                    rhs_has_symbolic = true;
                } else {
                    const_diff -= (int)token_const_length(tok);
                }
            }
        }

        if (!has_best) return false;

        // A split at the very start or very end is degenerate — skip.
        if ((best_lhs == 0 && best_rhs == 0) ||
            (best_lhs == lhs_len && best_rhs == rhs_len))
            return false;

        out_lhs_idx = best_lhs;
        out_rhs_idx = best_rhs;
        out_padding = best_padding;
        return true;
    }

    // -----------------------------------------------------------------------
    // apply_eq_split — Port of ZIPT's EqSplitModifier.Apply
    //
    // For a regex-free equation LHS = RHS, finds a split point and decomposes
    // into two shorter equations with optional padding variable:
    //
    //   eq1: LHS[0..lhsIdx] · [pad if padding<0] = [pad if padding>0] · RHS[0..rhsIdx]
    //   eq2: LHS[lhsIdx..] · [pad if padding>0] = [pad if padding<0] · RHS[rhsIdx..]
    //
    // Creates a single progress child.
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_eq_split(nielsen_node* node) {
        ast_manager& m = m_sg.get_manager();
        seq_util& seq = m_sg.get_seq_util();
        arith_util arith(m);

        for (unsigned eq_idx = 0; eq_idx < node->str_eqs().size(); ++eq_idx) {
            str_eq const& eq = node->str_eqs()[eq_idx];
            if (eq.is_trivial())
                continue;
            if (!eq.m_lhs || !eq.m_rhs)
                continue;
            // EqSplit only applies to regex-free equations.
            if (!eq.m_lhs->is_regex_free() || !eq.m_rhs->is_regex_free())
                continue;

            euf::snode_vector lhs_toks, rhs_toks;
            eq.m_lhs->collect_tokens(lhs_toks);
            eq.m_rhs->collect_tokens(rhs_toks);
            if (lhs_toks.empty() || rhs_toks.empty())
                continue;

            unsigned split_lhs = 0, split_rhs = 0;
            int padding = 0;
            if (!find_eq_split_point(lhs_toks, rhs_toks, split_lhs, split_rhs, padding))
                continue;

            // Split the equation sides into prefix / suffix.
            euf::snode* lhs_prefix = m_sg.drop_right(eq.m_lhs, lhs_toks.size() - split_lhs);
            euf::snode* lhs_suffix = m_sg.drop_left(eq.m_lhs, split_lhs);
            euf::snode* rhs_prefix = m_sg.drop_right(eq.m_rhs, rhs_toks.size() - split_rhs);
            euf::snode* rhs_suffix = m_sg.drop_left(eq.m_rhs, split_rhs);

            // Build the two new equations, incorporating a padding variable if needed.
            euf::snode* eq1_lhs = lhs_prefix;
            euf::snode* eq1_rhs = rhs_prefix;
            euf::snode* eq2_lhs = lhs_suffix;
            euf::snode* eq2_rhs = rhs_suffix;

            euf::snode* pad = nullptr;
            if (padding != 0) {
                pad = mk_fresh_var();
                if (padding > 0) {
                    // LHS prefix is longer by |padding| constants.
                    // Prepend pad to RHS prefix, append pad to LHS suffix.
                    eq1_rhs = m_sg.mk_concat(pad, rhs_prefix);
                    eq2_lhs = m_sg.mk_concat(lhs_suffix, pad);
                } else {
                    // RHS prefix is longer by |padding| constants.
                    // Append pad to LHS prefix, prepend pad to RHS suffix.
                    eq1_lhs = m_sg.mk_concat(lhs_prefix, pad);
                    eq2_rhs = m_sg.mk_concat(pad, rhs_suffix);
                }
            }

            // Create single progress child.
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, true);

            // Remove the original equation and add the two new ones.
            auto& eqs = child->str_eqs();
            eqs[eq_idx] = eqs.back();
            eqs.pop_back();
            eqs.push_back(str_eq(eq1_lhs, eq1_rhs, eq.m_dep));
            eqs.push_back(str_eq(eq2_lhs, eq2_rhs, eq.m_dep));

            // Int constraints on the edge.
            // 1) len(pad) = |padding|  (if padding variable was created)
            if (pad && pad->get_expr()) {
                expr_ref len_pad(seq.str.mk_length(pad->get_expr()), m);
                expr_ref abs_pad(arith.mk_int(std::abs(padding)), m);
                e->add_side_int(mk_int_constraint(len_pad, abs_pad, int_constraint_kind::eq, eq.m_dep));
            }
            // 2) len(eq1_lhs) = len(eq1_rhs)
            expr_ref l1 = compute_length_expr(eq1_lhs);
            expr_ref r1 = compute_length_expr(eq1_rhs);
            e->add_side_int(mk_int_constraint(l1, r1, int_constraint_kind::eq, eq.m_dep));

            // 3) len(eq2_lhs) = len(eq2_rhs)
            expr_ref l2 = compute_length_expr(eq2_lhs);
            expr_ref r2 = compute_length_expr(eq2_rhs);
            e->add_side_int(mk_int_constraint(l2, r2, int_constraint_kind::eq, eq.m_dep));

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

    euf::snode* nielsen_graph::mk_fresh_char_var() {
        ++m_stats.m_num_fresh_vars;
        std::string name = "?c!" + std::to_string(m_fresh_cnt++);
        seq_util& seq = m_sg.get_seq_util();
        ast_manager& m = m_sg.get_manager();
        sort* char_sort = seq.mk_char_sort();
        expr_ref fresh_const(m.mk_fresh_const(name.c_str(), char_sort), m);
        expr_ref unit(seq.str.mk_unit(fresh_const), m);
        return m_sg.mk(unit);
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

        // Priority 5: EqSplit - split equations into two (single progress child)
        if (apply_eq_split(node))
            return ++m_stats.m_mod_eq_split, true;

        // Priority 6: StarIntr - stabilizer introduction for regex cycles
        if (apply_star_intr(node))
            return ++m_stats.m_mod_star_intr, true;

        // Priority 7: GPowerIntr - ground power introduction
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
        euf::snode *power = find_power_token(node);
        if (!power)
            return false;

        SASSERT(power->is_power() && power->num_args() >= 1);
        euf::snode *base = power->arg(0);
        dep_tracker dep;
        for (str_eq const &eq : node->str_eqs()) {
            if (!eq.is_trivial()) {
                dep = eq.m_dep;
                break;
            }
        }

        nielsen_node* child;
        nielsen_edge* e;

        // Branch 1: base → ε (if base is a variable, substitute it to empty)
        // This makes u^n = ε^n = ε for any n.
        if (base->is_var()) {
            child = mk_child(node);
            e = mk_edge(node, child, true);
            nielsen_subst s1(base, m_sg.mk_empty(), dep);
            e->add_subst(s1);
            child->apply_subst(m_sg, s1);
        }

        // Branch 2: replace the power token itself with ε (n = 0 semantics)
        child = mk_child(node);
        e = mk_edge(node, child, true);
        nielsen_subst s2(power, m_sg.mk_empty(), dep);
        e->add_subst(s2);
        child->apply_subst(m_sg, s2);

        return true;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_num_cmp
    // For equations involving two power tokens u^m and u^n with the same base,
    // branch on the numeric relationship: m <= n vs n < m.
    // Generates proper integer side constraints for each branch.
    // mirrors ZIPT's NumCmpModifier
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_num_cmp(nielsen_node* node) {
        ast_manager& m = m_sg.get_manager();
        arith_util arith(m);

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

            // Get exponent expressions (m and n from u^m and u^n)
            expr* exp_m = get_power_exponent(lhead);
            expr* exp_n = get_power_exponent(rhead);

            // Branch 1: m <= n → cancel u^m from both sides
            // Side constraint: m <= n
            // After cancellation: ε·A = u^(n-m)·B
            {
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                nielsen_subst s(lhead, m_sg.mk_empty(), eq.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
                if (exp_m && exp_n)
                    e->add_side_int(mk_int_constraint(exp_m, exp_n, int_constraint_kind::le, eq.m_dep));
            }
            // Branch 2: n < m → cancel u^n from both sides
            // Side constraint: n < m, i.e., n + 1 <= m, i.e., m >= n + 1
            // After cancellation: u^(m-n)·A = ε·B
            {
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                nielsen_subst s(rhead, m_sg.mk_empty(), eq.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
                if (exp_m && exp_n) {
                    expr_ref n_plus_1(arith.mk_add(exp_n, arith.mk_int(1)), m);
                    e->add_side_int(mk_int_constraint(exp_m, n_plus_1, int_constraint_kind::ge, eq.m_dep));
                }
            }
            return true;
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_const_num_unwinding
    // For a power token u^n facing a constant (char) head,
    // branch: (1) n = 0 → u^n = ε, (2) n >= 1 → peel one u from power.
    // Generates integer side constraints for each branch.
    // mirrors ZIPT's ConstNumUnwindingModifier
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_const_num_unwinding(nielsen_node* node) {
        ast_manager& m = m_sg.get_manager();
        arith_util arith(m);

        euf::snode* power = nullptr;
        euf::snode* other_head = nullptr;
        str_eq const* eq = nullptr;
        if (!find_power_vs_const(node, power, other_head, eq))
            return false;

        SASSERT(power->is_power() && power->num_args() >= 1);
        euf::snode* base = power->arg(0);
        expr* exp_n = get_power_exponent(power);
        expr* zero = arith.mk_int(0);
        expr* one = arith.mk_int(1);

        // Branch 1: n = 0 → replace power with ε (progress)
        // Side constraint: n = 0
        {
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, true);
            nielsen_subst s(power, m_sg.mk_empty(), eq->m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
            if (exp_n)
                e->add_side_int(mk_int_constraint(exp_n, zero, int_constraint_kind::eq, eq->m_dep));
        }

        // Branch 2: n >= 1 → peel one u: replace u^n with u · u^(n-1)
        // Side constraint: n >= 1
        // Use fresh power variable for u^(n-1)
        {
            euf::snode* fresh_power = mk_fresh_var();
            euf::snode* replacement = m_sg.mk_concat(base, fresh_power);
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, false);
            nielsen_subst s(power, replacement, eq->m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
            if (exp_n)
                e->add_side_int(mk_int_constraint(exp_n, one, int_constraint_kind::ge, eq->m_dep));
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
    // Generalized power introduction: for an equation where one side's head
    // is a variable v and the other side has a ground prefix followed by a
    // variable x that forms a dependency cycle back to v, introduce
    // v = base^n · suffix where base is the ground prefix.
    // Generates side constraints n >= 0 and 0 <= len(suffix) < len(base).
    // mirrors ZIPT's GPowerIntrModifier (SplitGroundPower + TryGetPowerSplitBase)
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_gpower_intr(nielsen_node* node) {
        ast_manager& m = m_sg.get_manager();
        arith_util arith(m);
        seq_util& seq = m_sg.get_seq_util();

        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial()) continue;
            if (!eq.m_lhs || !eq.m_rhs) continue;

            euf::snode* lhead = eq.m_lhs->first();
            euf::snode* rhead = eq.m_rhs->first();
            if (!lhead || !rhead) continue;

            // Try both orientations (mirrors ZIPT calling SplitGroundPower
            // with (t2, LHS) and (t1, RHS) from ExtendDir)
            // Orientation 1: RHS head is var, scan LHS for ground prefix + cycle var
            if (rhead->is_var() && !lhead->is_var()) {
                euf::snode_vector toks;
                eq.m_lhs->collect_tokens(toks);
                euf::snode_vector ground_prefix;
                euf::snode* target_var = nullptr;
                for (unsigned i = 0; i < toks.size(); ++i) {
                    if (toks[i]->is_var()) { target_var = toks[i]; break; }
                    ground_prefix.push_back(toks[i]);
                }
                if (target_var && !ground_prefix.empty() && target_var->id() == rhead->id()) {
                    if (fire_gpower_intro(node, eq, rhead, ground_prefix))
                        return true;
                }
            }
            // Orientation 2: LHS head is var, scan RHS for ground prefix + cycle var
            if (lhead->is_var() && !rhead->is_var()) {
                euf::snode_vector toks;
                eq.m_rhs->collect_tokens(toks);
                euf::snode_vector ground_prefix;
                euf::snode* target_var = nullptr;
                for (unsigned i = 0; i < toks.size(); ++i) {
                    if (toks[i]->is_var()) { target_var = toks[i]; break; }
                    ground_prefix.push_back(toks[i]);
                }
                if (target_var && !ground_prefix.empty() && target_var->id() == lhead->id()) {
                    if (fire_gpower_intro(node, eq, lhead, ground_prefix))
                        return true;
                }
            }
            // TODO: Extend to transitive cycles across multiple equations
            // (ZIPT's varDep + HasDepCycle). Currently only self-cycles are detected.
        }
        return false;
    }

    bool nielsen_graph::fire_gpower_intro(
            nielsen_node* node, str_eq const& eq,
            euf::snode* var, euf::snode_vector const& ground_prefix) {
        ast_manager& m = m_sg.get_manager();
        arith_util arith(m);
        seq_util& seq = m_sg.get_seq_util();
        unsigned base_len = ground_prefix.size();

        // Build base string expression from ground prefix tokens.
        // Each s_char snode's get_expr() is already seq.unit(ch) (a string).
        expr_ref base_str(m);
        for (unsigned i = 0; i < base_len; ++i) {
            expr* tok_expr = ground_prefix[i]->get_expr();
            if (!tok_expr) return false;
            if (i == 0)
                base_str = tok_expr;
            else
                base_str = seq.str.mk_concat(base_str, tok_expr);
        }

        // Create fresh exponent variable and power expression: base^n
        expr_ref fresh_n = mk_fresh_int_var();
        expr_ref power_expr(seq.str.mk_power(base_str, fresh_n), m);
        euf::snode* power_snode = m_sg.mk(power_expr);
        if (!power_snode) return false;

        expr* zero = arith.mk_int(0);

        // Generate one child per proper prefix of the base, mirroring ZIPT's
        // GetDecompose. For base [t0, t1, ..., t_{k-1}], the proper prefixes
        // are: ε, t0, t0·t1, ..., t0·t1·...·t_{k-2}.
        // Child i substitutes var → base^n · prefix_i with n >= 0.
        for (unsigned pfx_len = 0; pfx_len < base_len; ++pfx_len) {
            euf::snode* replacement = power_snode;
            if (pfx_len > 0) {
                euf::snode* prefix_snode = ground_prefix[0];
                for (unsigned j = 1; j < pfx_len; ++j)
                    prefix_snode = m_sg.mk_concat(prefix_snode, ground_prefix[j]);
                replacement = m_sg.mk_concat(power_snode, prefix_snode);
            }

            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, true);
            nielsen_subst s(var, replacement, eq.m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);

            // Side constraint: n >= 0
            e->add_side_int(mk_int_constraint(fresh_n, zero, int_constraint_kind::ge, eq.m_dep));
        }

        return true;
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

            // Branch 2+: for each minterm m_i, x → ?c · x'
            // where ?c is a symbolic char constrained by the minterm
            for (euf::snode* mt : minterms) {
                if (mt->is_fail()) continue;

                // Try Brzozowski derivative with respect to this minterm
                // If the derivative is fail (empty language), skip this minterm
                euf::snode* deriv = m_sg.brzozowski_deriv(mem.m_regex, mt);
                if (deriv && deriv->is_fail()) continue;

                euf::snode* fresh_var = mk_fresh_var();
                euf::snode* fresh_char = mk_fresh_char_var();
                euf::snode* replacement = m_sg.mk_concat(fresh_char, fresh_var);
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                nielsen_subst s(first, replacement, mem.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
                // TODO: derive char_set from minterm and add as range constraint
                // child->add_char_range(fresh_char, minterm_to_char_set(mt));
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
    //   (2) x = u^n · x' (the variable extends past the full power)
    // Generates integer side constraints for the fresh exponent variables.
    // mirrors ZIPT's PowerSplitModifier
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_power_split(nielsen_node* node) {
        ast_manager& m = m_sg.get_manager();
        arith_util arith(m);
        seq_util& seq = m_sg.get_seq_util();

        euf::snode* power = nullptr;
        euf::snode* var_head = nullptr;
        str_eq const* eq = nullptr;
        if (!find_power_vs_var(node, power, var_head, eq))
            return false;

        SASSERT(power->is_power() && power->num_args() >= 1);
        euf::snode* base = power->arg(0);
        expr* exp_n = get_power_exponent(power);
        expr* zero = arith.mk_int(0);

        // Branch 1: x = base^m · prefix where 0 <= m < n
        // Side constraints: m >= 0, m < n (i.e., n >= m + 1)
        {
            expr_ref fresh_m = mk_fresh_int_var();
            euf::snode* fresh_power = mk_fresh_var(); // represents base^m
            euf::snode* fresh_suffix = mk_fresh_var(); // represents prefix(base)
            euf::snode* replacement = m_sg.mk_concat(fresh_power, fresh_suffix);
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, true);
            nielsen_subst s(var_head, replacement, eq->m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
            // m >= 0
            e->add_side_int(mk_int_constraint(fresh_m, zero, int_constraint_kind::ge, eq->m_dep));
            // m < n  ⟺  n >= m + 1
            if (exp_n) {
                expr_ref m_plus_1(arith.mk_add(fresh_m, arith.mk_int(1)), m);
                e->add_side_int(mk_int_constraint(exp_n, m_plus_1, int_constraint_kind::ge, eq->m_dep));
            }
        }

        // Branch 2: x = u^n · x' (variable extends past full power, non-progress)
        // Side constraint: n >= 0
        {
            euf::snode* fresh_tail = mk_fresh_var();
            // Peel one base unit (approximation of extending past the power)
            euf::snode* replacement = m_sg.mk_concat(base, fresh_tail);
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, false);
            nielsen_subst s(var_head, replacement, eq->m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
            if (exp_n)
                e->add_side_int(mk_int_constraint(exp_n, zero, int_constraint_kind::ge, eq->m_dep));
        }

        return true;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_var_num_unwinding
    // For a power token u^n facing a variable, branch:
    //   (1) n = 0 → u^n = ε (replace power with empty)
    //   (2) n >= 1 → peel one u from the power
    // Generates integer side constraints for each branch.
    // mirrors ZIPT's VarNumUnwindingModifier
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_var_num_unwinding(nielsen_node* node) {
        ast_manager& m = m_sg.get_manager();
        arith_util arith(m);

        euf::snode* power = nullptr;
        euf::snode* var_head = nullptr;
        str_eq const* eq = nullptr;
        if (!find_power_vs_var(node, power, var_head, eq))
            return false;

        SASSERT(power->is_power() && power->num_args() >= 1);
        euf::snode* base = power->arg(0);
        expr* exp_n = get_power_exponent(power);
        expr* zero = arith.mk_int(0);
        expr* one = arith.mk_int(1);

        // Branch 1: n = 0 → replace u^n with ε (progress)
        // Side constraint: n = 0
        {
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, true);
            nielsen_subst s(power, m_sg.mk_empty(), eq->m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
            if (exp_n)
                e->add_side_int(mk_int_constraint(exp_n, zero, int_constraint_kind::eq, eq->m_dep));
        }

        // Branch 2: n >= 1 → peel one u: u^n → u · u^(n-1)
        // Side constraint: n >= 1
        {
            euf::snode* fresh = mk_fresh_var();
            euf::snode* replacement = m_sg.mk_concat(base, fresh);
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, false);
            nielsen_subst s(power, replacement, eq->m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
            if (exp_n)
                e->add_side_int(mk_int_constraint(exp_n, one, int_constraint_kind::ge, eq->m_dep));
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

    // -----------------------------------------------------------------------
    // int_constraint display
    // -----------------------------------------------------------------------

    std::ostream& int_constraint::display(std::ostream& out) const {
        if (m_lhs) out << mk_pp(m_lhs, m_lhs.get_manager());
        else out << "null";
        switch (m_kind) {
        case int_constraint_kind::eq: out << " = "; break;
        case int_constraint_kind::le: out << " <= "; break;
        case int_constraint_kind::ge: out << " >= "; break;
        }
        if (m_rhs) out << mk_pp(m_rhs, m_rhs.get_manager());
        else out << "null";
        return out;
    }

    // -----------------------------------------------------------------------
    // LP integer subsolver implementation
    // Replaces ZIPT's SubSolver with Z3's native lp::lar_solver.
    // -----------------------------------------------------------------------

    void nielsen_graph::lp_solver_reset() {
        m_lp_solver = alloc(lp::lar_solver);
        m_expr2lpvar.reset();
        m_lp_ext_cnt = 0;
    }

    lp::lpvar nielsen_graph::lp_ensure_var(expr* e) {
        if (!e) return lp::null_lpvar;

        ast_manager& m = m_sg.get_manager();
        arith_util arith(m);

        // If already mapped, return cached
        unsigned eid = e->get_id();
        lp::lpvar j;
        if (m_expr2lpvar.find(eid, j))
            return j;

        // Check if this is a numeral — shouldn't be called with a numeral directly,
        // but handle it gracefully by creating a fixed variable
        rational val;
        if (arith.is_numeral(e, val)) {
            j = m_lp_solver->add_var(m_lp_ext_cnt++, true);
            m_lp_solver->add_var_bound(j, lp::EQ, lp::mpq(val));
            m_expr2lpvar.insert(eid, j);
            return j;
        }

        // Decompose linear arithmetic: a + b → create LP term (1*a + 1*b)
        expr* e1 = nullptr;
        expr* e2 = nullptr;
        if (arith.is_add(e, e1, e2)) {
            lp::lpvar j1 = lp_ensure_var(e1);
            lp::lpvar j2 = lp_ensure_var(e2);
            if (j1 == lp::null_lpvar || j2 == lp::null_lpvar) return lp::null_lpvar;
            vector<std::pair<lp::mpq, lp::lpvar>> coeffs;
            coeffs.push_back({lp::mpq(1), j1});
            coeffs.push_back({lp::mpq(1), j2});
            j = m_lp_solver->add_term(coeffs, m_lp_ext_cnt++);
            m_expr2lpvar.insert(eid, j);
            return j;
        }

        // Decompose: a - b → create LP term (1*a + (-1)*b)
        if (arith.is_sub(e, e1, e2)) {
            lp::lpvar j1 = lp_ensure_var(e1);
            lp::lpvar j2 = lp_ensure_var(e2);
            if (j1 == lp::null_lpvar || j2 == lp::null_lpvar) return lp::null_lpvar;
            vector<std::pair<lp::mpq, lp::lpvar>> coeffs;
            coeffs.push_back({lp::mpq(1), j1});
            coeffs.push_back({lp::mpq(-1), j2});
            j = m_lp_solver->add_term(coeffs, m_lp_ext_cnt++);
            m_expr2lpvar.insert(eid, j);
            return j;
        }

        // Decompose: c * x where c is numeral → create LP term (c*x)
        if (arith.is_mul(e, e1, e2)) {
            rational coeff;
            if (arith.is_numeral(e1, coeff)) {
                lp::lpvar jx = lp_ensure_var(e2);
                if (jx == lp::null_lpvar) return lp::null_lpvar;
                vector<std::pair<lp::mpq, lp::lpvar>> coeffs;
                coeffs.push_back({lp::mpq(coeff), jx});
                j = m_lp_solver->add_term(coeffs, m_lp_ext_cnt++);
                m_expr2lpvar.insert(eid, j);
                return j;
            }
            if (arith.is_numeral(e2, coeff)) {
                lp::lpvar jx = lp_ensure_var(e1);
                if (jx == lp::null_lpvar) return lp::null_lpvar;
                vector<std::pair<lp::mpq, lp::lpvar>> coeffs;
                coeffs.push_back({lp::mpq(coeff), jx});
                j = m_lp_solver->add_term(coeffs, m_lp_ext_cnt++);
                m_expr2lpvar.insert(eid, j);
                return j;
            }
        }

        // Decompose: -x → create LP term (-1*x)
        if (arith.is_uminus(e, e1)) {
            lp::lpvar jx = lp_ensure_var(e1);
            if (jx == lp::null_lpvar) return lp::null_lpvar;
            vector<std::pair<lp::mpq, lp::lpvar>> coeffs;
            coeffs.push_back({lp::mpq(-1), jx});
            j = m_lp_solver->add_term(coeffs, m_lp_ext_cnt++);
            m_expr2lpvar.insert(eid, j);
            return j;
        }

        // Leaf expression (variable, length, or other opaque term): map to fresh LP var
        j = m_lp_solver->add_var(m_lp_ext_cnt++, true /* is_integer */);
        m_expr2lpvar.insert(eid, j);
        return j;
    }

    void nielsen_graph::lp_add_constraint(int_constraint const& ic) {
        if (!m_lp_solver || !ic.m_lhs || !ic.m_rhs)
            return;

        ast_manager& m = m_sg.get_manager();
        arith_util arith(m);

        // We handle simple patterns:
        //   expr <kind> numeral    →  add_var_bound
        //   expr <kind> expr       →  create term (lhs - rhs) and bound to 0
        rational val;
        bool is_num_rhs = arith.is_numeral(ic.m_rhs, val);

        if (is_num_rhs && (is_app(ic.m_lhs))) {
            // Simple case: single variable or len(x) vs numeral
            lp::lpvar j = lp_ensure_var(ic.m_lhs);
            if (j == lp::null_lpvar) return;
            lp::mpq rhs_val(val);
            switch (ic.m_kind) {
            case int_constraint_kind::eq:
                m_lp_solver->add_var_bound(j, lp::EQ, rhs_val);
                break;
            case int_constraint_kind::le:
                m_lp_solver->add_var_bound(j, lp::LE, rhs_val);
                break;
            case int_constraint_kind::ge:
                m_lp_solver->add_var_bound(j, lp::GE, rhs_val);
                break;
            }
            return;
        }

        // General case: create term lhs - rhs and bound it
        // For now, handle single variable on LHS vs single variable on RHS
        // (covers the common case of len(x) = len(y), n >= 0, etc.)
        bool is_num_lhs = arith.is_numeral(ic.m_lhs, val);
        if (is_num_lhs) {
            // numeral <kind> expr  →  reverse and flip kind
            lp::lpvar j = lp_ensure_var(ic.m_rhs);
            if (j == lp::null_lpvar) return;
            lp::mpq lhs_val(val);
            switch (ic.m_kind) {
            case int_constraint_kind::eq:
                m_lp_solver->add_var_bound(j, lp::EQ, lhs_val);
                break;
            case int_constraint_kind::le:
                // val <= rhs  ⇔  rhs >= val
                m_lp_solver->add_var_bound(j, lp::GE, lhs_val);
                break;
            case int_constraint_kind::ge:
                // val >= rhs  ⇔  rhs <= val
                m_lp_solver->add_var_bound(j, lp::LE, lhs_val);
                break;
            }
            return;
        }

        // Both sides are expressions: create term (lhs - rhs) with bound 0
        lp::lpvar j_lhs = lp_ensure_var(ic.m_lhs);
        lp::lpvar j_rhs = lp_ensure_var(ic.m_rhs);
        if (j_lhs == lp::null_lpvar || j_rhs == lp::null_lpvar) return;

        // Create a term: 1*lhs + (-1)*rhs
        vector<std::pair<lp::mpq, lp::lpvar>> coeffs;
        coeffs.push_back({lp::mpq(1), j_lhs});
        coeffs.push_back({lp::mpq(-1), j_rhs});
        lp::lpvar term_j = m_lp_solver->add_term(coeffs, m_lp_ext_cnt++);

        lp::mpq zero(0);
        switch (ic.m_kind) {
        case int_constraint_kind::eq:
            m_lp_solver->add_var_bound(term_j, lp::EQ, zero);
            break;
        case int_constraint_kind::le:
            m_lp_solver->add_var_bound(term_j, lp::LE, zero);
            break;
        case int_constraint_kind::ge:
            m_lp_solver->add_var_bound(term_j, lp::GE, zero);
            break;
        }
    }

    void nielsen_graph::collect_path_int_constraints(nielsen_node* node,
                                                      svector<nielsen_edge*> const& cur_path,
                                                      vector<int_constraint>& out) {
        // collect from root node
        if (m_root) {
            for (auto const& ic : m_root->int_constraints())
                out.push_back(ic);
        }

        // collect from edges along the path and their target nodes
        for (nielsen_edge* e : cur_path) {
            for (auto const& ic : e->side_int())
                out.push_back(ic);
            if (e->tgt()) {
                for (auto const& ic : e->tgt()->int_constraints())
                    out.push_back(ic);
            }
        }
    }

    bool nielsen_graph::check_int_feasibility(nielsen_node* node, svector<nielsen_edge*> const& cur_path) {
        vector<int_constraint> constraints;
        collect_path_int_constraints(node, cur_path, constraints);

        if (constraints.empty())
            return true; // no integer constraints, trivially feasible

        lp_solver_reset();

        for (auto const& ic : constraints)
            lp_add_constraint(ic);

        lp::lp_status status = m_lp_solver->find_feasible_solution();
        return status != lp::lp_status::INFEASIBLE;
    }

    int_constraint nielsen_graph::mk_int_constraint(expr* lhs, expr* rhs,
                                                     int_constraint_kind kind,
                                                     dep_tracker const& dep) {
        return int_constraint(lhs, rhs, kind, dep, m_sg.get_manager());
    }

    expr* nielsen_graph::get_power_exponent(euf::snode* power) {
        if (!power || !power->is_power()) return nullptr;
        if (power->num_args() < 2) return nullptr;
        euf::snode* exp_snode = power->arg(1);
        return exp_snode ? exp_snode->get_expr() : nullptr;
    }

    expr_ref nielsen_graph::mk_fresh_int_var() {
        ast_manager& m = m_sg.get_manager();
        arith_util arith(m);
        std::string name = "n!" + std::to_string(m_fresh_cnt++);
        return expr_ref(m.mk_fresh_const(name.c_str(), arith.mk_int()), m);
    }

}

