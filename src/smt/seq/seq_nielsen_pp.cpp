/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_nielsen_pp.cpp

Abstract:

    Display and DOT output routines for the Nielsen graph.

Author:

    Clemens Eisenhofer 2026-03-02
    Nikolaj Bjorner (nbjorner) 2026-03-02

--*/

#include "smt/seq/seq_nielsen.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "util/obj_hashtable.h"
#include <sstream>

namespace seq {

    std::ostream& nielsen_graph::display(std::ostream& out, nielsen_node const* n) const {
        out << "  node[" << n->id() << "]";
        if (n == m_root)
            out << " (root)";
        if (n->is_general_conflict())
            out << " CONFLICT";
        if (n->is_extended())
            out << " EXTENDED";
        out << "\n";

        // display string equalities
        for (auto const &eq : n->str_eqs()) {
            out << "    str_eq: ";
            if (eq.m_lhs)
                out << "lhs[id=" << eq.m_lhs->id() << ",len=" << eq.m_lhs->length() << "]";
            else
                out << "null";
            out << " = ";
            if (eq.m_rhs)
                out << "rhs[id=" << eq.m_rhs->id() << ",len=" << eq.m_rhs->length() << "]";
            else
                out << "null";
            out << "\n";
            out << mk_pp(eq.m_lhs->get_expr(), m) << " = " << mk_pp(eq.m_rhs->get_expr(), m) << "\n";
        }

        // display regex memberships
        for (auto const &mem : n->str_mems()) {
            out << "    str_mem: ";
            if (mem.m_str)
                out << "str[id=" << mem.m_str->id() << ",len=" << mem.m_str->length() << "]";
            else
                out << "null";
            out << " in ";
            if (mem.m_regex)
                out << "re[id=" << mem.m_regex->id() << "]";
            else
                out << "null";
            out << "\n";
            out << mk_pp(mem.m_str->get_expr(), m) << " in " << mk_pp(mem.m_regex->get_expr(), m) << "\n";
        }

        // display outgoing edges
        for (nielsen_edge const *e : n->outgoing()) {
            out << "    -> node[" << e->tgt()->id() << "]";
            if (e->is_progress())
                out << " (progress)";
            for (auto const &s : e->subst()) {
                out << " {";
                if (s.m_var)
                    out << "var[" << s.m_var->id() << "]";
                out << " -> ";
                if (s.m_replacement)
                    out << "repl[" << s.m_replacement->id() << ",len=" << s.m_replacement->length() << "]";
                else
                    out << "eps";
                out << "}";
            }
            out << "\n";
        }

        return out;
    }

    std::ostream& nielsen_graph::display(std::ostream& out) const {
        out << "nielsen_graph with " << m_nodes.size() << " nodes, "
            << m_edges.size() << " edges\n";

        for (const nielsen_node * n : m_nodes)
            display(out, n);        

        return out;
    }

    // -----------------------------------------------------------------------
    // nielsen_node: display_html
    // Render constraint set as an HTML fragment for DOT labels.
    // Mirrors ZIPT's NielsenNode.ToHtmlString().
    // -----------------------------------------------------------------------

    // Helper: HTML-escape a string and replace literal \n with <br/>.
    static std::string dot_html_escape(std::string const& s, const bool html_escape) {
        if (!html_escape)
            return s;
        std::string r;
        r.reserve(s.size());
        for (const char c : s) {
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
            }
            else
                result += r[i++];
        }
        return result;
    }

    std::string decode_recursive_name(expr* e, ast_manager& m, bool html_escape) {
        SASSERT(e && is_app(e));
        th_rewriter rw(m);
        const skolem sk(m, rw);
        expr* arg = e, *l, *r;
        unsigned cnt = 0;
        while (sk.is_slice(arg, arg, l, r)) {
            cnt++;
        }
        if (to_app(arg)->get_num_args() != 0)
            return "";
        std::string s = dot_html_escape(to_app(arg)->get_decl()->get_name().str(), html_escape);
        if (cnt == 0)
            return s;
        return s + "[" + std::to_string(cnt) + "]";
    }

    static std::string code_to_str(unsigned code) {
        if (code >= 32 && code < 127 && code != '"' && code != '\\') {
            return std::string(reinterpret_cast<char*>(&code), 1);
        }
        char buf[16];
        snprintf(buf, sizeof(buf), "'\\x%x'", code);
        return std::string(buf);
    }

    // Helper: render an arithmetic/integer expression in infix HTML notation.
    // Recognises +, -, *, unary minus, numerals, str.len, and named constants;
    // falls back to HTML-escaped mk_pp for anything else.
    static std::string arith_expr_html(expr* e, obj_map<expr, std::string>& names, uint64_t& next_id, ast_manager& m, bool html_escape) {
        if (!e) return "null";
        arith_util arith(m);
        seq_util seq(m);
        rational val;
        if (arith.is_numeral(e, val))
            return val.to_string();
        if (!is_app(e)) {
            std::ostringstream os;
            os << mk_bounded_pp(e, m);
            return dot_html_escape(os.str(), html_escape);
        }
        app* a = to_app(e);
        expr* x, * y;
        if (m.is_or(e)) {
            app* ap = to_app(e);
            std::string res;
            res = arith_expr_html(ap->get_arg(0), names, next_id, m, html_escape);
            for (unsigned i = 1; i < ap->get_num_args(); ++i) {
                res += " || ";
                res += arith_expr_html(ap->get_arg(i), names, next_id, m, html_escape);
            }
            return res;
        }
        if (m.is_not(e, x))
            return "!(" + arith_expr_html(x, names, next_id, m, html_escape) + ")";
        if (arith.is_lt(e, x, y)) {
            return arith_expr_html(x, names, next_id, m, html_escape) + " &lt; " + arith_expr_html(y, names, next_id, m, html_escape);
        }
        if (arith.is_gt(e, x, y)) {
            return arith_expr_html(x, names, next_id, m, html_escape) + " &gt; " + arith_expr_html(y, names, next_id, m, html_escape);
        }
        if (arith.is_le(e, x, y)) {
            return arith_expr_html(x, names, next_id, m, html_escape) + " &#8804; " + arith_expr_html(y, names, next_id, m, html_escape);
        }
        if (arith.is_ge(e, x, y)) {
            return arith_expr_html(x, names, next_id, m, html_escape) + " &#8805; " + arith_expr_html(y, names, next_id, m, html_escape);
        }
        if (m.is_eq(e, x, y)) {
            return arith_expr_html(x, names, next_id, m, html_escape) + " = " + arith_expr_html(y, names, next_id, m, html_escape);
        }
        if (arith.is_add(e)) {
            std::string r = arith_expr_html(a->get_arg(0), names, next_id, m, html_escape);
            for (unsigned i = 1; i < a->get_num_args(); ++i) {
                expr* arg = a->get_arg(i);
                // render (+ x (- y)) as "x - y" and (+ x (- n)) as "x - n"
                expr* neg_inner;
                rational neg_val;
                if (arith.is_uminus(arg, neg_inner)) {
                    r += " &#8722; "; // minus sign
                    r += arith_expr_html(neg_inner, names, next_id, m, html_escape);
                } else if (arith.is_numeral(arg, neg_val) && neg_val.is_neg()) {
                    r += " &#8722; "; // minus sign
                    r += (-neg_val).to_string();
                }
                else {
                    r += " + ";
                    r += arith_expr_html(arg, names, next_id, m, html_escape);
                }
            }
            return r;
        }
        if (arith.is_sub(e, x, y))
            return arith_expr_html(x, names, next_id, m, html_escape) + " &#8722; " + arith_expr_html(y, names, next_id, m, html_escape);
        if (arith.is_uminus(e, x))
            return "&#8722;" + arith_expr_html(x, names, next_id, m, html_escape);
        if (arith.is_mul(e)) {
            std::string r;
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                if (i > 0) r += " &#183; "; // middle dot
                r += arith_expr_html(a->get_arg(i), names, next_id, m, html_escape);
            }
            return r;
        }
        if (seq.str.is_length(e, x)) {
            std::string name = decode_recursive_name(x, m, html_escape);
            if (!name.empty()) {
                return "|" + name + "|";
            }
            if (names.contains(x)) {
                return "|" + names[x] + "|";
            }
            std::stringstream ss;
            ss << mk_bounded_pp(x, m);
            std::string s = ss.str();
            names.insert(x, s);
            return "|" + s + "|";
        }
        unsigned c;
        if (seq.is_const_char(e, c))
            return '"' + code_to_str(c) + '"';

        // named constant, fresh variable like n!0
        if (a->get_num_args() == 0)
            return dot_html_escape(a->get_decl()->get_name().str(), html_escape);
        if (names.contains(e))
            return names[e];
        std::stringstream ss;
        ss << mk_bounded_pp(e, m);
        std::string s = dot_html_escape(ss.str(), html_escape);
        names.insert(e, s);
        return s;
    }

    // Helper: render a constraint as an HTML string for DOT edge labels.
    static std::string constraint_html(constraint const& ic, obj_map<expr, std::string>& names, uint64_t& next_id, ast_manager& m) {
        if (ic.fml) return arith_expr_html(ic.fml, names, next_id, m, true);
        return "null";
    }

    static std::string regex_expr_html(expr* e, obj_map<expr, std::string>& names, uint64_t& next_id, ast_manager& m, seq_util& seq, bool html_escape) {
        if (!e)
            return "null";
        expr* a = nullptr, * b = nullptr;

        if (seq.re.is_to_re(e, a)) {
            zstring s;
            bool first = true;
            svector<expr*> args;
            args.push_back(a);
            // flatten concatenations
            std::ostringstream os;
            while (!args.empty()) {
                expr* arg = args.back();
                args.pop_back();
                if (seq.str.is_concat(arg)) {
                    args.push_back(to_app(arg)->get_arg(1));
                    args.push_back(to_app(arg)->get_arg(0));
                    continue;
                }
                if (seq.str.is_string(arg, s)) {
                    if (!first) os << " ";
                    os << "\"" + dot_html_escape(s.encode(), html_escape) + "\"";
                    first = false;
                    continue;
                }
                unsigned ch_val = 0;
                if (seq.str.is_unit(arg) && seq.is_const_char(to_app(arg)->get_arg(0), ch_val)) {
                    if (!first) os << " ";
                    os << "\"" + dot_html_escape(zstring(ch_val).encode(), html_escape) + "\"";
                    first = false;
                    continue;
                }
                if (!first) os << " ";
                os << mk_pp(arg, m);
                first = false;
            }
            return dot_html_escape(os.str(), html_escape);
        }
        unsigned c;
        if (seq.is_const_char(e, c))
            return code_to_str(c);
        if (seq.re.is_concat(e)) {
            app* ap = to_app(e);
            std::string res;
            if (ap->get_num_args() == 0) return "()";
            for (unsigned i = 0; i < ap->get_num_args(); ++i) {
                if (i > 0) res += " ";
                bool needs_parens = seq.re.is_union(ap->get_arg(i));
                if (needs_parens) res += "(";
                res += regex_expr_html(ap->get_arg(i), names, next_id, m, seq, html_escape);
                if (needs_parens) res += ")";
            }
            return res;
        }
        if (m.is_ite(e)) {
            app* ap = to_app(e);
            std::string cond = arith_expr_html(ap->get_arg(0), names, next_id, m, html_escape);
            std::string t = regex_expr_html(ap->get_arg(1), names, next_id, m, seq, html_escape);
            std::string f = regex_expr_html(ap->get_arg(2), names, next_id, m, seq, html_escape);
            return cond + " ? (" + t + ") : (" + f + ")";
        }
        if (seq.re.is_union(e)) {
            app* ap = to_app(e);
            std::string res;
            if (ap->get_num_args() == 0)
                return "&#8709;";
            res = regex_expr_html(ap->get_arg(0), names, next_id, m, seq, html_escape);
            for (unsigned i = 1; i < ap->get_num_args(); ++i) {
                res += " | ";
                res += regex_expr_html(ap->get_arg(i), names, next_id, m, seq, html_escape);
            }
            return res;
        }
        if (seq.re.is_intersection(e)) {
            app* ap = to_app(e);
            std::string res;
            for (unsigned i = 0; i < ap->get_num_args(); ++i) {
                if (i > 0) res += " &amp; ";
                bool needs_parens = seq.re.is_union(ap->get_arg(i)) || seq.re.is_concat(ap->get_arg(i));
                if (needs_parens) res += "(";
                res += regex_expr_html(ap->get_arg(i), names, next_id, m, seq, html_escape);
                if (needs_parens) res += ")";
            }
            return res;
        }
        if (seq.re.is_star(e, a)) {
            bool needs_parens = seq.re.is_union(a) || seq.re.is_concat(a) || seq.re.is_intersection(a);
            std::string res = needs_parens ? "(" : "";
            res += regex_expr_html(a, names, next_id, m, seq, html_escape);
            res += needs_parens ? ")<SUP>*</SUP>" : "<SUP>*</SUP>";
            return res;
        }
        if (seq.re.is_plus(e, a)) {
            bool needs_parens = seq.re.is_union(a) || seq.re.is_concat(a) || seq.re.is_intersection(a);
            std::string res = needs_parens ? "(" : "";
            res += regex_expr_html(a, names, next_id, m, seq, html_escape);
            res += needs_parens ? ")<SUP>+</SUP>" : "<SUP>+</SUP>";
            return res;
        }
        if (seq.re.is_opt(e, a)) {
            bool needs_parens = seq.re.is_union(a) || seq.re.is_concat(a) || seq.re.is_intersection(a);
            std::string res = needs_parens ? "(" : "";
            res += regex_expr_html(a, names, next_id, m, seq, html_escape);
            res += needs_parens ? ")?" : "?";
            return res;
        }
        if (seq.re.is_complement(e, a)) {
            bool needs_parens = seq.re.is_union(a) || seq.re.is_concat(a) || seq.re.is_intersection(a);
            std::string res = "~";
            res += needs_parens ? "(" : "";
            res += regex_expr_html(a, names, next_id, m, seq, html_escape);
            res += needs_parens ? ")" : "";
            return res;
        }
        if (seq.re.is_range(e, a, b)) {
            zstring s1, s2;
            std::string c1 = seq.str.is_string(a, s1) ? dot_html_escape(s1.encode(), html_escape) : arith_expr_html(a, names, next_id, m, html_escape);
            std::string c2 = seq.str.is_string(b, s2) ? dot_html_escape(s2.encode(), html_escape) : arith_expr_html(b, names, next_id, m, html_escape);
            return "[" + c1 + "-" + c2 + "]";
        }
        if (seq.re.is_full_char(e)) {
            return "&#931;"; // Sigma
        }
        if (seq.re.is_full_seq(e)) {
            return "&#931;<SUP>*</SUP>"; // Sigma*
        }
        if (seq.re.is_empty(e)) {
            return "&#8709;"; // empty set
        }

        std::ostringstream os;
        os << mk_pp(e, m);
        return dot_html_escape(os.str(), html_escape);
    }

    // Helper: render a snode as an HTML label for DOT output.
    // Groups consecutive s_char tokens into quoted strings, renders s_var by name,
    // shows s_power with superscripts, s_unit by its inner expression,
    // and falls back to mk_pp, HTML-escaped, for other token kinds.
    std::string snode_label_html(euf::snode const* n, obj_map<expr, std::string>& names, uint64_t& next_id, ast_manager& m, bool html_escape) {
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
            result += "\"" + dot_html_escape(char_acc, html_escape) + "\"";
            first = false;
            char_acc.clear();
        };

        for (euf::snode const* tok : tokens) {
            expr* e = tok->get_expr();

            // s_char: seq.unit(const_char) - extract char code and accumulate
            if (tok->is_char() && e) {
                expr* ch_expr = to_app(e)->get_arg(0);
                unsigned code = 0;
                if (seq.is_const_char(ch_expr, code)) {
                    char_acc += code_to_str(code);
                    flush_chars();
                    continue;
                }
            }

            flush_chars();
            if (!first) result += " + ";
            first = false;

            if (!e) {
                result += "#" + std::to_string(tok->id());
            } else if (tok->is_var()) {
                std::string name = decode_recursive_name(e, m, html_escape);
                if (!name.empty()) {
                    result += name;
                }
                else if (names.contains(e))
                    result += names[e];
                else {
                    std::stringstream ss;
                    ss << mk_bounded_pp(e, m);
                    std::string s = dot_html_escape(ss.str(), html_escape);
                    names.insert(e, s);
                    result += s;
                }
            } else if (tok->is_unit()) {
                // seq.unit with non-literal character: show the character expression
                expr* ch = to_app(e)->get_arg(0);
                if (is_app(ch) && to_app(ch)->get_num_args() == 0)
                    result += "[" + dot_html_escape(to_app(ch)->get_decl()->get_name().str(), html_escape) + "]";
                else {
                    std::ostringstream os;
                    os << mk_pp(ch, m);
                    result += "[" + dot_html_escape(os.str(), html_escape) + "]";
                }
            }
            else if (tok->is_power()) {
                // seq.power(base, n): render as base<SUP>n</SUP>
                std::string base_html = snode_label_html(tok->arg(0), m, html_escape);
                if (tok->arg(0)->length() > 1)
                    base_html = "(" + base_html + ")";
                result += base_html;
                result += "<SUP>";
                expr* exp_expr = to_app(e)->get_arg(1);
                result += arith_expr_html(exp_expr, names, next_id, m, html_escape);
                result += "</SUP>";
            }
            else if (seq.is_re(e))
                result += regex_expr_html(e, names, next_id, m, seq, html_escape);
            else {
                std::ostringstream os;
                os << mk_pp(e, m);
                result += dot_html_escape(os.str(), html_escape);
            }
        }
        flush_chars();
        return result;
    }

    std::string snode_label_html(euf::snode const* n, ast_manager& m, bool html_escape) {
        obj_map<expr, std::string> names;
        uint64_t next_id = 0;
        return snode_label_html(n, names, next_id, m, html_escape);
    }

    std::ostream& nielsen_node::to_html(std::ostream& out, ast_manager& m) const {
        obj_map<expr, std::string> names;
        uint64_t next_id = 0;
        return to_html(out, names, next_id, m);
    }

    std::ostream& nielsen_node::to_html(std::ostream& out, obj_map<expr, std::string>& names, uint64_t& next_id, ast_manager& m) const {
        bool any = false;
        bool hasEq = false;
        bool hasDisEq = false;
        bool hasMem = false;
        bool hasRange = false;

        // string equalities
        for (auto const& eq : m_str_eq) {
            if (!any) { out << "Cnstr:<br/>"; any = true; }
            if (!hasEq) { out << "Eq:<br/>"; hasEq = true; }
            out << snode_label_html(eq.m_lhs, names, next_id, m, true)
                << " = "
                << snode_label_html(eq.m_rhs, names, next_id, m, true)
                << "<br/>";
        }
        // string disequalities
        for (auto const& eq : m_str_deq) {
            if (!any) { out << "Cnstr:<br/>"; any = true; }
            if (!hasDisEq) { out << "DisEq:<br/>"; hasDisEq = true; }
            out << snode_label_html(eq.m_lhs, names, next_id, m, true)
                << " &#x2260; "
                << snode_label_html(eq.m_rhs, names, next_id, m, true)
                << "<br/>";
        }
        // regex memberships
        for (auto const& mem : m_str_mem) {
            if (!any) { out << "Cnstr:<br/>"; any = true; }
            if (!hasMem) { out << "Mem:<br/>"; hasMem = true; }
            out << snode_label_html(mem.m_str, names, next_id, m, true)
                << " &#8712; "
                << regex_expr_html(mem.m_regex->get_expr(), names, next_id, m, graph().seq(), true)
                << "<br/>";
        }
        // character ranges
        for (auto const& kv : m_char_ranges) {
            if (!any) { out << "Cnstr:<br/>"; any = true; }
            if (!hasRange) { out << "Ranges:<br/>"; hasRange = true; }
            out << "?" << kv.m_key << " &#8712; ";
            kv.m_value.first.display(out);
            out << "<br/>";
        }
        // integer constraints
        std::vector<std::string> int_constraints;
        for (auto const& ic : m_constraints) {
            int_constraints.push_back(constraint_html(ic, names, next_id, m));
            SASSERT(!int_constraints.empty());
        }
        if (!int_constraints.empty()) {
            // eliminate duplicates
            std::ranges::sort(int_constraints);
            unsigned prev = 0;
            for (unsigned i = 1; i < int_constraints.size(); i++) {
                if (int_constraints[i] != int_constraints[prev])
                    int_constraints[++prev] = int_constraints[i];
            }
            int_constraints.resize(prev + 1);
            if (!any) { out << "Cnstr:<br/>"; any = true; }
            out << "Int:<br/>";
            for (const auto& s : int_constraints) {
                out << s << "<br/>";
            }
        }

        if (!any)
            out << "&#8868;"; // top, trivially satisfied
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
        case backtrack_reason::external:         return "External";
        case backtrack_reason::children_failed:  return "Children Failed";
        default:                                 return "?";
        }
    }

    // Render the current substitution of the original (root) variables at `node`.
    // Walks the parent-edge chain from the root down to `node`, composing the
    // edge substitutions exactly the way seq_model::extract_assignments does,
    // and prints each root variable together with its current value (the image
    // of the variable after applying all substitutions on the root-to-node path).
    // Only variables whose value actually changed are shown. Purely for display:
    // the values are computed on demand and any snodes created during
    // substitution are harmless (the sgraph is monotone within a scope).
    static void render_current_subst(std::ostream& out, nielsen_node const* node,
                                     nielsen_node const* root,
                                     u_map<nielsen_edge*> const& parent_edge,
                                     euf::sgraph& sg,
                                     obj_map<expr, std::string>& names, uint64_t& next_id,
                                     ast_manager& m) {
        if (!root)
            return;

        // collect the original variables present in the root node's constraints
        euf::snode_vector vars;
        uint_set seen;
        auto add_vars = [&](euf::snode const* s) {
            if (!s)
                return;
            for (euf::snode const* t : s->collect_tokens())
                if (t->is_var() && !seen.contains(t->id())) {
                    seen.insert(t->id());
                    vars.push_back(t);
                }
        };
        for (auto const& eq : root->str_eqs()) { add_vars(eq.m_lhs); add_vars(eq.m_rhs); }
        for (auto const& deq : root->str_deqs()) { add_vars(deq.m_lhs); add_vars(deq.m_rhs); }
        for (auto const& mem : root->str_mems()) add_vars(mem.m_str);
        if (vars.empty())
            return;

        // collect edges along the root-to-node path (path[0] is node's parent edge)
        ptr_vector<nielsen_edge> path;
        uint_set visited;
        for (nielsen_node const* cur = node; cur != root && !visited.contains(cur->id()); ) {
            visited.insert(cur->id());
            nielsen_edge* pe = nullptr;
            if (!parent_edge.find(cur->id(), pe))
                break;
            path.push_back(pe);
            cur = pe->src();
        }

        bool any = false;
        for (euf::snode const* var : vars) {
            euf::snode const* val = var;
            // apply substitutions in root-to-node order (path is node-to-root)
            for (unsigned i = path.size(); i-- > 0; ) {
                for (nielsen_subst const& s : path[i]->subst()) {
                    val = sg.subst(val, s.m_var, s.m_replacement);
                }
            }
            if (val == var)
                continue; // unchanged: variable is still free at this node
            if (!any) { out << "<br/>Subst:<br/>"; any = true; }
            out << snode_label_html(var, names, next_id, m, true)
                << " &#8594; "
                << snode_label_html(val, names, next_id, m, true)
                << "<br/>";
        }
    }

    // gives a graphviz graph representation of the Nielsen graph, for debugging
    std::ostream& nielsen_graph::to_dot(std::ostream& out) const {

        // collect sat-path nodes and edges for green highlighting
        ptr_addr_hashtable<nielsen_node> sat_nodes;
        ptr_addr_hashtable<nielsen_edge> sat_edges;
        for (nielsen_edge* e : m_sat_path) {
            if (e->src()) sat_nodes.insert(e->src());
            if (e->tgt()) sat_nodes.insert(e->tgt());
            sat_edges.insert(e);
        }

        obj_map<expr, std::string> names;
        uint64_t next_id = 0;
        out << "digraph G {\n";

        // map each node to an incoming edge so the root-to-node substitution
        // path can be reconstructed (m_parent_edge is not maintained).
        u_map<nielsen_edge*> parent_edge;
        for (nielsen_node const* n : m_nodes)
            for (nielsen_edge* e : n->outgoing())
                parent_edge.insert(e->tgt()->id(), e);

        // --- nodes ---
        for (nielsen_node const* n : m_nodes) {
            out << "    " << n->id() << " [label=<"
                << n->id() << ": ";
            n->to_html(out, names, next_id, m);
            // append the current substitution of the root variables at this node
            render_current_subst(out, n, m_root, parent_edge, m_sg, names, next_id, m);
            // append conflict reason if this is a direct conflict
            if (n->is_currently_conflict())
                out << "<br/>" << reason_to_str(n->reason());
            if (n->reason() == backtrack_reason::external)
                out << "<br/>" << n->get_external_conflict_literal();
            out << ">";

            // colour
            if (sat_nodes.contains(const_cast<nielsen_node*>(n)))
                out << ", color=green";
            else if (n->is_general_conflict())
                out << ", color=darkred";
            else if (n->is_currently_conflict())
                out << ", color=red";

            out << "];\n";
        }

        // --- edges ---
        for (nielsen_node const* n : m_nodes) {
            for (nielsen_edge const* e : n->outgoing()) {
                out << "    " << n->id() << " -> " << e->tgt()->id() << " [label=<";

                // edge label: substitutions joined by <br/>
                out << "[" << e->rule_name() << "]";
                for (auto const& s : e->subst()) {
                    out << "<br/>";
                    out << snode_label_html(s.m_var, m, true)
                        << " &#8594; " // mapping arrow
                        << snode_label_html(s.m_replacement, m, true);
                }
                // side constraints: integer equalities/inequalities
                for (auto const& ic : e->side_constraints()) {
                    out << "<br/>";
                    out << "<font color=\"gray\">"
                        << constraint_html(ic, names, next_id, m)
                        << "</font>";
                }
                out << ">";

                // colour
                nielsen_edge* ep = const_cast<nielsen_edge*>(e);
                if (sat_edges.contains(ep))
                    out << ", color=green";
                else if (e->tgt()->is_currently_conflict())
                    out << ", color=red";

                out << "];\n";
            }
        }
        out << "}\n";
        return out;
    }

    std::string nielsen_graph::to_dot() const {
        std::stringstream ss;
        to_dot(ss);
        return ss.str();
    }

    std::ostream& nielsen_graph::partial_dfa_to_dot(std::ostream& out, euf::snode const* start_state, bool keep_names) const {
        out << "digraph G {\n";
        out << "  node [shape=box];\n";

        if (!start_state || !start_state->get_expr())
            return out << "}\n";

        const unsigned start_state_id = start_state->get_expr()->get_id();

        unsigned_vector todo;
        uint_set visited;
        vector<partial_dfa_edge const*> edges;

        todo.push_back(start_state_id);
        visited.insert(start_state_id);

        auto sanitize = [](std::string const& s) {
            std::string res;
            for (const char c : s) {
                if (c == '"') res += "\\\"";
                else if (c == '\n') res += "\\n";
                else res += c;
            }
            return res;
        };

        while (!todo.empty()) {
            unsigned curr = todo.back();
            todo.pop_back();

            auto it = m_partial_dfa_out.find(curr);
            if (it == m_partial_dfa_out.end())
                continue;

            for (const unsigned edge_idx : it->second) {
                if (edge_idx >= m_partial_dfa_edges.size())
                    continue;
                partial_dfa_edge const& e = m_partial_dfa_edges[edge_idx];
                edges.push_back(&e);

                if (!visited.contains(e.m_dst->get_id())) {
                    visited.insert(e.m_dst->get_id());
                    todo.push_back(e.m_dst->get_id());
                }
            }
        }

        for (const unsigned node_id : visited) {
            expr* node_expr = nullptr;
            for (auto* e : edges) {
                if (e->m_src->get_id() == node_id) {
                    node_expr = e->m_src;
                    break;
                }
                if (e->m_dst->get_id() == node_id) {
                    node_expr = e->m_dst;
                    break;
                }
            }
            if (!node_expr) {
                for (expr* pinned : m_partial_dfa_pin) {
                    if (pinned && pinned->get_id() == node_id) {
                        node_expr = pinned;
                        break;
                    }
                }
            }

            bool accepting = false;
            if (node_expr) {
                euf::snode const* sn = m_sg.mk(node_expr);
                accepting = m_sg.re_nullable(sn) == l_true;
            }

            out << "  N" << node_id << " [";
            if (accepting) {
                out << "shape=doublecircle, ";
            }
            out << "label=\"";

            if (keep_names) {
                if (node_expr) {
                    std::stringstream ss;
                    ss << mk_ismt2_pp(node_expr, m);
                    out << sanitize(ss.str());
                } else {
                    out << node_id;
                }
            } else {
                out << node_id;
            }
            out << "\"];\n";
        }

        for (auto* e : edges) {
            out << "  N" << e->m_src->get_id() << " -> N" << e->m_dst->get_id() << " [label=\"";
            //if (e->m_label) {
            //    std::stringstream ss;
            //    ss << mk_ismt2_pp(e->m_label, m);
            //    out << sanitize(ss.str());
            //} else {
            //    out << "??";
            //}
            out << "\"];\n";
        }

        out << "}\n";
        return out;
    }

    std::string nielsen_graph::partial_dfa_to_dot(euf::snode const* start_state, bool keep_names) const {
        std::stringstream ss;
        partial_dfa_to_dot(ss, start_state, keep_names);
        return ss.str();
    }

} // namespace seq
