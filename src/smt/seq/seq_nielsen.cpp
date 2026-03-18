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
#include "smt/seq/seq_parikh.h"
#include "smt/seq/seq_regex.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"
#include "util/hashtable.h"
#include "util/statistics.h"
#include <algorithm>
#include <cstdlib>
#include <sstream>

namespace seq {

    // Normalize an arithmetic expression using th_rewriter.
    // Simplifies e.g. (n - 1 + 1) to n, preventing unbounded growth
    // of power exponents during unwind/merge cycles.
    static expr_ref normalize_arith(ast_manager& m, expr* e) {
        expr_ref result(e, m);
        th_rewriter rw(m);
        rw(result);
        return result;
    }

    // Directional helpers mirroring ZIPT's fwd flag:
    // fwd=true  -> left-to-right (prefix/head)
    // fwd=false -> right-to-left (suffix/tail)
    static euf::snode* dir_token(euf::snode* s, bool fwd) {
        if (!s) return nullptr;
        return fwd ? s->first() : s->last();
    }

    static euf::snode* dir_drop(euf::sgraph& sg, euf::snode* s, unsigned count, bool fwd) {
        if (!s || count == 0) return s;
        return fwd ? sg.drop_left(s, count) : sg.drop_right(s, count);
    }

    static euf::snode* dir_concat(euf::sgraph& sg, euf::snode* a, euf::snode* b, bool fwd) {
        if (!a) return b;
        if (!b) return a;
        return fwd ? sg.mk_concat(a, b) : sg.mk_concat(b, a);
    }

    static void collect_tokens_dir(euf::snode* s, bool fwd, euf::snode_vector& toks) {
        toks.reset();
        if (!s) return;
        s->collect_tokens(toks);
        if (fwd || toks.size() < 2) return;
        unsigned n = toks.size();
        for (unsigned i = 0; i < n / 2; ++i)
            std::swap(toks[i], toks[n - 1 - i]);
    }

    // Right-derivative helper used by backward str_mem simplification:
    // dR(re, c) = reverse( derivative(c, reverse(re)) ).
    static euf::snode* reverse_brzozowski_deriv(euf::sgraph& sg, euf::snode* re, euf::snode* elem) {
        if (!re || !elem || !re->get_expr() || !elem->get_expr())
            return nullptr;
        ast_manager& m = sg.get_manager();
        seq_util& seq = sg.get_seq_util();
        seq_rewriter rw(m);

        expr* elem_expr = elem->get_expr();
        expr* ch = nullptr;
        if (seq.str.is_unit(elem_expr, ch))
            elem_expr = ch;

        expr_ref re_rev(seq.re.mk_reverse(re->get_expr()), m);
        expr_ref d = rw.mk_derivative(elem_expr, re_rev);
        if (!d.get())
            return nullptr;
        expr_ref result(seq.re.mk_reverse(d), m);
        th_rewriter tr(m);
        tr(result);
        return sg.mk(result);
    }

    // -----------------------------------------------
    // str_eq
    // -----------------------------------------------

    void str_eq::sort() {
        if (m_lhs && m_rhs && m_lhs->id() > m_rhs->id()) {
            std::swap(m_lhs, m_rhs);
        }
    }

    bool str_eq::is_trivial() const {
        return m_lhs == m_rhs ||
               (m_lhs && m_rhs && m_lhs->is_empty() && m_rhs->is_empty());
    }

    bool str_eq::contains_var(euf::snode* var) const {
        if (!var)
            return false;
        // check if var appears in the token list of lhs or rhs
        if (m_lhs) {
            euf::snode_vector tokens;
            m_lhs->collect_tokens(tokens);
            for (euf::snode* t : tokens) {
                if (t == var)
                    return true;
            }
        }
        if (m_rhs) {
            euf::snode_vector tokens;
            m_rhs->collect_tokens(tokens);
            for (euf::snode* t : tokens) {
                if (t == var)
                    return true;
            }
        }
        return false;
    }

    // -----------------------------------------------
    // str_mem
    // -----------------------------------------------

    bool str_mem::is_primitive() const {
        return m_str && m_str->length() == 1 && m_str->is_var();
    }

    bool str_mem::is_trivial() const {
        return m_str && m_regex && m_str->is_empty() && m_regex->is_nullable();
    }

    bool str_mem::contains_var(euf::snode* var) const {
        SASSERT(var);
        if (m_str) {
            euf::snode_vector tokens;
            m_str->collect_tokens(tokens);
            for (const euf::snode* t : tokens) {
                if (t == var)
                    return true;
            }
        }
        return false;
    }

    // -----------------------------------------------
    // nielsen_subst
    // -----------------------------------------------

    bool nielsen_subst::is_eliminating() const {
        SASSERT(m_var && m_replacement);
        // check if var appears in replacement
        euf::snode_vector tokens;
        m_replacement->collect_tokens(tokens);
        for (const euf::snode* t : tokens) {
            if (t == m_var)
                return false;
        }
        return true;
    }

    // -----------------------------------------------
    // nielsen_edge
    // -----------------------------------------------

    nielsen_edge::nielsen_edge(nielsen_node* src, nielsen_node* tgt, bool is_progress):
        m_src(src), m_tgt(tgt), m_is_progress(is_progress) { }

    // -----------------------------------------------
    // nielsen_node
    // -----------------------------------------------

    nielsen_node::nielsen_node(nielsen_graph& graph, unsigned id):
        m_id(id), m_graph(graph), m_is_progress(true) { }

    void nielsen_node::clone_from(nielsen_node const& parent) {
        m_str_eq.reset();
        m_str_mem.reset();
        m_int_constraints.reset();
        m_char_diseqs.reset();
        m_char_ranges.reset();
        m_var_lb.reset();
        m_var_ub.reset();
        for (auto const& eq : parent.m_str_eq)
            m_str_eq.push_back(str_eq(eq.m_lhs, eq.m_rhs, eq.m_dep));
        for (auto const& mem : parent.m_str_mem)
            m_str_mem.push_back(str_mem(mem.m_str, mem.m_regex, mem.m_history, mem.m_id, mem.m_dep));
        for (auto const& ic : parent.m_int_constraints)
            m_int_constraints.push_back(ic);
        
        // clone character disequalities
        for (auto const& kv : parent.m_char_diseqs) {
            ptr_vector<euf::snode> diseqs;
            for (euf::snode* s : kv.m_value) {
                diseqs.push_back(s);
            }
            m_char_diseqs.insert(kv.m_key, diseqs);
        }
        // clone character ranges
        for (auto const& kv : parent.m_char_ranges) {
            m_char_ranges.insert(kv.m_key, kv.m_value.clone());
        }
        // clone per-variable integer bounds
        for (auto const& kv : parent.m_var_lb) {
            m_var_lb.insert(kv.m_key, kv.m_value);
        }
        for (auto const& kv : parent.m_var_ub) {
            m_var_ub.insert(kv.m_key, kv.m_value);
        }
        // clone regex occurrence tracking
        m_regex_occurrence = parent.m_regex_occurrence;
    }

    bool nielsen_node::track_regex_occurrence(unsigned regex_id, unsigned mem_id) {
        auto key = std::make_pair(regex_id, mem_id);
        auto it = m_regex_occurrence.find(key);
        if (it != m_regex_occurrence.end()) {
            // Already seen — cycle detected
            return true;
        }
        m_regex_occurrence[key] = m_id;
        return false;
    }

    // NSB review: optimize sg.subst to apply join only if the substitution had an effect.
    void nielsen_node::apply_subst(euf::sgraph& sg, nielsen_subst const& s) {
        if (!s.m_var)
            return;
        for (unsigned i = 0; i < m_str_eq.size(); ++i) {
            str_eq& eq = m_str_eq[i];
            eq.m_lhs = sg.subst(eq.m_lhs, s.m_var, s.m_replacement);
            eq.m_rhs = sg.subst(eq.m_rhs, s.m_var, s.m_replacement);
            eq.m_dep = m_graph.dep_mgr().mk_join(eq.m_dep, s.m_dep);
            eq.sort();
        }
        for (unsigned i = 0; i < m_str_mem.size(); ++i) {
            str_mem& mem = m_str_mem[i];
            mem.m_str = sg.subst(mem.m_str, s.m_var, s.m_replacement);
            // regex is typically ground, but apply subst for generality
            mem.m_regex = sg.subst(mem.m_regex, s.m_var, s.m_replacement);
            mem.m_dep = m_graph.dep_mgr().mk_join(mem.m_dep, s.m_dep);
        }
        // VarBoundWatcher: propagate bounds on s.m_var to variables in s.m_replacement
        watch_var_bounds(s);
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
        }
        else
            m_char_ranges.insert(id, range.clone());
    }

    void nielsen_node::add_char_diseq(euf::snode* sym_char, euf::snode* other) {
        SASSERT(sym_char && sym_char->is_unit());
        SASSERT(other && other->is_unit());
        unsigned id = sym_char->id();
        if (!m_char_diseqs.contains(id))
            m_char_diseqs.insert(id, ptr_vector<euf::snode>());
        ptr_vector<euf::snode>& existing = m_char_diseqs.find(id);
        // check for duplicates
        for (euf::snode* s : existing) {
            if (s == other)
                return;
        }
        existing.push_back(other);
    }

    // -----------------------------------------------
    // nielsen_node: IntBounds methods
    // mirrors ZIPT's AddLowerIntBound / AddHigherIntBound
    // -----------------------------------------------

    unsigned nielsen_node::var_lb(euf::snode* var) const {
        SASSERT(var);
        unsigned v = 0;
        m_var_lb.find(var->id(), v);
        return v;
    }

    unsigned nielsen_node::var_ub(euf::snode* var) const {
        SASSERT(!var);
        unsigned v = UINT_MAX;
        m_var_ub.find(var->id(), v);
        return v;
    }

    bool nielsen_node::add_lower_int_bound(euf::snode* var, unsigned lb, dep_tracker const& dep) {
        SASSERT(var && var->is_var());
        unsigned id = var->id();
        // check against existing lower bound
        unsigned cur_lb = 0;
        m_var_lb.find(id, cur_lb);
        if (lb <= cur_lb) return false;  // no tightening
        m_var_lb.insert(id, lb);
        // conflict if lb > current upper bound
        unsigned cur_ub = UINT_MAX;
        m_var_ub.find(id, cur_ub);
        if (lb > cur_ub) {
            m_is_general_conflict = true;
            m_reason = backtrack_reason::arithmetic;
            return true;
        }
        // add int_constraint: len(var) >= lb
        ast_manager& m = m_graph.get_manager();
        seq_util& seq = m_graph.seq();
        arith_util arith(m);
        expr_ref len_var(seq.str.mk_length(var->get_expr()), m);
        expr_ref bound(arith.mk_int(lb), m);
        m_int_constraints.push_back(int_constraint(len_var, bound, int_constraint_kind::ge, dep, m));
        return true;
    }

    bool nielsen_node::add_upper_int_bound(euf::snode* var, unsigned ub, dep_tracker const& dep) {
        if (!var || !var->is_var()) return false;
        unsigned id = var->id();
        // check against existing upper bound
        unsigned cur_ub = UINT_MAX;
        m_var_ub.find(id, cur_ub);
        if (ub >= cur_ub) return false;  // no tightening
        m_var_ub.insert(id, ub);
        // conflict if current lower bound > ub
        unsigned cur_lb = 0;
        m_var_lb.find(id, cur_lb);
        if (cur_lb > ub) {
            m_is_general_conflict = true;
            m_reason = backtrack_reason::arithmetic;
            return true;
        }
        // add int_constraint: len(var) <= ub
        ast_manager& m = m_graph.get_manager();
        seq_util& seq = m_graph.seq();
        arith_util arith(m);
        expr_ref len_var(seq.str.mk_length(var->get_expr()), m);
        expr_ref bound(arith.mk_int(ub), m);
        m_int_constraints.push_back(int_constraint(len_var, bound, int_constraint_kind::le, dep, m));
        return true;
    }

    // VarBoundWatcher: after applying substitution s, propagate bounds on s.m_var
    // to variables in s.m_replacement.
    // If s.m_var has bounds [lo, hi], and the replacement decomposes into
    // const_len concrete chars plus a list of variable tokens, then:
    //   - for a single variable y: lo-const_len <= len(y) <= hi-const_len
    //   - for multiple variables: each gets an upper bound hi-const_len
    // Mirrors ZIPT's VarBoundWatcher mechanism.
    void nielsen_node::watch_var_bounds(nielsen_subst const& s) {
        SASSERT(s.m_var);
        unsigned id = s.m_var->id();
        unsigned lo = 0, hi = UINT_MAX;
        m_var_lb.find(id, lo);
        m_var_ub.find(id, hi);
        if (lo == 0 && hi == UINT_MAX)
            return;  // no bounds to propagate

        // decompose replacement into constant length + variable tokens
        if (!s.m_replacement)
            return;
        euf::snode_vector tokens;
        s.m_replacement->collect_tokens(tokens);

        unsigned const_len = 0;
        euf::snode_vector var_tokens;
        for (euf::snode* t : tokens) {
            if (t->is_char() || t->is_unit())
                ++const_len;
            else if (t->is_var())
                var_tokens.push_back(t);
            else
                // power or unknown token: cannot propagate simply, abort
                return;
        }

        if (var_tokens.empty()) {
            // all concrete: check if const_len is within [lo, hi]
            if (const_len < lo || (hi != UINT_MAX && const_len > hi)) {
                m_is_general_conflict = true;
                m_reason = backtrack_reason::arithmetic;
            }
            return;
        }

        if (var_tokens.size() == 1) {
            euf::snode* y = var_tokens[0];
            // lo <= const_len + len(y) => len(y) >= lo - const_len (if lo > const_len)
            if (lo > const_len)
                add_lower_int_bound(y, lo - const_len, s.m_dep);
            // const_len + len(y) <= hi => len(y) <= hi - const_len
            if (hi != UINT_MAX) {
                if (const_len > hi) {
                    m_is_general_conflict = true;
                    m_reason = backtrack_reason::arithmetic;
                }
                else
                    add_upper_int_bound(y, hi - const_len, s.m_dep);
            }
        }
        else {
            // multiple variables: propagate upper bound to each
            // (each variable contributes >= 0, so each <= hi - const_len)
            if (hi != UINT_MAX) {
                if (const_len > hi) {
                    m_is_general_conflict = true;
                    m_reason = backtrack_reason::arithmetic;
                    return;
                }
                unsigned each_ub = hi - const_len;
                for (euf::snode* y : var_tokens) {
                    add_upper_int_bound(y, each_ub, s.m_dep);
                }
            }
        }
    }

    // Initialize per-variable Parikh bounds from this node's regex memberships.
    // For each str_mem (str ∈ regex) with bounded regex length [min_len, max_len],
    // calls add_lower/upper_int_bound for the primary string variable (if str is
    // a single variable) or stores a bound on the length expression otherwise.
    void nielsen_node::init_var_bounds_from_mems() {
        for (str_mem const& mem : m_str_mem) {
            if (!mem.m_str || !mem.m_regex) continue;
            unsigned min_len = 0, max_len = UINT_MAX;
            m_graph.compute_regex_length_interval(mem.m_regex, min_len, max_len);
            if (min_len == 0 && max_len == UINT_MAX) continue;

            // if str is a single variable, apply bounds directly
            if (mem.m_str->is_var()) {
                if (min_len > 0)
                    add_lower_int_bound(mem.m_str, min_len, mem.m_dep);
                if (max_len < UINT_MAX)
                    add_upper_int_bound(mem.m_str, max_len, mem.m_dep);
            }
            else {
                // str is a concatenation or other term: add as general int_constraints
                ast_manager& m = m_graph.get_manager();
                arith_util arith(m);
                expr_ref len_str = m_graph.compute_length_expr(mem.m_str);
                if (min_len > 0) {
                    expr_ref bound(arith.mk_int(min_len), m);
                    m_int_constraints.push_back(
                        int_constraint(len_str, bound, int_constraint_kind::ge, mem.m_dep, m));
                }
                if (max_len < UINT_MAX) {
                    expr_ref bound(arith.mk_int(max_len), m);
                    m_int_constraints.push_back(
                        int_constraint(len_str, bound, int_constraint_kind::le, mem.m_dep, m));
                }
            }
        }
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
        }
        else {
            SASSERT(s.m_val->is_char());
            // symbolic char → concrete char: check range constraints
            if (m_char_ranges.contains(var_id)) {
                char_set& range = m_char_ranges.find(var_id);
                unsigned ch_val = 0;
                seq_util& seq = sg.get_seq_util();
                expr* unit_expr = s.m_val->get_expr();
                expr* ch_expr = nullptr;
                bool have_char = unit_expr && seq.str.is_unit(unit_expr, ch_expr) && seq.is_const_char(ch_expr, ch_val);
                if (have_char && !range.contains(ch_val)) {
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

    nielsen_graph::nielsen_graph(euf::sgraph& sg, simple_solver& solver):
        m(sg.get_manager()),
        m_seq(sg.get_seq_util()),
        m_sg(sg),
        m_solver(solver),
        m_parikh(alloc(seq_parikh, sg)),
        m_seq_regex(alloc(seq::seq_regex, sg)),
        m_len_vars(sg.get_manager()) {
    }

    nielsen_graph::~nielsen_graph() {
        dealloc(m_parikh);
        dealloc(m_seq_regex);
        reset();
    }

    nielsen_node* nielsen_graph::mk_node() {
        unsigned id = m_nodes.size();
        nielsen_node* n = alloc(nielsen_node, *this, id);
        m_nodes.push_back(n);
        return n;
    }

    nielsen_node* nielsen_graph::mk_child(nielsen_node* parent) {
        nielsen_node* child = mk_node();
        child->clone_from(*parent);
        child->m_parent_ic_count = parent->int_constraints().size();
        return child;
    }

    nielsen_edge* nielsen_graph::mk_edge(nielsen_node* src, nielsen_node* tgt, bool is_progress) {
        nielsen_edge* e = alloc(nielsen_edge, src, tgt, is_progress);
        m_edges.push_back(e);
        src->add_outgoing(e);
        return e;
    }

    void nielsen_graph::add_str_eq(euf::snode* lhs, euf::snode* rhs, smt::enode* l, smt::enode* r) {
        if (!m_root)
            m_root = mk_node();
        dep_tracker dep = m_dep_mgr.mk_leaf(enode_pair(l, r));
        str_eq eq(lhs, rhs, dep);
        eq.sort();
        m_root->add_str_eq(eq);
    }

    void nielsen_graph::add_str_mem(euf::snode* str, euf::snode* regex, sat::literal l) {
        if (!m_root)
            m_root = mk_node();
        dep_tracker dep = m_dep_mgr.mk_leaf(l);
        euf::snode* history = m_sg.mk_empty_seq(str->get_sort());
        unsigned id = next_mem_id();
        m_root->add_str_mem(str_mem(str, regex, history, id, dep));
    }

    // test-friendly overloads (no external dependency tracking)
    void nielsen_graph::add_str_eq(euf::snode* lhs, euf::snode* rhs) {
        if (!m_root)
            m_root = mk_node();
        dep_tracker dep = m_dep_mgr.mk_leaf(enode_pair(nullptr, nullptr));
        str_eq eq(lhs, rhs, dep);
        eq.sort();
        m_root->add_str_eq(eq);
    }

    void nielsen_graph::add_str_mem(euf::snode* str, euf::snode* regex) {
        if (!m_root)
            m_root = mk_node();
        dep_tracker dep = nullptr;
        euf::snode* history = m_sg.mk_empty_seq(str->get_sort());
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
        m_sat_node = nullptr;
        m_sat_path.reset();
        m_run_idx = 0;
        m_depth_bound = 0;
        m_next_mem_id = 0;
        m_fresh_cnt = 0;
        m_root_constraints_asserted = false;
        m_mod_cnt.reset();
        m_len_var_cache.clear();
        m_len_vars.reset();
        m_dep_mgr.reset();
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
            }
            else
                result += r[i++];
        }
        return result;
    }

    // Helper: render an arithmetic/integer expression in infix HTML notation.
    // Recognises +, -, *, unary minus, numerals, str.len, and named constants;
    // falls back to HTML-escaped mk_pp for anything else.
    static std::string arith_expr_html(expr* e, ast_manager& m) {
        if (!e) return "null";
        arith_util arith(m);
        seq_util seq(m);
        rational val;
        if (arith.is_numeral(e, val))
            return val.to_string();
        if (!is_app(e)) {
            std::ostringstream os;
            os << mk_pp(e, m);
            return dot_html_escape(os.str());
        }
        app* a = to_app(e);
        expr* x, * y;
        if (arith.is_add(e)) {
            std::string r = arith_expr_html(a->get_arg(0), m);
            for (unsigned i = 1; i < a->get_num_args(); ++i) {
                expr* arg = a->get_arg(i);
                // render (+ x (- y)) as "x - y" and (+ x (- n)) as "x - n"
                expr* neg_inner;
                rational neg_val;
                if (arith.is_uminus(arg, neg_inner)) {
                    r += " &#8722; "; // minus sign
                    r += arith_expr_html(neg_inner, m);
                } else if (arith.is_numeral(arg, neg_val) && neg_val.is_neg()) {
                    r += " &#8722; "; // minus sign
                    r += (-neg_val).to_string();
                }
                else {
                    r += " + ";
                    r += arith_expr_html(arg, m);
                }
            }
            return r;
        }
        if (arith.is_sub(e, x, y))
            return arith_expr_html(x, m) + " &#8722; " + arith_expr_html(y, m);
        if (arith.is_uminus(e, x))
            return "&#8722;" + arith_expr_html(x, m);
        if (arith.is_mul(e)) {
            std::string r;
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                if (i > 0) r += " &#183; "; // middle dot
                r += arith_expr_html(a->get_arg(i), m);
            }
            return r;
        }
        if (seq.str.is_length(e, x)) {
            return "|" + dot_html_escape(to_app(x)->get_decl()->get_name().str()) + "|";
        }
        // named constant (fresh variable like n!0)
        if (a->get_num_args() == 0)
            return dot_html_escape(a->get_decl()->get_name().str());
        // fallback
        std::ostringstream os;
        os << mk_pp(e, m);
        return dot_html_escape(os.str());
    }

    // Helper: render an int_constraint as an HTML string for DOT edge labels.
    static std::string int_constraint_html(int_constraint const& ic, ast_manager& m) {
        std::string r = arith_expr_html(ic.m_lhs, m);
        switch (ic.m_kind) {
        case int_constraint_kind::eq: r += " = ";       break;
        case int_constraint_kind::le: r += " &#8804; "; break; // ≤
        case int_constraint_kind::ge: r += " &#8805; "; break; // ≥
        }
        r += arith_expr_html(ic.m_rhs, m);
        return r;
    }

    static std::string regex_expr_html(expr* e, ast_manager& m, seq_util& seq) {
        if (!e)
            return "null";
        expr* a = nullptr, * b = nullptr;

        if (seq.re.is_to_re(e, a)) {
            zstring s;
            if (seq.str.is_string(a, s))
                return "\"" + dot_html_escape(s.encode()) + "\"";
            unsigned ch_val = 0;
            if (seq.str.is_unit(a) && seq.is_const_char(to_app(a)->get_arg(0), ch_val)) {
                return "\"" + dot_html_escape(zstring(ch_val).encode()) + "\"";
            }
            std::ostringstream os;
            os << mk_pp(a, m);
            return dot_html_escape(os.str());
        }
        if (seq.re.is_concat(e)) {
            app* ap = to_app(e);
            std::string res;
            if (ap->get_num_args() == 0) return "()";
            for (unsigned i = 0; i < ap->get_num_args(); ++i) {
                if (i > 0) res += " ";
                bool needs_parens = seq.re.is_union(ap->get_arg(i));
                if (needs_parens) res += "(";
                res += regex_expr_html(ap->get_arg(i), m, seq);
                if (needs_parens) res += ")";
            }
            return res;
        }
        if (seq.re.is_union(e)) {
            app* ap = to_app(e);
            std::string res;
            if (ap->get_num_args() == 0) return "&#8709;";
            for (unsigned i = 0; i < ap->get_num_args(); ++i) {
                if (i > 0) res += " | ";
                res += regex_expr_html(ap->get_arg(i), m, seq);
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
                res += regex_expr_html(ap->get_arg(i), m, seq);
                if (needs_parens) res += ")";
            }
            return res;
        }
        if (seq.re.is_star(e, a)) {
            bool needs_parens = seq.re.is_union(a) || seq.re.is_concat(a) || seq.re.is_intersection(a);
            std::string res = needs_parens ? "(" : "";
            res += regex_expr_html(a, m, seq);
            res += needs_parens ? ")<SUP>*</SUP>" : "<SUP>*</SUP>";
            return res;
        }
        if (seq.re.is_plus(e, a)) {
            bool needs_parens = seq.re.is_union(a) || seq.re.is_concat(a) || seq.re.is_intersection(a);
            std::string res = needs_parens ? "(" : "";
            res += regex_expr_html(a, m, seq);
            res += needs_parens ? ")<SUP>+</SUP>" : "<SUP>+</SUP>";
            return res;
        }
        if (seq.re.is_opt(e, a)) {
            bool needs_parens = seq.re.is_union(a) || seq.re.is_concat(a) || seq.re.is_intersection(a);
            std::string res = needs_parens ? "(" : "";
            res += regex_expr_html(a, m, seq);
            res += needs_parens ? ")?" : "?";
            return res;
        }
        if (seq.re.is_complement(e, a)) {
            bool needs_parens = seq.re.is_union(a) || seq.re.is_concat(a) || seq.re.is_intersection(a);
            std::string res = "~";
            res += needs_parens ? "(" : "";
            res += regex_expr_html(a, m, seq);
            res += needs_parens ? ")" : "";
            return res;
        }
        if (seq.re.is_range(e, a, b)) {
            zstring s1, s2;
            std::string c1 = seq.str.is_string(a, s1) ? dot_html_escape(s1.encode()) : arith_expr_html(a, m);
            std::string c2 = seq.str.is_string(b, s2) ? dot_html_escape(s2.encode()) : arith_expr_html(b, m);
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
        return dot_html_escape(os.str());
    }

    // Helper: render a snode as an HTML label for DOT output.
    // Groups consecutive s_char tokens into quoted strings, renders s_var by name,
    // shows s_power with superscripts, s_unit by its inner expression,
    // and falls back to mk_pp (HTML-escaped) for other token kinds.

    static std::string snode_label_html(euf::snode const* n, ast_manager& m) {
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
            result += "\"" + dot_html_escape(char_acc) + "\"";
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
                    }
                    else {
                        flush_chars();
                        char buf[16];
                        snprintf(buf, sizeof(buf), "'\\x%x'", code);
                        if (!first)
                            result += " + ";
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
                result += dot_html_escape(to_app(e)->get_decl()->get_name().str());
            } else if (tok->is_unit()) {
                // seq.unit with non-literal character: show the character expression
                expr* ch = to_app(e)->get_arg(0);
                if (is_app(ch))
                    result += dot_html_escape(to_app(ch)->get_decl()->get_name().str());
                else {
                    std::ostringstream os;
                    os << mk_pp(ch, m);
                    result += dot_html_escape(os.str());
                }
            }
            else if (tok->is_power()) {
                // seq.power(base, n): render as base<SUP>n</SUP>
                std::string base_html = snode_label_html(tok->arg(0), m);
                if (tok->arg(0)->length() > 1)
                    base_html = "(" + base_html + ")";
                result += base_html;
                result += "<SUP>";
                expr* exp_expr = to_app(e)->get_arg(1);
                result += arith_expr_html(exp_expr, m);
                result += "</SUP>";
            }
            else if (e && seq.is_re(e))
                result += regex_expr_html(e, m, seq);
            else {
                std::ostringstream os;
                os << mk_pp(e, m);
                result += dot_html_escape(os.str());
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
            out << snode_label_html(eq.m_lhs, m)
                << " = "
                << snode_label_html(eq.m_rhs, m)
                << "<br/>";
        }
        // regex memberships
        for (auto const& mem : m_str_mem) {
            if (!any) { out << "Cnstr:<br/>"; any = true; }
            out << snode_label_html(mem.m_str, m)
                << " &#8712; "
                << snode_label_html(mem.m_regex, m)
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
        // integer constraints
        for (auto const& ic : m_int_constraints) {
            if (!any) { out << "Cnstr:<br/>"; any = true; }
            out << int_constraint_html(ic, m) << "<br/>";
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
            out << "    " << n->id() << " [label=<"
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
                out << "    " << n->id() << " -> " << e->tgt()->id() << " [label=<";

                // edge label: substitutions joined by <br/>
                bool first = true;
                for (auto const& s : e->subst()) {
                    if (!first) out << "<br/>";
                    first = false;
                    out << snode_label_html(s.m_var, m)
                        << " &#8594; " // mapping arrow
                        << snode_label_html(s.m_replacement, m);
                }
                for (auto const& cs : e->char_substs()) {
                    if (!first) out << "<br/>";
                    first = false;
                    out << "?" << cs.m_var->id()
                        << " &#8594; ?" << cs.m_val->id();
                }
                // side constraints: string equalities
                for (auto const* eq : e->side_str_eq()) {
                    if (!first) out << "<br/>";
                    first = false;
                    out << "<font color=\"gray\">"
                        << snode_label_html(eq->m_lhs, m)
                        << " = "
                        << snode_label_html(eq->m_rhs, m)
                        << "</font>";
                }
                // side constraints: regex memberships
                for (auto const* mem : e->side_str_mem()) {
                    if (!first) out << "<br/>";
                    first = false;
                    out << "<font color=\"gray\">"
                        << snode_label_html(mem->m_str, m)
                        << " &#8712; "
                        << snode_label_html(mem->m_regex, m)
                        << "</font>";
                }
                // side constraints: integer equalities/inequalities
                for (auto const& ic : e->side_int()) {
                    if (!first) out << "<br/>";
                    first = false;
                    out << "<font color=\"gray\">"
                        << int_constraint_html(ic, m)
                        << "</font>";
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
                out << "    " << n->id() << " -> " << n->backedge()->id()
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
        bool has_char = std::any_of(tokens.begin(), tokens.end(), [](euf::snode* t){ return t->is_char(); });
        bool all_eliminable = std::all_of(tokens.begin(), tokens.end(), [](euf::snode* t){
            return t->is_var() || t->is_power() || t->kind() == euf::snode_kind::s_other;
        });
        if (has_char || !all_eliminable) {
            m_is_general_conflict = true;
            m_reason = backtrack_reason::symbol_clash;
            return true;
        }
        ast_manager& m = sg.get_manager();
        arith_util arith(m);
        seq_util& seq = sg.get_seq_util();
        for (euf::snode* t : tokens) {
            if (t->is_var()) {
                nielsen_subst s(t, sg.mk_empty_seq(t->get_sort()), dep);
                apply_subst(sg, s);
                changed = true;
            }
            else if (t->is_power()) {
                // Power equated to empty → exponent must be 0.
                expr* e = t->get_expr();
                expr* pow_base = nullptr, *pow_exp = nullptr;
                if (e) seq.str.is_power(e, pow_base, pow_exp);
                if (pow_exp) {
                    expr* zero = arith.mk_numeral(rational(0), true);
                    m_int_constraints.push_back(
                        int_constraint(pow_exp, zero, int_constraint_kind::eq, dep, m));
                }
                nielsen_subst s(t, sg.mk_empty_seq(t->get_sort()), dep);
                apply_subst(sg, s);
                changed = true;
            }
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Power simplification helpers (mirrors ZIPT's MergePowers,
    // SimplifyPowerElim/CommPower, SimplifyPowerSingle)
    // -----------------------------------------------------------------------

    // Check if exponent b equals exponent a + diff for some rational constant diff.
    // Uses syntactic matching on Z3 expression structure: pointer equality
    // detects shared sub-expressions created during ConstNumUnwinding.
    //
    static bool get_const_power_diff(expr* b, expr* a, arith_util& arith, rational& diff) {
        if (a == b) { diff = rational(0); return true; }
        // b = (+ a k) ?
        if (arith.is_add(b) && to_app(b)->get_num_args() == 2) {
            rational val;
            if (to_app(b)->get_arg(0) == a && arith.is_numeral(to_app(b)->get_arg(1), val))
                { diff = val; return true; }
            if (to_app(b)->get_arg(1) == a && arith.is_numeral(to_app(b)->get_arg(0), val))
                { diff = val; return true; }
        }
        // a = (+ b k) → diff = -k
        if (arith.is_add(a) && to_app(a)->get_num_args() == 2) {
            rational val;
            if (to_app(a)->get_arg(0) == b && arith.is_numeral(to_app(a)->get_arg(1), val))
                { diff = -val; return true; }
            if (to_app(a)->get_arg(1) == b && arith.is_numeral(to_app(a)->get_arg(0), val))
                { diff = -val; return true; }
        }
        // b = (- a k) → diff = -k
        if (arith.is_sub(b) && to_app(b)->get_num_args() == 2) {
            rational val;
            if (to_app(b)->get_arg(0) == a && arith.is_numeral(to_app(b)->get_arg(1), val))
                { diff = -val; return true; }
        }
        // a = (- b k) → diff = k
        if (arith.is_sub(a) && to_app(a)->get_num_args() == 2) {
            rational val;
            if (to_app(a)->get_arg(0) == b && arith.is_numeral(to_app(a)->get_arg(1), val))
                { diff = val; return true; }
        }
        return false;
    }

    // Get the base expression of a power snode.
    static expr* get_power_base_expr(euf::snode* power, seq_util& seq) {
        if (!power || !power->is_power()) return nullptr;
        expr* e = power->get_expr();
        expr* base = nullptr, *exp = nullptr;
        return (e && seq.str.is_power(e, base, exp)) ? base : nullptr;
    }

    // Get the exponent expression of a power snode.
    static expr* get_power_exp_expr(euf::snode* power, seq_util& seq) {
        if (!power || !power->is_power()) return nullptr;
        expr* e = power->get_expr();
        expr* base = nullptr, *exp = nullptr;
        return (e && seq.str.is_power(e, base, exp)) ? exp : nullptr;
    }

    // Merge adjacent tokens with the same power base on one side of an equation.
    // Handles: char(c) · power(c^e) → power(c^(e+1)),
    //          power(c^e) · char(c) → power(c^(e+1)),
    //          power(c^e1) · power(c^e2) → power(c^(e1+e2)).
    // Returns new snode if merging happened, nullptr otherwise.
    static euf::snode* merge_adjacent_powers(euf::sgraph& sg, euf::snode* side) {
        if (!side || side->is_empty() || side->is_token())
            return nullptr;

        euf::snode_vector tokens;
        side->collect_tokens(tokens);
        if (tokens.size() < 2) return nullptr;

        ast_manager& m = sg.get_manager();
        arith_util arith(m);
        seq_util& seq = sg.get_seq_util();

        bool merged = false;
        euf::snode_vector result;

        unsigned i = 0;
        while (i < tokens.size()) {
            euf::snode* tok = tokens[i];

            // Case 1: current is a power token — absorb following same-base tokens.
            // Skip at leading position (i == 0) to keep exponents small: CommPower
            // cross-side cancellation works better with unmerged leading powers
            // (e.g., w^k trivially ≤ 1+k, but w^(2k) vs 1+k requires k ≥ 1).
            if (tok->is_power() && i > 0) {
                expr* base_e = get_power_base_expr(tok, seq);
                expr* exp_acc = get_power_exp_expr(tok, seq);
                if (!base_e || !exp_acc) { result.push_back(tok); ++i; continue; }

                bool local_merged = false;
                unsigned j = i + 1;
                while (j < tokens.size()) {
                    euf::snode* next = tokens[j];
                    if (next->is_power()) {
                        expr* nb = get_power_base_expr(next, seq);
                        if (nb == base_e) {
                            exp_acc = arith.mk_add(exp_acc, get_power_exp_expr(next, seq));
                            local_merged = true; ++j; continue;
                        }
                    }
                    if (next->is_char() && next->get_expr() == base_e) {
                        exp_acc = arith.mk_add(exp_acc, arith.mk_int(1));
                        local_merged = true; ++j; continue;
                    }
                    break;
                }
                if (local_merged) {
                    merged = true;
                    expr_ref norm_exp = normalize_arith(m, exp_acc);
                    expr_ref new_pow(seq.str.mk_power(base_e, norm_exp), m);
                    result.push_back(sg.mk(new_pow));
                }
                else
                    result.push_back(tok);
                i = j;
                continue;
            }

            // Case 2: current is a char — check if next is a same-base power.
            // Skip at leading position (i == 0) to avoid undoing power unwinding:
            // unwind produces u · u^(n-1); merging it back to u^n creates an infinite cycle.
            if (i > 0 && tok->is_char() && tok->get_expr() && i + 1 < tokens.size()) {
                euf::snode* next = tokens[i + 1];
                if (next->is_power() && get_power_base_expr(next, seq) == tok->get_expr()) {
                    expr* base_e = tok->get_expr();
                    // Use same arg order as Case 1: add(exp, 1), not add(1, exp),
                    // so that merging "c · c^e" and "c^e · c" both produce add(e, 1)
                    // and the resulting power expression is hash-consed identically.
                    expr* exp_acc = arith.mk_add(get_power_exp_expr(next, seq), arith.mk_int(1));
                    unsigned j = i + 2;
                    while (j < tokens.size()) {
                        euf::snode* further = tokens[j];
                        if (further->is_power() && get_power_base_expr(further, seq) == base_e) {
                            exp_acc = arith.mk_add(exp_acc, get_power_exp_expr(further, seq));
                            ++j; continue;
                        }
                        if (further->is_char() && further->get_expr() == base_e) {
                            exp_acc = arith.mk_add(exp_acc, arith.mk_int(1));
                            ++j; continue;
                        }
                        break;
                    }
                    merged = true;
                    expr_ref norm_exp = normalize_arith(m, exp_acc);
                    expr_ref new_pow(seq.str.mk_power(base_e, norm_exp), m);
                    result.push_back(sg.mk(new_pow));
                    i = j;
                    continue;
                }
            }

            result.push_back(tok);
            ++i;
        }

        if (!merged) return nullptr;

        euf::snode* rebuilt = nullptr;
        for (unsigned k = 0; k < result.size(); ++k)
            rebuilt = (k == 0) ? result[k] : sg.mk_concat(rebuilt, result[k]);
        if (!rebuilt) rebuilt = sg.mk_empty_seq(side->get_sort());
        return rebuilt;
    }

    // Simplify constant-exponent powers: base^0 → ε, base^1 → base.
    // Returns new snode if any simplification happened, nullptr otherwise.
    static euf::snode* simplify_const_powers(euf::sgraph& sg, euf::snode* side) {
        if (!side || side->is_empty())
            return nullptr;

        euf::snode_vector tokens;
        side->collect_tokens(tokens);

        ast_manager& m = sg.get_manager();
        arith_util arith(m);
        seq_util& seq = sg.get_seq_util();

        bool simplified = false;
        euf::snode_vector result;

        for (euf::snode* tok : tokens) {
            if (tok->is_power()) {
                expr* exp_e = get_power_exp_expr(tok, seq);
                rational val;
                if (exp_e && arith.is_numeral(exp_e, val)) {
                    if (val.is_zero()) {
                        // base^0 → ε (skip this token entirely)
                        simplified = true;
                        continue;
                    }
                    if (val.is_one()) {
                        // base^1 → base
                        euf::snode* base_sn = tok->arg(0);
                        if (base_sn) {
                            result.push_back(base_sn);
                            simplified = true;
                            continue;
                        }
                    }
                }
            }
            result.push_back(tok);
        }

        if (!simplified)
            return nullptr;

        euf::snode* rebuilt = nullptr;
        for (euf::snode* tok : result) {
            rebuilt = rebuilt ? sg.mk_concat(rebuilt, tok) : tok;
        }
        if (!rebuilt)
            rebuilt = sg.mk_empty_seq(side->get_sort());
        return rebuilt;
    }

    // CommPower: count how many times a power's base pattern appears in
    // the directional prefix of the other side (fwd=true: left prefix,
    // fwd=false: right suffix). Mirrors ZIPT's CommPower helper.
    // Returns (count_expr, num_tokens_consumed).  count_expr is nullptr
    // when no complete base-pattern match is found.
    static std::pair<expr_ref, unsigned> comm_power(
            euf::snode* base_sn, euf::snode* side, ast_manager& m, seq_util& seq, bool fwd) {
        arith_util arith(m);
        euf::snode_vector base_tokens, side_tokens;
        collect_tokens_dir(base_sn, fwd, base_tokens);
        collect_tokens_dir(side, fwd, side_tokens);
        if (base_tokens.empty() || side_tokens.empty())
            return {expr_ref(nullptr, m), 0};

        expr* sum = nullptr;
        unsigned pos = 0;
        expr* last_stable_sum = nullptr;
        unsigned last_stable_idx = 0;

        unsigned i = 0;
        for (; i < side_tokens.size(); i++) {
            euf::snode* t = side_tokens[i];
            if (pos == 0) {
                last_stable_idx = i;
                last_stable_sum = sum;
            }
            // Case 1: direct token match with base pattern
            if (pos < base_tokens.size() && t == base_tokens[pos]) {
                pos++;
                if (pos >= base_tokens.size()) {
                    pos = 0;
                    sum = sum ? arith.mk_add(sum, arith.mk_int(1))
                              : arith.mk_int(1);
                }
                continue;
            }
            // Case 2: power token whose base matches our base pattern (at pos == 0)
            if (pos == 0 && t->is_power()) {
                euf::snode* pow_base = t->arg(0);
                if (pow_base) {
                    euf::snode_vector pb_tokens;
                    collect_tokens_dir(pow_base, fwd, pb_tokens);
                    if (pb_tokens.size() == base_tokens.size()) {
                        bool match = true;
                        for (unsigned j = 0; j < pb_tokens.size() && match; j++)
                            match = (pb_tokens[j] == base_tokens[j]);
                        if (match) {
                            expr* pow_exp = get_power_exp_expr(t, seq);
                            if (pow_exp) {
                                sum = sum ? arith.mk_add(sum, pow_exp) : pow_exp;
                                continue;
                            }
                        }
                    }
                }
            }
            break;
        }
        // After loop: i = break index or side_tokens.size()
        if (pos == 0) {
            last_stable_idx = i;
            last_stable_sum = sum;
        }
        return {expr_ref(last_stable_sum, m), last_stable_idx};
    }

    simplify_result nielsen_node::simplify_and_init(svector<nielsen_edge*> const& cur_path) {
        if (m_is_extended)
            return simplify_result::proceed;

        euf::sgraph& sg = m_graph.sg();
        ast_manager& m = sg.get_manager();
        arith_util arith(m);
        seq_util& seq = this->graph().seq();
        bool changed = true;

        while (changed) {
            changed = false;

            // pass 1: remove trivially satisfied equalities and memberships
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

            unsigned wj = 0;
            for (unsigned j = 0; j < m_str_mem.size(); ++j) {
                str_mem& mem = m_str_mem[j];
                if (mem.is_trivial())
                    continue;
                m_str_mem[wj++] = mem;
            }
            if (wj < m_str_mem.size()) {
                m_str_mem.shrink(wj);
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
                        if ((lt->is_char() || lt->is_var()) && m.are_equal(lt->get_expr(), rt->get_expr())) {
                            ++prefix;
                        }
                        else if (lt->is_char() && rt->is_char() && m.are_distinct(lt->get_expr(), rt->get_expr())) {
                            m_is_general_conflict = true;
                            m_reason = backtrack_reason::symbol_clash;
                            return simplify_result::conflict;
                        }
                        else
                            break;
                    }

                    // --- suffix (only among the tokens not already consumed by prefix) ---
                    unsigned lsz = lhs_toks.size(), rsz = rhs_toks.size();
                    unsigned suffix = 0;
                    while (suffix < lsz - prefix && suffix < rsz - prefix) {
                        euf::snode* lt = lhs_toks[lsz - 1 - suffix];
                        euf::snode* rt = rhs_toks[rsz - 1 - suffix];
                        if ((lt->is_char() || lt->is_var()) && m.are_equal(lt->get_expr(), rt->get_expr())) {
                            ++suffix;
                        } else if (lt->is_char() && rt->is_char() && m.are_distinct(lt->get_expr(), rt->get_expr())) {
                            m_is_general_conflict = true;
                            m_reason = backtrack_reason::symbol_clash;
                            return simplify_result::conflict;
                        }
                        else
                            break;
                    }

                    if (prefix > 0 || suffix > 0) {
                        eq.m_lhs = sg.drop_left(sg.drop_right(eq.m_lhs, suffix), prefix);
                        eq.m_rhs = sg.drop_left(sg.drop_right(eq.m_rhs, suffix), prefix);
                        changed = true;
                    }
                }

                // pass 2b: power-character directional inconsistency
                // (mirrors ZIPT's SimplifyDir power unit case + IsPrefixConsistent)
                // For each direction (left-to-right and right-to-left):
                // when one side starts (in that direction) with a power u^n whose
                // base starts (in that direction) with char a, and the other side
                // starts with a different char b, then exponent n must be 0.
                // Creates a single deterministic child with the substitution and
                // constraint as edge labels so they appear in the graph.
                // Guard: skip if we already created a child (re-entry via iterative deepening).

                // Spec: DirectionalInconsistency.
                //   For direction d ∈ {left, right}, let first_d(u) denote the first token of u
                //   in direction d.
                //   If pow_side[d] = u^p  and  other_side[d] = c  (a concrete character),
                //   and first_d(base(u)) = c'  with  c' ≠ c,
                //   then p = 0  (the power is vacuous in direction d).
                //   Action: create a deterministic child with substitution u^p → ε and
                //   int constraint p = 0.
                if (!eq.is_trivial() && eq.m_lhs && eq.m_rhs) {
                    for (unsigned od = 0; od < 2; ++od) {
                        bool fwd = (od == 0);
                        euf::snode* lh = dir_token(eq.m_lhs, fwd);
                        euf::snode* rh = dir_token(eq.m_rhs, fwd);
                        for (int side = 0; side < 2; ++side) {
                            euf::snode* pow_head = (side == 0) ? lh : rh;
                            euf::snode* other_head = (side == 0) ? rh : lh;
                            if (!pow_head || !pow_head->is_power() || !other_head || !other_head->is_char())
                                continue;
                            euf::snode* base_sn = pow_head->arg(0);
                            if (!base_sn) continue;
                            euf::snode* base_head = dir_token(base_sn, fwd);
                            if (!base_head || !base_head->is_char()) continue;
                            if (m.are_equal(base_head->get_expr(), other_head->get_expr())) continue;
                            // Directional base/head mismatch -> force exponent 0 and power -> ε.
                            nielsen_node* child = m_graph.mk_child(this);
                            nielsen_edge* e = m_graph.mk_edge(this, child, true);
                            nielsen_subst s(pow_head, sg.mk_empty_seq(pow_head->get_sort()), eq.m_dep);
                            e->add_subst(s);
                            child->apply_subst(sg, s);
                            expr* pow_exp = get_power_exp_expr(pow_head, seq);
                            if (pow_exp) {
                                expr* zero = arith.mk_numeral(rational(0), true);
                                e->add_side_int(m_graph.mk_int_constraint(
                                    pow_exp, zero, int_constraint_kind::eq, eq.m_dep));
                            }
                            set_extended(true);
                            return simplify_result::proceed;
                        }
                    }
                }
            }

            // pass 3: power simplification (mirrors ZIPT's LcpCompression +
            // SimplifyPowerElim + SimplifyPowerSingle)
            for (str_eq& eq : m_str_eq) {
                if (eq.is_trivial() || !eq.m_lhs || !eq.m_rhs)
                    continue;

                // 3a: simplify constant-exponent powers (base^0 → ε, base^1 → base)
                if (euf::snode* s = simplify_const_powers(sg, eq.m_lhs))
                    { eq.m_lhs = s; changed = true; }
                if (euf::snode* s = simplify_const_powers(sg, eq.m_rhs))
                    { eq.m_rhs = s; changed = true; }

                // 3b: merge adjacent same-base tokens into combined powers
                if (euf::snode* s = merge_adjacent_powers(sg, eq.m_lhs))
                    { eq.m_lhs = s; changed = true; }
                if (euf::snode* s = merge_adjacent_powers(sg, eq.m_rhs))
                    { eq.m_rhs = s; changed = true; }

                // 3c: CommPower-based power elimination — when one side starts
                // with a power w^p, count base-pattern occurrences c on the
                // other side's prefix.  If we can determine the ordering between
                // p and c, cancel the matched portion.  Mirrors ZIPT's
                // SimplifyPowerElim calling CommPower.
                // Spec: CommPower cancellation.
                //   Given: pow_side = w^p · rest_pow  and  other_side = w^c · rest_other
                //   where c is the number of times the base pattern w occurs in the
                //   directional prefix of other_side.
                //   - If p ≤ c: pow_side := rest_pow,            other_side := w^(c-p) · rest_other
                //   - If c ≤ p: pow_side := w^(p-c) · rest_pow,  other_side := rest_other
                //   - If p = c: both reduce completely (handled by both conditions above).
                SASSERT(eq.m_lhs && eq.m_rhs);
                bool comm_changed = false;
                for (int side = 0; side < 2 && !comm_changed; ++side) {
                    euf::snode*& pow_side = side == 0 ? eq.m_lhs : eq.m_rhs;
                    euf::snode*& other_side = side == 0 ? eq.m_rhs : eq.m_lhs;
                    if (!pow_side || !other_side)
                        continue;
                    for (unsigned od = 0; od < 2 && !comm_changed; ++od) {
                        bool fwd = od == 0;
                        euf::snode* end_tok = dir_token(pow_side, fwd);
                        if (!end_tok || !end_tok->is_power())
                            continue;
                        euf::snode* base_sn = end_tok->arg(0);
                        expr* pow_exp = get_power_exp_expr(end_tok, seq);
                        if (!base_sn || !pow_exp)
                            continue;

                        auto [count, consumed] =
                            comm_power(base_sn, other_side, m, seq, fwd);
                        if (!count.get() || consumed == 0)
                            continue;

                        expr_ref norm_count = normalize_arith(m, count);
                        bool pow_le_count = false, count_le_pow = false;
                        rational diff;
                        if (get_const_power_diff(norm_count, pow_exp, arith, diff)) {
                            count_le_pow = diff.is_nonpos();
                            pow_le_count = diff.is_nonneg();
                        }
                        else if (!cur_path.empty()) {
                            pow_le_count = m_graph.check_lp_le(pow_exp, norm_count, this, cur_path);
                            count_le_pow = m_graph.check_lp_le(norm_count, pow_exp, this, cur_path);
                        }
                        if (!pow_le_count && !count_le_pow)
                            continue;

                        pow_side = dir_drop(sg, pow_side, 1, fwd);
                        other_side = dir_drop(sg, other_side, consumed, fwd);
                        expr* base_e = get_power_base_expr(end_tok, seq);
                        if (pow_le_count && count_le_pow) {
                            // equal: both cancel completely
                        }
                        else if (pow_le_count) {
                            // pow <= count: remainder goes to other_side
                            expr_ref rem = normalize_arith(m, arith.mk_sub(norm_count, pow_exp));
                            expr_ref pw(seq.str.mk_power(base_e, rem), m);
                            other_side = dir_concat(sg, sg.mk(pw), other_side, fwd);
                        }
                        else {
                            // count <= pow: remainder goes to pow_side
                            expr_ref rem = normalize_arith(m, arith.mk_sub(pow_exp, norm_count));
                            expr_ref pw(seq.str.mk_power(base_e, rem), m);
                            pow_side = dir_concat(sg, sg.mk(pw), pow_side, fwd);
                        }
                        comm_changed = true;
                    }
                }
                if (comm_changed)
                    changed = true;

                // After any change in passes 3a–3c, restart the while loop
                // before running 3d/3e.  This lets 3a simplify new constant-
                // exponent powers (e.g. base^1 → base created by 3c) before
                // 3e attempts LP-based elimination which would introduce a
                // needless fresh variable.
                if (changed)
                    continue;

                // 3d: power prefix elimination — when both sides start with a
                // power of the same base, cancel the common power prefix.
                // (Subsumed by 3c for many cases, but handles same-base-power
                // pairs that CommPower may miss when both leading tokens are powers.)
                SASSERT(eq.m_lhs && eq.m_rhs);
                for (unsigned od = 0; od < 2 && !changed; ++od) {
                    bool fwd = (od == 0);
                    euf::snode* lh = dir_token(eq.m_lhs, fwd);
                    euf::snode* rh = dir_token(eq.m_rhs, fwd);
                    if (!(lh && rh && lh->is_power() && rh->is_power()))
                        continue;
                    expr* lb = get_power_base_expr(lh, seq);
                    expr* rb = get_power_base_expr(rh, seq);
                    if (!(lb && rb && lb == rb))
                        continue;
                    expr* lp = get_power_exp_expr(lh, seq);
                    expr* rp = get_power_exp_expr(rh, seq);
                    rational diff;
                    if (lp && rp && get_const_power_diff(rp, lp, arith, diff)) {
                        // rp = lp + diff (constant difference)
                        eq.m_lhs = dir_drop(sg, eq.m_lhs, 1, fwd);
                        eq.m_rhs = dir_drop(sg, eq.m_rhs, 1, fwd);
                        if (diff.is_pos()) {
                            // rp > lp: put base^diff on RHS (direction-aware prepend/append)
                            expr_ref de(arith.mk_int(diff), m);
                            expr_ref pw(seq.str.mk_power(lb, de), m);
                            eq.m_rhs = dir_concat(sg, sg.mk(pw), eq.m_rhs, fwd);
                        }
                        else if (diff.is_neg()) {
                            // lp > rp: put base^(-diff) on LHS
                            expr_ref de(arith.mk_int(-diff), m);
                            expr_ref pw(seq.str.mk_power(lb, de), m);
                            eq.m_lhs = dir_concat(sg, sg.mk(pw), eq.m_lhs, fwd);
                        }
                        // diff == 0: both powers cancel completely
                        changed = true;
                    }
                    // 3e: LP-aware power directional elimination
                    else if (lp && rp && !cur_path.empty()) {
                        bool lp_le_rp = m_graph.check_lp_le(lp, rp, this, cur_path);
                        bool rp_le_lp = m_graph.check_lp_le(rp, lp, this, cur_path);
                        if (lp_le_rp || rp_le_lp) {
                            expr* smaller_exp = lp_le_rp ? lp : rp;
                            expr* larger_exp  = lp_le_rp ? rp : lp;
                            eq.m_lhs = dir_drop(sg, eq.m_lhs, 1, fwd);
                            eq.m_rhs = dir_drop(sg, eq.m_rhs, 1, fwd);
                            if (lp_le_rp && rp_le_lp) {
                                // both ≤ -> equal -> both cancel completely
                                add_int_constraint(m_graph.mk_int_constraint(lp, rp, int_constraint_kind::eq, eq.m_dep));
                            }
                            else {
                                // strictly less: create diff power d = larger - smaller >= 1
                                expr_ref d(m_graph.mk_fresh_int_var());
                                expr_ref one_e(arith.mk_int(1), m);
                                expr_ref d_plus_smaller(arith.mk_add(d, smaller_exp), m);
                                add_int_constraint(m_graph.mk_int_constraint(d, one_e, int_constraint_kind::ge, eq.m_dep));
                                add_int_constraint(m_graph.mk_int_constraint(d_plus_smaller, larger_exp, int_constraint_kind::eq, eq.m_dep));
                                expr_ref pw(seq.str.mk_power(lb, d), m);
                                euf::snode*& larger_side = lp_le_rp ? eq.m_rhs : eq.m_lhs;
                                larger_side = dir_concat(sg, sg.mk(pw), larger_side, fwd);
                            }
                            changed = true;
                        }
                    }
                }
            }
        }

        // consume concrete characters from str_mem via Brzozowski derivatives
        // in both directions (left-to-right, then right-to-left), mirroring ZIPT.
        for (str_mem& mem : m_str_mem) {
            SASSERT(mem.m_str && mem.m_regex);
            if (mem.is_primitive())
                continue;
            for (unsigned od = 0; od < 2; ++od) {
                bool fwd = od == 0;
                while (!mem.m_str->is_empty()) {
                    euf::snode* tok = dir_token(mem.m_str, fwd);
                    if (!tok || !tok->is_char())
                        break;
                    euf::snode* deriv = fwd
                        ? sg.brzozowski_deriv(mem.m_regex, tok)
                        : reverse_brzozowski_deriv(sg, mem.m_regex, tok);
                    if (!deriv)
                        break;
                    if (deriv->is_fail()) {
                        m_is_general_conflict = true;
                        m_reason = backtrack_reason::regex;
                        return simplify_result::conflict;
                    }
                    mem.m_str = dir_drop(sg, mem.m_str, 1, fwd);
                    mem.m_regex = deriv;
                    // ZIPT tracks history only in forward direction.
                    if (fwd)
                        mem.m_history = sg.mk_concat(mem.m_history, tok);
                }
            }
        }

        // consume symbolic characters (s_unit tokens) via uniform derivative
        // check.  When all minterms of the regex produce the same Brzozowski
        // derivative, the derivative is independent of the character value
        // and we can deterministically consume the token.  Forward direction
        // only (matches ZIPT history tracking convention).
        //
        // Extended: when uniform derivative fails but the token has a char_range
        // constraint (from apply_regex_var_split), check if the char_range is a
        // subset of a single minterm's character class.  If so, the derivative
        // is deterministic for that token.
        // Mirrors ZIPT StrMem.SimplifyCharRegex lines 96-117.
        for (str_mem& mem : m_str_mem) {
            SASSERT(mem.m_str && mem.m_regex);
            if (mem.is_primitive())
                continue;
            while (mem.m_str && !mem.m_str->is_empty()) {
                euf::snode* tok = mem.m_str->first();
                if (!tok || !tok->is_unit())
                    break;
                // compute minterms and check for uniform derivative
                euf::snode_vector minterms;
                sg.compute_minterms(mem.m_regex, minterms);
                VERIFY(!minterms.empty());
                euf::snode* uniform = nullptr;
                bool is_uniform = true;
                for (euf::snode* mt : minterms) {
                    if (!mt || mt->is_fail())
                        continue;
                    euf::snode* deriv = sg.brzozowski_deriv(mem.m_regex, mt);
                    if (!deriv) {
                        is_uniform = false;
                        break;
                    }
                    if (!uniform)
                        uniform = deriv;
                    else if (uniform->id() != deriv->id()) {
                        is_uniform = false;
                        break;
                    }
                }
                if (is_uniform && uniform) {
                    if (uniform->is_fail()) {
                        m_is_general_conflict = true;
                        m_reason = backtrack_reason::regex;
                        return simplify_result::conflict;
                    }
                    mem.m_str = sg.drop_left(mem.m_str, 1);
                    mem.m_regex = uniform;
                    mem.m_history = sg.mk_concat(mem.m_history, tok);
                    continue;
                }
                // Uniform derivative failed — try char_range subset approach.
                // If the symbolic char has a char_range constraint and that
                // range is a subset of exactly one minterm's character class,
                // we can deterministically take that minterm's derivative.
                if (m_char_ranges.contains(tok->id()) && m_graph.m_parikh) {
                    char_set const& cs = m_char_ranges[tok->id()];
                    if (!cs.is_empty()) {
                        euf::snode* matching_deriv = nullptr;
                        bool found = false;
                        for (euf::snode* mt : minterms) {
                            if (!mt || mt->is_fail()) continue;
                            if (!mt->get_expr()) continue;
                            char_set mt_cs = m_graph.m_seq_regex->minterm_to_char_set(mt->get_expr());
                            if (cs.is_subset(mt_cs)) {
                                euf::snode* deriv = sg.brzozowski_deriv(mem.m_regex, mt);
                                if (!deriv) { found = false; break; }
                                if (deriv->is_fail()) {
                                    m_is_general_conflict = true;
                                    m_reason = backtrack_reason::regex;
                                    return simplify_result::conflict;
                                }
                                matching_deriv = deriv;
                                found = true;
                                break;
                            }
                        }
                        if (found && matching_deriv) {
                            mem.m_str = sg.drop_left(mem.m_str, 1);
                            mem.m_regex = matching_deriv;
                            mem.m_history = sg.mk_concat(mem.m_history, tok);
                            continue;
                        }
                    }
                }
                break;
            }
        }

        // check for regex memberships that are immediately infeasible
        for (str_mem& mem : m_str_mem) {
            SASSERT(mem.m_str && mem.m_regex);
            if (mem.m_str->is_empty() && !mem.m_regex->is_nullable()) {
                m_is_general_conflict = true;
                m_reason = backtrack_reason::regex;
                return simplify_result::conflict;
            }
        }

        // Regex widening: for each remaining str_mem, overapproximate
        // the string by replacing variables with their regex intersection
        // and check if the result intersected with the target regex is empty.
        // Detects infeasible constraints that would otherwise require
        // expensive exploration. Mirrors ZIPT NielsenNode.CheckRegexWidening.
        SASSERT(m_graph.m_seq_regex);
        for (str_mem const& mem : m_str_mem) {
            SASSERT(mem.m_str && mem.m_regex);
            if (mem.is_primitive())
                continue;
            if (m_graph.check_regex_widening(*this, mem.m_str, mem.m_regex)) {
                std::cout << "Widening conflict: " << mk_pp(mem.m_str->get_expr(), m) << " ∉ " << mk_pp(mem.m_regex->get_expr(), m) << std::endl;
                m_is_general_conflict = true;
                m_reason = backtrack_reason::regex;
                return simplify_result::conflict;
            }
        }

        // IntBounds initialization: derive per-variable Parikh length bounds from
        // remaining regex memberships and add to m_int_constraints.
        init_var_bounds_from_mems();

        // pass 5: variable-character look-ahead substitution
        // (mirrors ZIPT's StrEq.SimplifyFinal)
        // When one side starts (in a direction) with variable x and the other
        // with chars, look ahead to find how many chars can be deterministically
        // assigned to x without splitting, by checking directional consistency.
        // Guard: skip if we already created a child (re-entry via iterative deepening).
        for (str_eq& eq : m_str_eq) {
            SASSERT(eq.m_lhs && eq.m_rhs);
            if (eq.is_trivial())
                continue;
            for (unsigned od = 0; od < 2; ++od) {
                bool fwd = od == 0;

                // Orient: var_side starts with a variable, char_side with a char
                euf::snode* var_side = nullptr;
                euf::snode* char_side = nullptr;
                euf::snode* lhead = dir_token(eq.m_lhs, fwd);
                euf::snode* rhead = dir_token(eq.m_rhs, fwd);
                if (!lhead || !rhead) continue;

                if (lhead->is_var() && rhead->is_char()) {
                    var_side = eq.m_lhs;
                    char_side = eq.m_rhs;
                }
                else if (rhead->is_var() && lhead->is_char()) {
                    var_side = eq.m_rhs;
                    char_side = eq.m_lhs;
                }
                else
                    continue;

                euf::snode_vector var_toks, char_toks;
                collect_tokens_dir(var_side, fwd, var_toks);
                collect_tokens_dir(char_side, fwd, char_toks);
                if (var_toks.size() <= 1 || char_toks.empty())
                    continue;

                euf::snode* var_node = var_toks[0];
                SASSERT(var_node->is_var());

                // For increasing directional prefix lengths i (chars from char_side),
                // check if x -> chars[0..i-1] · x (or x · chars[...] in backward mode)
                // is consistent.
                unsigned i = 0;
                for (; i < char_toks.size() && char_toks[i]->is_char(); ++i) {
                    unsigned j1 = 1;   // index into var_toks (after the variable)
                    unsigned j2 = i;   // index into char_toks (after copied prefix)
                    bool failed = false;

                    while (j1 < var_toks.size() && j2 < char_toks.size()) {
                        euf::snode* st1 = var_toks[j1];
                        euf::snode* st2 = char_toks[j2];

                        if (!st2->is_char())
                            break;  // cannot compare against non-char -> indeterminate

                        if (st1->is_char()) {
                            if (st1->id() == st2->id()) {
                                j1++;
                                j2++;
                                continue;
                            }
                            failed = true;
                            break;
                        }

                        if (st1->id() != var_node->id())
                            break;  // different variable/power -> indeterminate

                        // st1 is the same variable x again — compare against chars copied so far
                        bool inner_indet = false;
                        for (unsigned l = 0; j2 < char_toks.size() && l < i; ++l) {
                            st2 = char_toks[j2];
                            if (!st2->is_char()) {
                                inner_indet = true;
                                break;
                            }
                            if (st2->id() == char_toks[l]->id()) {
                                j2++;
                                continue;
                            }
                            failed = true;
                            break;
                        }
                        if (inner_indet || failed)
                            break;
                        j1++;
                    }

                    if (failed)
                        continue;  // prefix i inconsistent -> try longer
                    break;         // prefix i consistent/indeterminate -> stop
                }

                if (i == 0)
                    continue;

                // Divergence guard (mirrors ZIPT's HasDepCycle + power skip).
                bool skip_dir = false;
                euf::snode* next_var = nullptr;
                for (unsigned k = i; k < char_toks.size(); ++k) {
                    euf::snode* t = char_toks[k];
                    if (t->is_power()) {
                        skip_dir = true; // could diverge via repeated power unwinding
                        break;
                    }
                    if (t->is_var()) {
                        next_var = t;
                        break;
                    }
                }
                if (skip_dir)
                    continue;

                // If there is a variable after the copied chars, reject substitutions
                // that create a directional Nielsen dependency cycle.
                if (next_var) {
                    u_map<unsigned> dep_edges;  // var id -> first dependent var id
                    for (str_eq const& other_eq : m_str_eq) {
                        if (other_eq.is_trivial())
                            continue;
                        if (!other_eq.m_lhs || !other_eq.m_rhs)
                            continue;

                        euf::snode* lh2 = dir_token(other_eq.m_lhs, fwd);
                        euf::snode* rh2 = dir_token(other_eq.m_rhs, fwd);
                        if (!lh2 || !rh2)
                            continue;

                        auto record_dep = [&](euf::snode* head_var, euf::snode* other_side) {
                            euf::snode_vector other_toks;
                            collect_tokens_dir(other_side, fwd, other_toks);
                            for (unsigned idx = 0; idx < other_toks.size(); ++idx) {
                                if (other_toks[idx]->is_var()) {
                                    if (!dep_edges.contains(head_var->id()))
                                        dep_edges.insert(head_var->id(), other_toks[idx]->id());
                                    return;
                                }
                            }
                        };

                        if (lh2->is_var() && rh2->is_var()) {
                            if (!dep_edges.contains(lh2->id()))
                                dep_edges.insert(lh2->id(), rh2->id());
                            if (!dep_edges.contains(rh2->id()))
                                dep_edges.insert(rh2->id(), lh2->id());
                        }
                        else if (lh2->is_var() && !rh2->is_var())
                            record_dep(lh2, other_eq.m_rhs);
                        else if (rh2->is_var() && !lh2->is_var())
                            record_dep(rh2, other_eq.m_lhs);
                    }

                    // DFS from next_var to see if we can reach var_node
                    uint_set visited;
                    svector<unsigned> worklist;
                    worklist.push_back(next_var->id());
                    bool cycle_found = false;
                    while (!worklist.empty() && !cycle_found) {
                        unsigned cur = worklist.back();
                        worklist.pop_back();
                        if (cur == var_node->id()) {
                            cycle_found = true;
                            break;
                        }
                        if (visited.contains(cur))
                            continue;
                        visited.insert(cur);
                        unsigned dep_id;
                        if (dep_edges.find(cur, dep_id))
                            worklist.push_back(dep_id);
                    }
                    if (cycle_found)
                        continue;
                }

                // Create a single deterministic child with directional substitution.
                euf::snode* prefix_sn = char_toks[0];
                for (unsigned j = 1; j < i; ++j) {
                    prefix_sn = dir_concat(sg, prefix_sn, char_toks[j], fwd);
                }
                euf::snode* replacement = dir_concat(sg, prefix_sn, var_node, fwd);
                nielsen_subst s(var_node, replacement, eq.m_dep);
                nielsen_node* child = m_graph.mk_child(this);
                nielsen_edge* e = m_graph.mk_edge(this, child, true);
                e->add_subst(s);
                child->apply_subst(sg, s);
                set_extended(true);
                return simplify_result::proceed;
            }
        }

        if (is_satisfied())
            return simplify_result::satisfied;
        return simplify_result::proceed;
    }

    bool nielsen_node::is_satisfied() const {
        for (str_eq const& eq : m_str_eq) {
            if (!eq.is_trivial())
                return false;
        }
        for (str_mem const& mem : m_str_mem) {
            if (!mem.is_trivial() && !mem.is_primitive())
                return false;
        }
        return true;
    }

    bool nielsen_node::has_opaque_terms() const {
        auto is_opaque = [](euf::snode* n) { return n && n->kind() == euf::snode_kind::s_other; };
        for (str_eq const& eq : m_str_eq) {
            if (eq.is_trivial())
                continue;
            if (is_opaque(eq.m_lhs) || is_opaque(eq.m_rhs))
                return true;
            euf::snode_vector toks;
            if (eq.m_lhs) {
                eq.m_lhs->collect_tokens(toks);
                for (auto* t : toks) {
                    if (is_opaque(t))
                        return true;
                }
                toks.reset();
            }
            if (eq.m_rhs) {
                eq.m_rhs->collect_tokens(toks);
                for (auto* t : toks) {
                    if (is_opaque(t))
                        return true;
                }
            }
        }
        for (str_mem const& mem : m_str_mem) {
            if (!mem.m_str)
                continue;
            if (is_opaque(mem.m_str))
                return true;
            euf::snode_vector toks;
            mem.m_str->collect_tokens(toks);
            for (auto* t : toks) {
                if (is_opaque(t))
                    return true;
            }
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // nielsen_graph: search
    // -----------------------------------------------------------------------

    void nielsen_graph::apply_parikh_to_node(nielsen_node& node) {
        if (!m_parikh_enabled || node.m_parikh_applied)
            return;
        node.m_parikh_applied = true;

        // Generate modular length constraints (len(str) = min_len + stride·k, etc.)
        // and append them to the node's integer constraint list.
        m_parikh->apply_to_node(node);

        // Lightweight feasibility pre-check: does the Parikh modular constraint
        // contradict the variable's current integer bounds?  If so, mark this
        // node as a Parikh-image conflict immediately (avoids a solver call).
        if (!node.is_currently_conflict() && m_parikh->check_parikh_conflict(node)) {
            node.set_general_conflict(true);
            node.set_reason(backtrack_reason::parikh_image);
        }
    }

    void nielsen_graph::assert_root_constraints_to_solver() {
        if (m_root_constraints_asserted)
            return;
        m_root_constraints_asserted = true;
        // Constraint.Shared: assert all root-level length/Parikh constraints
        // to m_solver at the base level (no push/pop). These include:
        //   - len(lhs) = len(rhs) for each non-trivial string equality
        //   - len(str) >= min_len and len(str) <= max_len for each regex membership
        //   - len(x) >= 0 for each variable appearing in the root constraints
        // Making these visible to the solver before the DFS allows arithmetic
        // pruning at every node, not just the root.
        vector<length_constraint> constraints;
        generate_length_constraints(constraints);
        for (auto const& lc : constraints) {
            m_solver.assert_expr(lc.m_expr);
        }
    }

    nielsen_graph::search_result nielsen_graph::solve() {
        if (!m_root)
            return search_result::sat;

        try {
            ++m_stats.m_num_solve_calls;
            m_sat_node = nullptr;
            m_sat_path.reset();

            // Constraint.Shared: assert root-level length/Parikh constraints to the
            // solver at the base level, so they are visible during all feasibility checks.
            assert_root_constraints_to_solver();

            // Iterative deepening: increment by 1 on each failure.
            // m_max_search_depth == 0 means unlimited; otherwise stop when bound exceeds it.
            m_depth_bound = 3;
            while (true) {
                if (!m.inc()) {
#ifdef Z3DEBUG
                    // Examining the Nielsen graph is probably the best way of debugging
                    std::string dot = to_dot();
                    IF_VERBOSE(1, verbose_stream() << dot << "\n";);
#endif
                    break;
                }
                if (m_max_search_depth > 0 && m_depth_bound > m_max_search_depth)
                    break;
                inc_run_idx();
                svector<nielsen_edge *> cur_path;
                search_result r = search_dfs(m_root, 0, cur_path);
                IF_VERBOSE(1, verbose_stream()
                                  << " depth_bound=" << m_depth_bound << " dfs_nodes=" << m_stats.m_num_dfs_nodes
                                  << " max_depth=" << m_stats.m_max_depth << " extensions=" << m_stats.m_num_extensions
                                  << " arith_prune=" << m_stats.m_num_arith_infeasible << " result="
                                  << (r == search_result::sat     ? "SAT"
                                      : r == search_result::unsat ? "UNSAT"
                                                                  : "UNKNOWN")
                                  << "\n";);
                if (r == search_result::sat) {
                    ++m_stats.m_num_sat;
                    return r;
                }
                if (r == search_result::unsat) {
                    ++m_stats.m_num_unsat;
                    return r;
                }
                // depth limit hit – double the bound and retry
                m_depth_bound *= 2;
            }
            ++m_stats.m_num_unknown;
            return search_result::unknown;
        }
        catch(const std::exception&) {
#ifdef Z3DEBUG
            std::string dot = to_dot();
#endif
            throw;
        }
    }

    nielsen_graph::search_result nielsen_graph::search_dfs(nielsen_node* node, unsigned depth, svector<nielsen_edge*>& cur_path) {
        ++m_stats.m_num_dfs_nodes;
        m_stats.m_max_depth = std::max(m_stats.m_max_depth, depth);

        // check for external cancellation (timeout, user interrupt)
        if (!m.inc())
            return search_result::unknown;

        // check DFS node budget (0 = unlimited)
        if (m_max_nodes > 0 && m_stats.m_num_dfs_nodes > m_max_nodes)
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
        simplify_result sr = node->simplify_and_init(cur_path);

        if (sr == simplify_result::conflict) {
            ++m_stats.m_num_simplify_conflict;
            node->set_general_conflict(true);
            return search_result::unsat;
        }

        // Apply Parikh image filter: generate modular length constraints and
        // perform a lightweight feasibility pre-check.  The filter is guarded
        // internally (m_parikh_applied) so it only runs once per node.
        // Note: Parikh filtering is skipped for satisfied nodes (returned above);
        // a fully satisfied node has no remaining memberships to filter.
        apply_parikh_to_node(*node);
        if (node->is_currently_conflict()) {
            ++m_stats.m_num_simplify_conflict;
            return search_result::unsat;
        }

        // Assert any new int_constraints added during simplify_and_init for this
        // node into the current solver scope. Constraints inherited from the parent
        // (indices 0..m_parent_ic_count-1) are already present at the enclosing
        // scope level; only the newly-added tail needs to be asserted here.
        // Also generate per-node |LHS| = |RHS| length constraints for descendant
        // equations (root constraints are already at the base level).
        generate_node_length_constraints(node);
        assert_node_new_int_constraints(node);

        // integer feasibility check: the solver now holds all path constraints
        // incrementally; just query the solver directly
        if (!cur_path.empty() && !check_int_feasibility(node, cur_path)) {
            node->set_reason(backtrack_reason::arithmetic);
            ++m_stats.m_num_arith_infeasible;
            return search_result::unsat;
        }

        if (sr == simplify_result::satisfied || node->is_satisfied()) {
            // Before declaring SAT, check leaf-node regex feasibility:
            // for each variable with multiple regex constraints, verify
            // that the intersection of all its regexes is non-empty.
            // Mirrors ZIPT NielsenNode.CheckRegex.
            if (!check_leaf_regex(*node)) {
                node->set_general_conflict(true);
                node->set_reason(backtrack_reason::regex);
                return search_result::unsat;
            }
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
        for (nielsen_edge *e : node->outgoing()) {
            cur_path.push_back(e);
            // Push a solver scope for this edge and assert its side integer
            // constraints.  The child's own new int_constraints will be asserted
            // inside the recursive call (above).  On return, pop the scope so
            // that backtracking removes those assertions.
            m_solver.push();

            // Lazily compute substitution length constraints (|x| = |u|) on first
            // traversal. This must happen before asserting side_int and before
            // bumping mod counts, so that LHS uses the parent's counts and RHS
            // uses the temporarily-bumped counts.
            if (!e->len_constraints_computed()) {
                add_subst_length_constraints(e);
                e->set_len_constraints_computed(true);
            }

            for (auto const &ic : e->side_int()) {
                m_solver.assert_expr(int_constraint_to_expr(ic));
            }

            // Bump modification counts for the child's context.
            inc_edge_mod_counts(e);

            search_result r = search_dfs(e->tgt(), e->is_progress() ? depth : depth + 1, cur_path);

            // Restore modification counts on backtrack.
            dec_edge_mod_counts(e);

            m_solver.pop(1);
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
            for (unsigned od = 0; od < 2; ++od) {
                bool fwd = (od == 0);
                euf::snode* lhead = dir_token(eq.m_lhs, fwd);
                euf::snode* rhead = dir_token(eq.m_rhs, fwd);
                if (!lhead || !rhead)
                    continue;

                // char vs var: branch 1: var -> ε, branch 2: var -> char·var   (depending on direction)
                // NSB review: add also case var -> unit·var
                euf::snode* char_head = lhead->is_char() ? lhead : (rhead->is_char() ? rhead : nullptr);
                euf::snode* var_head = lhead->is_var() ? lhead : (rhead->is_var() ? rhead : nullptr);
                if (char_head && var_head) {
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, true);
                    nielsen_subst s1(var_head, m_sg.mk_empty_seq(var_head->get_sort()), eq.m_dep);
                    e->add_subst(s1);
                    child->apply_subst(m_sg, s1);

                    euf::snode* replacement = dir_concat(m_sg, char_head, var_head, fwd);
                    child = mk_child(node);
                    e = mk_edge(node, child, false);
                    nielsen_subst s2(var_head, replacement, eq.m_dep);
                    e->add_subst(s2);
                    child->apply_subst(m_sg, s2);
                    return true;
                }
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
            for (unsigned od = 0; od < 2; ++od) {
                bool fwd = od == 0;
                euf::snode* lhead = dir_token(eq.m_lhs, fwd);
                euf::snode* rhead = dir_token(eq.m_rhs, fwd);
                if (!lhead || !rhead)
                    continue;
                if (!lhead->is_var() || !rhead->is_var())
                    continue;
                if (lhead->id() == rhead->id())
                    continue;

                // x·A = y·B where x,y are distinct variables (classic Nielsen)
                // child 1: x → ε (progress)
                {
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, true);
                    nielsen_subst s(lhead, m_sg.mk_empty_seq(lhead->get_sort()), eq.m_dep);
                    e->add_subst(s);
                    child->apply_subst(m_sg, s);
                }
                // child 2: y → ε (progress)
                {
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, true);
                    nielsen_subst s(rhead, m_sg.mk_empty_seq(rhead->get_sort()), eq.m_dep);
                    e->add_subst(s);
                    child->apply_subst(m_sg, s);
                }
                // child 3: x → y·x (no progress)
                {
                    euf::snode* replacement = dir_concat(m_sg, rhead, lhead, fwd);
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, false);
                    nielsen_subst s(lhead, replacement, eq.m_dep);
                    e->add_subst(s);
                    child->apply_subst(m_sg, s);
                }
                // child 4: y → x·y (no progress)
                {
                    euf::snode* replacement = dir_concat(m_sg, lhead, rhead, fwd);
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, false);
                    nielsen_subst s(rhead, replacement, eq.m_dep);
                    e->add_subst(s);
                    child->apply_subst(m_sg, s);
                }
                return true;
            }
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
                }
                else
                    const_diff += (int)token_const_length(tok);
            }
            else {
                if (ri >= rhs_len)
                    break;
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
                }
                else
                    const_diff -= (int)token_const_length(tok);
            }
        }

        if (!has_best)
            return false;

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
                pad = mk_fresh_var(eq.m_lhs->get_sort());
                if (padding > 0) {
                    // LHS prefix is longer by |padding| constants.
                    // Prepend pad to RHS prefix, append pad to LHS suffix.
                    eq1_rhs = m_sg.mk_concat(pad, rhs_prefix);
                    eq2_lhs = m_sg.mk_concat(lhs_suffix, pad);
                }
                else {
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

    euf::snode* nielsen_graph::mk_fresh_var(sort* s) {
        ++m_stats.m_num_fresh_vars;
        std::string name = "v!" + std::to_string(m_fresh_cnt++);
        return m_sg.mk_var(symbol(name.c_str()), s);
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

        // Priority 3b: SplitPowerElim - CommPower-based branching when
        // one side has a power and the other side has same-base occurrences
        // but ordering is unknown.
        if (apply_split_power_elim(node))
            return ++m_stats.m_mod_split_power_elim, true;

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
            if (eq.is_trivial())
                continue;
            if (!eq.m_lhs || !eq.m_rhs)
                continue;
            euf::snode_vector toks;
            eq.m_lhs->collect_tokens(toks);
            for (euf::snode* t : toks) {
                if (t->is_power())
                    return t;
            }
            toks.reset();
            eq.m_rhs->collect_tokens(toks);
            for (euf::snode* t : toks) {
                if (t->is_power())
                    return t;
            }
        }
        return nullptr;
    }

    // -----------------------------------------------------------------------
    // Helper: find a power token facing a constant (char) head
    // Returns true if found, sets power, other_head, eq_out.
    // -----------------------------------------------------------------------

    bool nielsen_graph::find_power_vs_non_var(nielsen_node* node,
                                            euf::snode*& power,
                                            euf::snode*& other_head,
                                            str_eq const*& eq_out,
                                            bool& fwd) const {
        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial())
                continue;
            if (!eq.m_lhs || !eq.m_rhs)
                continue;
            for (unsigned od = 0; od < 2; ++od) {
                bool local_fwd = (od == 0);
                euf::snode* lhead = dir_token(eq.m_lhs, local_fwd);
                euf::snode* rhead = dir_token(eq.m_rhs, local_fwd);
                // Match power vs any non-variable, non-empty token (char, unit,
                // power with different base, etc.).
                // Same-base power vs power is handled by NumCmp (priority 3).
                // Power vs variable is handled by PowerSplit (priority 11).
                // Power vs empty is handled by PowerEpsilon (priority 2).
                if (lhead && lhead->is_power() && rhead && !rhead->is_var() && !rhead->is_empty()) {
                    power = lhead;
                    other_head = rhead;
                    eq_out = &eq;
                    fwd = local_fwd;
                    return true;
                }
                if (rhead && rhead->is_power() && lhead && !lhead->is_var() && !lhead->is_empty()) {
                    power = rhead;
                    other_head = lhead;
                    eq_out = &eq;
                    fwd = local_fwd;
                    return true;
                }
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
                                          str_eq const*& eq_out,
                                          bool& fwd) const {
        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial())
                continue;
            if (!eq.m_lhs || !eq.m_rhs)
                continue;
            for (unsigned od = 0; od < 2; ++od) {
                bool local_fwd = (od == 0);
                euf::snode* lhead = dir_token(eq.m_lhs, local_fwd);
                euf::snode* rhead = dir_token(eq.m_rhs, local_fwd);
                if (lhead && lhead->is_power() && rhead && rhead->is_var()) {
                    power = lhead;
                    var_head = rhead;
                    eq_out = &eq;
                    fwd = local_fwd;
                    return true;
                }
                if (rhead && rhead->is_power() && lhead && lhead->is_var()) {
                    power = rhead;
                    var_head = lhead;
                    eq_out = &eq;
                    fwd = local_fwd;
                    return true;
                }
            }
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_power_epsilon
    // Fires only when one side of an equation is empty and the other side
    // starts with a power token u^n.  In that case, branch:
    //   (1) base u → ε (base is empty, so u^n = ε)
    //   (2) u^n → ε (the power is zero, replace power with empty)
    // mirrors ZIPT's PowerEpsilonModifier (which requires LHS.IsEmpty())
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_power_epsilon(nielsen_node* node) {
        // Match only when one equation side is empty and the other starts
        // with a power.  This mirrors ZIPT where PowerEpsilonModifier is
        // constructed only inside the "if (LHS.IsEmpty())" branch of
        // ExtendDir.  When both sides are non-empty and a power faces a
        // constant, ConstNumUnwinding (priority 4) handles it with both
        // n=0 and n≥1 branches.
        euf::snode* power = nullptr;
        dep_tracker dep = m_dep_mgr.mk_empty();
        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial())
                continue;
            if (!eq.m_lhs || !eq.m_rhs)
                continue;
            if (eq.m_lhs->is_empty() && eq.m_rhs->first() && eq.m_rhs->first()->is_power()) {
                power = eq.m_rhs->first();
                dep = eq.m_dep;
                break;
            }
            if (eq.m_rhs->is_empty() && eq.m_lhs->first() && eq.m_lhs->first()->is_power()) {
                power = eq.m_lhs->first();
                dep = eq.m_dep;
                break;
            }
        }
        if (!power)
            return false;

        SASSERT(power->is_power() && power->num_args() >= 1);
        euf::snode *base = power->arg(0);

        nielsen_node* child;
        nielsen_edge* e;

        // Branch 1: base → ε (if base is a variable, substitute it to empty)
        // This makes u^n = ε^n = ε for any n.
        if (base->is_var()) {
            child = mk_child(node);
            e = mk_edge(node, child, true);
            nielsen_subst s1(base, m_sg.mk_empty_seq(base->get_sort()), dep);
            e->add_subst(s1);
            child->apply_subst(m_sg, s1);
        }

        // Branch 2: replace the power token itself with ε (n = 0 semantics)
        child = mk_child(node);
        e = mk_edge(node, child, true);
        nielsen_subst s2(power, m_sg.mk_empty_seq(power->get_sort()), dep);
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

        // Look for two directional endpoint power tokens with the same base.
        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial())
                continue;
            if (!eq.m_lhs || !eq.m_rhs)
                continue;
            for (unsigned od = 0; od < 2; ++od) {
                bool fwd = (od == 0);
                euf::snode* lhead = dir_token(eq.m_lhs, fwd);
                euf::snode* rhead = dir_token(eq.m_rhs, fwd);
                if (!lhead || !rhead)
                    continue;
                if (!lhead->is_power() || !rhead->is_power())
                    continue;
                if (lhead->num_args() < 1 || rhead->num_args() < 1)
                    continue;
                // same base: compare the two powers
                if (lhead->arg(0)->id() != rhead->arg(0)->id())
                    continue;

                // Skip if the exponents differ by a constant — simplify_and_init's
                // directional power elimination already handles that case.
                expr* exp_m = get_power_exponent(lhead);
                expr* exp_n = get_power_exponent(rhead);
                if (!exp_m || !exp_n)
                    continue;
                rational diff;
                SASSERT(!get_const_power_diff(exp_n, exp_m, arith, diff)); // handled by simplification

                // Branch 1 (explored first): n < m  (i.e., m >= n + 1)
                {
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, true);
                    expr_ref n_plus_1(arith.mk_add(exp_n, arith.mk_int(1)), m);
                    e->add_side_int(mk_int_constraint(
                        exp_m, n_plus_1,
                        int_constraint_kind::ge, eq.m_dep));
                }
                // Branch 2 (explored second): m <= n  (i.e., n >= m)
                {
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, true);
                    e->add_side_int(mk_int_constraint(
                        exp_n, exp_m,
                        int_constraint_kind::ge, eq.m_dep));
                }
                return true;
            }
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_split_power_elim
    // When one side starts with a power w^p, call CommPower on the other
    // side to count base-pattern occurrences c. If c > 0 and the ordering
    // between p and c cannot be determined, create two branches:
    //   Branch 1: p < c   (add constraint c ≥ p + 1)
    //   Branch 2: c ≤ p   (add constraint p ≥ c)
    // After branching, simplify_and_init's CommPower pass (3c) can resolve
    // the ordering deterministically and cancel the matched portion.
    // mirrors ZIPT's SplitPowerElim + NumCmpModifier
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_split_power_elim(nielsen_node* node) {
        ast_manager& m = m_sg.get_manager();
        arith_util arith(m);
        seq_util& seq = this->seq();

        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial())
                continue;
            if (!eq.m_lhs || !eq.m_rhs)
                continue;

            for (int side = 0; side < 2; ++side) {
                euf::snode* pow_side   = (side == 0) ? eq.m_lhs : eq.m_rhs;
                euf::snode* other_side = (side == 0) ? eq.m_rhs : eq.m_lhs;
                if (!pow_side || !other_side)
                    continue;

                for (unsigned od = 0; od < 2; ++od) {
                    bool fwd = od == 0;
                    euf::snode* end_tok = dir_token(pow_side, fwd);
                    if (!end_tok || !end_tok->is_power())
                        continue;
                    euf::snode* base_sn = end_tok->arg(0);
                    expr* pow_exp = get_power_exp_expr(end_tok, seq);
                    if (!base_sn || !pow_exp)
                        continue;

                    auto [count, consumed] = comm_power(base_sn, other_side, m, seq, fwd);
                    if (!count.get() || consumed == 0)
                        continue;

                    expr_ref norm_count = normalize_arith(m, count);

                    // Skip if ordering is already deterministic — simplify_and_init
                    // pass 3c should have handled it.
                    rational diff;
                    if (get_const_power_diff(norm_count, pow_exp, arith, diff))
                        continue;

                    // Branch 1: pow_exp < count (i.e., count >= pow_exp + 1)
                    {
                        nielsen_node* child = mk_child(node);
                        nielsen_edge* e = mk_edge(node, child, true);
                        expr_ref pow_plus1(arith.mk_add(pow_exp, arith.mk_int(1)), m);
                        e->add_side_int(mk_int_constraint(
                            norm_count, pow_plus1,
                            int_constraint_kind::ge, eq.m_dep));
                    }
                    // Branch 2: count <= pow_exp (i.e., pow_exp >= count)
                    {
                        nielsen_node* child = mk_child(node);
                        nielsen_edge* e = mk_edge(node, child, true);
                        e->add_side_int(mk_int_constraint(
                            pow_exp, norm_count,
                            int_constraint_kind::ge, eq.m_dep));
                    }
                    return true;
                }
            }
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
        ast_manager &m = m_sg.get_manager();
        arith_util arith(m);

        euf::snode *power = nullptr;
        euf::snode *other_head = nullptr;
        str_eq const *eq = nullptr;
        bool fwd = true;
        if (!find_power_vs_non_var(node, power, other_head, eq, fwd))
            return false;

        SASSERT(power->is_power() && power->num_args() >= 1);
        euf::snode *base = power->arg(0);
        expr *exp_n = get_power_exponent(power);
        expr *zero = arith.mk_int(0);
        expr *one = arith.mk_int(1);

        // Branch 1 (explored first): n = 0 → replace power with ε (progress)
        // Side constraint: n = 0
        nielsen_node *child = mk_child(node);
        nielsen_edge *e = mk_edge(node, child, true);
        nielsen_subst s1(power, m_sg.mk_empty_seq(power->get_sort()), eq->m_dep);
        e->add_subst(s1);
        child->apply_subst(m_sg, s1);
        if (exp_n)
            e->add_side_int(mk_int_constraint(exp_n, zero, int_constraint_kind::eq, eq->m_dep));

        // Branch 2 (explored second): n >= 1 → peel one u: replace u^n with u · u^(n-1)
        // Side constraint: n >= 1
        // Create a proper nested power base^(n-1) instead of a fresh string variable.
        // This preserves power structure so that simplify_and_init can merge and
        // cancel adjacent same-base powers (mirroring ZIPT's SimplifyPowerUnwind).
        // Explored first because the n≥1 branch is typically more productive
        // for SAT instances (preserves power structure).
        seq_util &seq = m_sg.get_seq_util();
        expr *power_e = power->get_expr();
        SASSERT(power_e);
        expr *base_expr = to_app(power_e)->get_arg(0);
        expr_ref n_minus_1 = normalize_arith(m, arith.mk_sub(exp_n, one));
        expr_ref nested_pow(seq.str.mk_power(base_expr, n_minus_1), m);
        euf::snode *nested_power_snode = m_sg.mk(nested_pow);

        euf::snode *replacement = dir_concat(m_sg, base, nested_power_snode, fwd);
        child = mk_child(node);
        e = mk_edge(node, child, false);
        nielsen_subst s2(power, replacement, eq->m_dep);
        e->add_subst(s2);
        child->apply_subst(m_sg, s2);
        if (exp_n)
            e->add_side_int(mk_int_constraint(exp_n, one, int_constraint_kind::ge, eq->m_dep));

        return true;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_star_intr
    // Star introduction: for a str_mem x·s ∈ R where a cycle is detected
    // (backedge exists), introduce a stabilizer constraint x ∈ base*.
    // Creates a child that splits x into pr·po, adds pr ∈ base* and
    // po·s ∈ R, with a blocking constraint on po.
    // Enhanced to use strengthened_stabilizer and register via add_stabilizer.
    // mirrors ZIPT's StarIntrModifier (StarIntrModifier.cs:22-85)
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_star_intr(nielsen_node* node) {
        // Only fire if a backedge was set (cycle detected)
        if (!node->backedge())
            return false;

        // Look for a str_mem with a variable-headed string
        for (unsigned mi = 0; mi < node->str_mems().size(); ++mi) {
            str_mem const& mem = node->str_mems()[mi];
            if (!mem.m_str || !mem.m_regex) continue;
            if (mem.is_primitive()) continue;
            euf::snode* first = mem.m_str->first();
            if (!first || !first->is_var()) continue;

            euf::snode* x = first;
            seq_util& seq = m_sg.get_seq_util();
            ast_manager& mgr = m_sg.get_manager();
            expr* re_expr = mem.m_regex->get_expr();
            if (!re_expr)
                continue;

            // Determine the stabilizer base:
            // 1. If self-stabilizing, use regex itself as stabilizer
            // 2. Otherwise, try strengthened_stabilizer from cycle history
            // 3. Fall back to simple star(R)
            euf::snode* stab_base = nullptr;

            if (m_seq_regex && m_seq_regex->is_self_stabilizing(mem.m_regex))
                stab_base = mem.m_regex;
            else if (m_seq_regex && mem.m_history)
                stab_base = m_seq_regex->strengthened_stabilizer(mem.m_regex, mem.m_history);

            if (!stab_base)
                // Fall back: simple star of the cycle regex
                stab_base = mem.m_regex;

            // Register the stabilizer
            if (m_seq_regex)
                m_seq_regex->add_stabilizer(mem.m_regex, stab_base);

            // Check if stabilizer equals regex → self-stabilizing
            if (m_seq_regex && stab_base == mem.m_regex)
                m_seq_regex->set_self_stabilizing(mem.m_regex);

            // Build stab_star = star(stab_base)
            expr* stab_expr = stab_base->get_expr();
            if (!stab_expr)
                continue;
            expr_ref star_re(seq.re.mk_star(stab_expr), mgr);
            euf::snode* star_sn = m_sg.mk(star_re);
            if (!star_sn)
                continue;

            // Try subsumption: if L(x_range) ⊆ L(stab_star), drop the constraint
            if (m_seq_regex && m_seq_regex->try_subsume(mem, *node))
                continue;

            // Create child: x → pr · po
            euf::snode* pr = mk_fresh_var(mem.m_str->get_sort());
            euf::snode* po = mk_fresh_var(mem.m_str->get_sort());
            euf::snode* str_tail = m_sg.drop_first(mem.m_str);

            nielsen_node* child = mk_child(node);

            // Add membership: pr ∈ stab_base* (stabilizer constraint)
            child->add_str_mem(str_mem(pr, star_sn, mem.m_history, next_mem_id(), mem.m_dep));

            // Add remaining membership: po · tail ∈ R (same regex, trimmed history)
            euf::snode* post_tail = str_tail->is_empty() ? po : m_sg.mk_concat(po, str_tail);
            child->add_str_mem(str_mem(post_tail, mem.m_regex, nullptr, next_mem_id(), mem.m_dep));

            // Blocking constraint: po must NOT start with stab_base
            // po ∈ complement(non_nullable(stab_base) · Σ*)
            // This prevents redundant unrolling.
            if (!stab_base->is_nullable()) {
                sort* str_sort = seq.str.mk_string_sort();
                expr_ref full_seq(seq.re.mk_full_seq(seq.re.mk_re(str_sort)), mgr);
                expr_ref base_then_all(seq.re.mk_concat(stab_expr, full_seq), mgr);
                expr_ref block_re(seq.re.mk_complement(base_then_all), mgr);
                euf::snode* block_sn = m_sg.mk(block_re);
                if (block_sn)
                    child->add_str_mem(str_mem(po, block_sn, nullptr, next_mem_id(), mem.m_dep));
            }

            // Substitute x → pr · po
            nielsen_edge* e = mk_edge(node, child, false);
            euf::snode* replacement = m_sg.mk_concat(pr, po);
            nielsen_subst s(x, replacement, mem.m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);

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
        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial())
                continue;
            if (!eq.m_lhs || !eq.m_rhs)
                continue;

            // Try both directions (ZIPT's ExtendDir(fwd=true/false)).
            for (unsigned od = 0; od < 2; ++od) {
                bool fwd = (od == 0);
                euf::snode* lhead = dir_token(eq.m_lhs, fwd);
                euf::snode* rhead = dir_token(eq.m_rhs, fwd);
                if (!lhead || !rhead)
                    continue;

                // Orientation 1: RHS directional head is var, scan LHS in that
                // direction for ground prefix + matching cycle var.
                if (rhead->is_var() && !lhead->is_var()) {
                    euf::snode_vector toks;
                    collect_tokens_dir(eq.m_lhs, fwd, toks);
                    euf::snode_vector ground_prefix;
                    euf::snode* target_var = nullptr;
                    for (unsigned i = 0; i < toks.size(); ++i) {
                        if (toks[i]->is_var()) {
                            target_var = toks[i];
                            break;
                        }
                        ground_prefix.push_back(toks[i]);
                    }
                    if (target_var && !ground_prefix.empty() && target_var->id() == rhead->id()) {
                        if (fire_gpower_intro(node, eq, rhead, ground_prefix, fwd))
                            return true;
                    }
                }

                // Orientation 2: LHS directional head is var, scan RHS analogously.
                if (lhead->is_var() && !rhead->is_var()) {
                    euf::snode_vector toks;
                    collect_tokens_dir(eq.m_rhs, fwd, toks);
                    euf::snode_vector ground_prefix;
                    euf::snode* target_var = nullptr;
                    for (unsigned i = 0; i < toks.size(); ++i) {
                        if (toks[i]->is_var()) {
                            target_var = toks[i];
                            break;
                        }
                        ground_prefix.push_back(toks[i]);
                    }
                    if (target_var && !ground_prefix.empty() && target_var->id() == lhead->id()) {
                        if (fire_gpower_intro(node, eq, lhead, ground_prefix, fwd))
                            return true;
                    }
                }
            }
            // TODO: Extend to transitive cycles across multiple equations
            // (ZIPT's varDep + HasDepCycle). Currently only self-cycles are detected.
        }
        return false;
    }

    bool nielsen_graph::fire_gpower_intro(
            nielsen_node* node, str_eq const& eq,
            euf::snode* var, euf::snode_vector const& ground_prefix_orig, bool fwd) {
        ast_manager& m = m_sg.get_manager();
        arith_util arith(m);
        seq_util& seq = m_sg.get_seq_util();

        // Compress repeated patterns in the ground prefix (mirrors ZIPT's LcpCompressionFull).
        // E.g., [a,b,a,b] has minimal period 2 → use [a,b] as the power base.
        // This ensures we use the minimal repeating unit: x = (ab)^n · suffix
        // instead of x = (abab)^n · suffix.
        euf::snode_vector ground_prefix;
        unsigned n = ground_prefix_orig.size();
        unsigned period = n;
        for (unsigned p = 1; p <= n / 2; ++p) {
            if (n % p != 0)
                continue;
            bool match = true;
            for (unsigned i = p; i < n && match; ++i)
                match = ground_prefix_orig[i]->id() == ground_prefix_orig[i % p]->id();
            if (match) {
                period = p;
                break;
            }
        }
        for (unsigned i = 0; i < period; ++i) {
            ground_prefix.push_back(ground_prefix_orig[i]);
        }

        // If the compressed prefix is a single power snode, unwrap it to use
        // its base tokens, avoiding nested powers.
        // E.g., [(ab)^3] → [a, b] so we get (ab)^n instead of ((ab)^3)^n.
        // (mirrors ZIPT: if b.Length == 1 && b is PowerToken pt => b = pt.Base)
        if (ground_prefix.size() == 1 && ground_prefix[0]->is_power()) {
            expr* base_e = get_power_base_expr(ground_prefix[0], seq);
            if (base_e) {
                euf::snode* base_sn = m_sg.mk(base_e);
                if (base_sn) {
                    euf::snode_vector base_toks;
                    collect_tokens_dir(base_sn, fwd, base_toks);
                    if (!base_toks.empty()) {
                        ground_prefix.reset();
                        ground_prefix.append(base_toks);
                    }
                }
            }
        }

        unsigned base_len = ground_prefix.size();

        // Build base string expression from ground prefix tokens.
        // Each s_char snode's get_expr() is already seq.unit(ch) (a string).
        expr_ref base_str(m);
        for (unsigned i = 0; i < base_len; ++i) {
            expr* tok_expr = ground_prefix[i]->get_expr();
            if (!tok_expr) return false;
            if (i == 0)
                base_str = tok_expr;
            else if (fwd)
                base_str = seq.str.mk_concat(base_str, tok_expr);
            else
                base_str = seq.str.mk_concat(tok_expr, base_str);
        }

        // Create fresh exponent variable and power expression: base^n
        expr_ref fresh_n = mk_fresh_int_var();
        expr_ref power_expr(seq.str.mk_power(base_str, fresh_n), m);
        euf::snode* power_snode = m_sg.mk(power_expr);
        if (!power_snode)
            return false;

        expr* zero = arith.mk_int(0);

        // Generate children mirroring ZIPT's GetDecompose:
        // P(t0 · t1 · ... · t_{k-1}) = P(t0) | t0·P(t1) | ... | t0·...·t_{k-2}·P(t_{k-1})
        // For char tokens P(c) = {ε}, for power tokens P(u^m) = {u^m', 0 ≤ m' ≤ m}.
        // Child at position i substitutes var → base^n · t0·...·t_{i-1} · P(t_i).
        for (unsigned i = 0; i < base_len; ++i) {
            euf::snode* tok = ground_prefix[i];

            // Skip char position when preceding token is a power:
            // The power case at i-1 with 0 ≤ m' ≤ exp already covers m' = exp,
            // which produces the same result. Using the original exponent here
            // creates a rigid coupling that causes cycling.
            if (!tok->is_power() && i > 0 && ground_prefix[i - 1]->is_power())
                continue;

            // Build full-token prefix: ground_prefix[0..i-1]
            euf::snode* prefix_sn = nullptr;
            for (unsigned j = 0; j < i; ++j)
                prefix_sn = (j == 0) ? ground_prefix[0] : dir_concat(m_sg, prefix_sn, ground_prefix[j], fwd);

            euf::snode* replacement;
            expr_ref fresh_m(m);

            if (tok->is_power()) {
                // Token is a power u^exp: use fresh m' with 0 ≤ m' ≤ exp
                expr* inner_exp = get_power_exponent(tok);
                expr* inner_base = get_power_base_expr(tok, seq);
                if (inner_exp && inner_base) {
                    fresh_m = mk_fresh_int_var();
                    expr_ref partial_pow(seq.str.mk_power(inner_base, fresh_m), m);
                    euf::snode* partial_sn = m_sg.mk(partial_pow);
                    euf::snode* suffix_sn = prefix_sn ? dir_concat(m_sg, prefix_sn, partial_sn, fwd) : partial_sn;
                    replacement = dir_concat(m_sg, power_snode, suffix_sn, fwd);
                }
                else {
                    // Fallback: use full token (shouldn't normally happen)
                    euf::snode* suffix_sn = prefix_sn ? dir_concat(m_sg, prefix_sn, tok, fwd) : tok;
                    replacement = dir_concat(m_sg, power_snode, suffix_sn, fwd);
                }
            }
            else
                // Token is a char: P(char) = ε, suffix = just the prefix
                replacement = prefix_sn ? dir_concat(m_sg, power_snode, prefix_sn, fwd) : power_snode;

            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, true);
            nielsen_subst s(var, replacement, eq.m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);

            // Side constraint: n >= 0
            e->add_side_int(mk_int_constraint(fresh_n, zero, int_constraint_kind::ge, eq.m_dep));

            // Side constraints for fresh partial exponent
            if (fresh_m.get()) {
                expr* inner_exp = get_power_exponent(tok);
                // m' >= 0
                e->add_side_int(mk_int_constraint(fresh_m, zero, int_constraint_kind::ge, eq.m_dep));
                // m' <= inner_exp
                e->add_side_int(mk_int_constraint(inner_exp, fresh_m, int_constraint_kind::ge, eq.m_dep));
            }
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
            if (!mem.m_str || !mem.m_regex)
                continue;
            if (mem.is_primitive())
                continue;
            euf::snode* first = mem.m_str->first();
            if (!first || !first->is_var())
                continue;

            // Compute minterms from the regex
            // std::cout << "Regex split: " << mk_pp(mem.m_regex->get_expr(), m_sg.get_manager()) << std::endl;
            euf::snode_vector minterms;
            m_sg.compute_minterms(mem.m_regex, minterms);
            VERIFY(!minterms.empty());

            bool created = false;
            std::cout << "Considering regex: " << mk_pp(mem.m_regex->get_expr(), m_sg.get_manager()) << std::endl;

            // Branch 1: x → ε (progress)
            {
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                nielsen_subst s(first, m_sg.mk_empty_seq(first->get_sort()), mem.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
                created = true;
            }

            // Branch 2+: for each minterm m_i, x → ?c · x
            // where ?c is a symbolic char constrained by the minterm
            for (euf::snode* mt : minterms) {
                std::cout << "Processing minterm: " << mk_pp(mt->get_expr(), m_sg.get_manager()) << std::endl;
                SASSERT(mt);
                SASSERT(mt->get_expr());
                SASSERT(!mt->is_fail());

                // Try Brzozowski derivative with respect to this minterm
                // If the derivative is fail (empty language), skip this minterm
                euf::snode* deriv = m_sg.brzozowski_deriv(mem.m_regex, mt);
                SASSERT(deriv);
                if (deriv->is_fail())
                    continue;
                std::cout << "Result: " << mk_pp(deriv->get_expr(), m_sg.get_manager()) << std::endl;

                SASSERT(m_seq_regex);
                char_set cs = m_seq_regex->minterm_to_char_set(mt->get_expr());
                std::cout << "char_set:\n";
                for (auto& r : cs.ranges()) {
                    std::cout << "\t[" << r.m_lo << "; " << r.m_hi - 1 << "]" << std::endl;
                }

                euf::snode* fresh_char = nullptr;
                if (cs.is_unit()) {
                    expr_ref char_expr(m_sg.get_seq_util().str.mk_string(zstring(cs.first_char())), m_sg.get_manager());
                    fresh_char = m_sg.mk(char_expr);
                }
                else
                    fresh_char = mk_fresh_char_var();

                euf::snode* replacement = m_sg.mk_concat(fresh_char, first);
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, false);
                nielsen_subst s(first, replacement, mem.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
                // Constrain fresh_char to the character class of this minterm.
                // This is the key Parikh pruning step: when x → ?c · x' is
                // generated from minterm m_i, ?c must belong to the character
                // class described by m_i so that str ∈ derivative(R, m_i).
                if (!cs.is_unit() && !cs.is_empty())
                    child->add_char_range(fresh_char, cs);
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
        bool fwd = true;
        if (!find_power_vs_var(node, power, var_head, eq, fwd))
            return false;

        SASSERT(power->is_power() && power->num_args() >= 1);
        euf::snode* base = power->arg(0);
        expr* exp_n = get_power_exponent(power);
        expr* zero = arith.mk_int(0);

        // Branch 1: enumerate all decompositions of the base.
        // x = base^m · prefix_i(base) where 0 <= m < n
        // Uses the same GetDecompose pattern as fire_gpower_intro.
        {
            euf::snode_vector base_toks;
            collect_tokens_dir(base, fwd, base_toks);
            unsigned base_len = base_toks.size();
            expr* base_expr = get_power_base_expr(power, seq);
            if (!base_expr || base_len == 0)
                return false;

            expr_ref fresh_m = mk_fresh_int_var();
            expr_ref power_m_expr(seq.str.mk_power(base_expr, fresh_m), m);
            euf::snode* power_m_sn = m_sg.mk(power_m_expr);
            if (!power_m_sn)
                return false;

            for (unsigned i = 0; i < base_len; ++i) {
                euf::snode* tok = base_toks[i];

                // Skip char position when preceding token is a power:
                // the power case at i-1 with 0 <= m' <= exp already covers m' = exp.
                if (!tok->is_power() && i > 0 && base_toks[i - 1]->is_power())
                    continue;

                // Build full-token prefix: base_toks[0..i-1]
                euf::snode* prefix_sn = nullptr;
                for (unsigned j = 0; j < i; ++j)
                    prefix_sn = (j == 0) ? base_toks[0] : dir_concat(m_sg, prefix_sn, base_toks[j], fwd);

                euf::snode* replacement;
                expr_ref fresh_inner_m(m);

                if (tok->is_power()) {
                    // Token is a power u^exp: decompose with fresh m', 0 <= m' <= exp
                    expr* inner_exp = get_power_exponent(tok);
                    expr* inner_base_e = get_power_base_expr(tok, seq);
                    if (inner_exp && inner_base_e) {
                        fresh_inner_m = mk_fresh_int_var();
                        expr_ref partial_pow(seq.str.mk_power(inner_base_e, fresh_inner_m), m);
                        euf::snode* partial_sn = m_sg.mk(partial_pow);
                        euf::snode* suffix_sn = prefix_sn ? dir_concat(m_sg, prefix_sn, partial_sn, fwd) : partial_sn;
                        replacement = dir_concat(m_sg, power_m_sn, suffix_sn, fwd);
                    }
                    else {
                        euf::snode* suffix_sn = prefix_sn ? dir_concat(m_sg, prefix_sn, tok, fwd) : tok;
                        replacement = dir_concat(m_sg, power_m_sn, suffix_sn, fwd);
                    }
                }
                else
                    // P(char) = ε, suffix is just the prefix
                    replacement = prefix_sn ? dir_concat(m_sg, power_m_sn, prefix_sn, fwd) : power_m_sn;

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

                // Inner power constraints: 0 <= m' <= inner_exp
                if (fresh_inner_m.get()) {
                    expr* inner_exp = get_power_exponent(tok);
                    e->add_side_int(mk_int_constraint(fresh_inner_m, zero, int_constraint_kind::ge, eq->m_dep));
                    e->add_side_int(mk_int_constraint(inner_exp, fresh_inner_m, int_constraint_kind::ge, eq->m_dep));
                }
            }
        }

        // Branch 2: x = u^n · x' (variable extends past full power, non-progress)
        {
            euf::snode* fresh_tail = mk_fresh_var(var_head->get_sort());
            euf::snode* replacement = dir_concat(m_sg, power, fresh_tail, fwd);
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
    // Generates integer side constraints for each branch.
    // mirrors ZIPT's VarNumUnwindingModifier
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_var_num_unwinding(nielsen_node* node) {
        ast_manager& m = m_sg.get_manager();
        arith_util arith(m);

        euf::snode* power = nullptr;
        euf::snode* var_head = nullptr;
        str_eq const* eq = nullptr;
        bool fwd = true;
        if (!find_power_vs_var(node, power, var_head, eq, fwd))
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
            nielsen_subst s(power, m_sg.mk_empty_seq(power->get_sort()), eq->m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
            if (exp_n)
                e->add_side_int(mk_int_constraint(exp_n, zero, int_constraint_kind::eq, eq->m_dep));
        }

        // Branch 2: n >= 1 → peel one u: u^n → u · u^(n-1)
        // Side constraint: n >= 1
        {
            euf::snode* fresh = mk_fresh_var(var_head->get_sort());
            euf::snode* replacement = dir_concat(m_sg, base, fresh, fwd);
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
                deps = m_dep_mgr.mk_join(deps, eq.m_dep);
            for (str_mem const& mem : n->str_mems())
                deps = m_dep_mgr.mk_join(deps, mem.m_dep);
        }
    }

    
    // NSB review: this is one of several methods exposed for testing
    void nielsen_graph::explain_conflict(svector<enode_pair>& eqs, 
        svector<sat::literal>& mem_literals) const {
        SASSERT(m_root);
        dep_tracker deps = m_dep_mgr.mk_empty();
        collect_conflict_deps(deps);
        vector<dep_source, false> vs;
        m_dep_mgr.linearize(deps, vs);
        for (dep_source const& d : vs) {
            if (std::holds_alternative<enode_pair>(d))
                eqs.push_back(std::get<enode_pair>(d));
            else
                mem_literals.push_back(std::get<sat::literal>(d));
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

        // For variables: consult modification counter.
        // mod_count > 0 means the variable has been reused by a non-eliminating
        // substitution; use a fresh integer variable to avoid the circular
        // |x| = 1 + |x| problem.
        if (n->is_var()) {
            unsigned mc = 0;
            m_mod_cnt.find(n->id(), mc);
            if (mc > 0)
                return get_or_create_len_var(n, mc);
        }

        // for variables at mod_count 0 and other terms, use symbolic (str.len expr)
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
    // Integer feasibility subsolver implementation
    // Uses the injected simple_solver (default: lp_simple_solver).
    // -----------------------------------------------------------------------

    expr_ref nielsen_graph::int_constraint_to_expr(int_constraint const& ic) {
        ast_manager& m = m_sg.get_manager();
        arith_util arith(m);
        switch (ic.m_kind) {
        case int_constraint_kind::eq:
            return expr_ref(m.mk_eq(ic.m_lhs, ic.m_rhs), m);
        case int_constraint_kind::le:
            return expr_ref(arith.mk_le(ic.m_lhs, ic.m_rhs), m);
        case int_constraint_kind::ge:
            return expr_ref(arith.mk_ge(ic.m_lhs, ic.m_rhs), m);
        }
        UNREACHABLE();
        return expr_ref(m.mk_true(), m);
    }

    // -----------------------------------------------------------------------
    // Modification counter: substitution length tracking
    // mirrors ZIPT's LocalInfo.CurrentModificationCnt + NielsenEdge.IncModCount/DecModCount
    // + NielsenNode constructor length assertion logic
    // -----------------------------------------------------------------------

    expr_ref nielsen_graph::get_or_create_len_var(euf::snode* var, unsigned mod_count) {
        ast_manager& m = m_sg.get_manager();
        SASSERT(var && var->is_var());
        SASSERT(mod_count > 0);

        auto key = std::make_pair(var->id(), mod_count);
        auto it = m_len_var_cache.find(key);
        if (it != m_len_var_cache.end())
            return expr_ref(it->second, m);

        // Create a fresh integer variable: len_<varname>_<mod_count>
        arith_util arith(m);
        std::string name = "len!" + std::to_string(var->id()) + "!" + std::to_string(mod_count);
        expr_ref fresh(m.mk_fresh_const(name.c_str(), arith.mk_int()), m);
        m_len_vars.push_back(fresh);
        m_len_var_cache.insert({key, fresh.get()});
        return fresh;
    }

    void nielsen_graph::add_subst_length_constraints(nielsen_edge* e) {
        auto const& substs = e->subst();

        // Quick check: any non-eliminating substitutions?
        bool has_non_elim = false;
        for (auto const& s : substs)
            if (!s.is_eliminating()) { has_non_elim = true; break; }
        if (!has_non_elim) return;

        ast_manager& m = m_sg.get_manager();
        arith_util arith(m);

        // Step 1: Compute LHS (|x|) for each non-eliminating substitution
        // using current m_mod_cnt (before bumping).
        // Also assert |x|_k >= 0 (mirrors ZIPT's NielsenNode constructor line 172).
        svector<std::pair<unsigned, expr*>> lhs_exprs;
        for (unsigned i = 0; i < substs.size(); ++i) {
            auto const& s = substs[i];
            if (s.is_eliminating()) continue;
            SASSERT(s.m_var && s.m_var->is_var());
            expr_ref lhs = compute_length_expr(s.m_var);
            lhs_exprs.push_back({i, lhs.get()});
            // Assert LHS >= 0
            e->add_side_int(int_constraint(lhs, arith.mk_int(0),
                                           int_constraint_kind::ge, s.m_dep, m));
        }

        // Step 2: Bump mod counts for all non-eliminating variables at once.
        for (auto const& s : substs) {
            if (s.is_eliminating()) continue;
            unsigned id = s.m_var->id();
            unsigned prev = 0;
            m_mod_cnt.find(id, prev);
            m_mod_cnt.insert(id, prev + 1);
        }

        // Step 3: Compute RHS (|u|) with bumped mod counts and add |x| = |u|.
        for (auto const& p : lhs_exprs) {
            unsigned idx = p.first;
            expr* lhs_expr = p.second;
            auto const& s = substs[idx];
            expr_ref rhs = compute_length_expr(s.m_replacement);
            e->add_side_int(int_constraint(lhs_expr, rhs, int_constraint_kind::eq,
                                           s.m_dep, m));

            // Assert non-negativity for any fresh length variables in the RHS
            // (variables at mod_count > 0 that are newly created).
            euf::snode_vector tokens;
            s.m_replacement->collect_tokens(tokens);
            for (euf::snode* tok : tokens) {
                if (tok->is_var()) {
                    unsigned mc = 0;
                    m_mod_cnt.find(tok->id(), mc);
                    if (mc > 0) {
                        expr_ref len_var = get_or_create_len_var(tok, mc);
                        e->add_side_int(int_constraint(len_var, arith.mk_int(0),
                                                       int_constraint_kind::ge, s.m_dep, m));
                    }
                }
            }
        }

        // Step 4: Restore mod counts (temporary bump for computing RHS only).
        for (auto const& s : substs) {
            if (s.is_eliminating()) continue;
            unsigned id = s.m_var->id();
            unsigned prev = 0;
            m_mod_cnt.find(id, prev);
            SASSERT(prev >= 1);
            if (prev <= 1)
                m_mod_cnt.remove(id);
            else
                m_mod_cnt.insert(id, prev - 1);
        }
    }

    void nielsen_graph::inc_edge_mod_counts(nielsen_edge* e) {
        for (auto const& s : e->subst()) {
            if (s.is_eliminating()) continue;
            unsigned id = s.m_var->id();
            unsigned prev = 0;
            m_mod_cnt.find(id, prev);
            m_mod_cnt.insert(id, prev + 1);
        }
    }

    void nielsen_graph::dec_edge_mod_counts(nielsen_edge* e) {
        for (auto const& s : e->subst()) {
            if (s.is_eliminating()) continue;
            unsigned id = s.m_var->id();
            unsigned prev = 0;
            m_mod_cnt.find(id, prev);
            SASSERT(prev >= 1);
            if (prev <= 1)
                m_mod_cnt.remove(id);
            else
                m_mod_cnt.insert(id, prev - 1);
        }
    }

    void nielsen_graph::assert_node_new_int_constraints(nielsen_node* node) {
        // Assert only the int_constraints that are new to this node (beyond those
        // inherited from its parent via clone_from).  The parent's constraints are
        // already present in the enclosing solver scope; asserting them again would
        // be redundant (though harmless).  This is called by search_dfs right after
        // simplify_and_init, which is where new constraints are produced.
        for (unsigned i = node->m_parent_ic_count; i < node->int_constraints().size(); ++i)
            m_solver.assert_expr(int_constraint_to_expr(node->int_constraints()[i]));
    }

    void nielsen_graph::generate_node_length_constraints(nielsen_node* node) {
        if (node->m_node_len_constraints_generated)
            return;
        node->m_node_len_constraints_generated = true;

        // Skip the root node — its length constraints are already asserted
        // at the base solver level by assert_root_constraints_to_solver().
        if (node == m_root)
            return;

        ast_manager& m = m_sg.get_manager();
        arith_util arith(m);
        uint_set seen_vars;

        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial())
                continue;

            expr_ref len_lhs = compute_length_expr(eq.m_lhs);
            expr_ref len_rhs = compute_length_expr(eq.m_rhs);
            node->add_int_constraint(int_constraint(len_lhs, len_rhs,
                                                     int_constraint_kind::eq, eq.m_dep, m));

            // non-negativity for each variable (mod-count-aware)
            euf::snode_vector tokens;
            eq.m_lhs->collect_tokens(tokens);
            eq.m_rhs->collect_tokens(tokens);
            for (euf::snode* tok : tokens) {
                if (tok->is_var() && !seen_vars.contains(tok->id())) {
                    seen_vars.insert(tok->id());
                    expr_ref len_var = compute_length_expr(tok);
                    node->add_int_constraint(int_constraint(len_var, arith.mk_int(0),
                                                             int_constraint_kind::ge, eq.m_dep, m));
                }
            }
        }

        // Parikh interval bounds for regex memberships at this node
        seq_util& seq = m_sg.get_seq_util();
        for (str_mem const& mem : node->str_mems()) {
            expr* re_expr = mem.m_regex->get_expr();
            if (!re_expr || !seq.is_re(re_expr))
                continue;

            unsigned min_len = 0, max_len = UINT_MAX;
            compute_regex_length_interval(mem.m_regex, min_len, max_len);

            expr_ref len_str = compute_length_expr(mem.m_str);

            if (min_len > 0) {
                node->add_int_constraint(int_constraint(len_str, arith.mk_int(min_len),
                                                         int_constraint_kind::ge, mem.m_dep, m));
            }
            if (max_len < UINT_MAX) {
                node->add_int_constraint(int_constraint(len_str, arith.mk_int(max_len),
                                                         int_constraint_kind::le, mem.m_dep, m));
            }

            // non-negativity for string-side variables
            euf::snode_vector tokens;
            mem.m_str->collect_tokens(tokens);
            for (euf::snode* tok : tokens) {
                if (tok->is_var() && !seen_vars.contains(tok->id())) {
                    seen_vars.insert(tok->id());
                    expr_ref len_var = compute_length_expr(tok);
                    node->add_int_constraint(int_constraint(len_var, arith.mk_int(0),
                                                             int_constraint_kind::ge, mem.m_dep, m));
                }
            }
        }
    }

    bool nielsen_graph::check_int_feasibility(nielsen_node* node, svector<nielsen_edge*> const& cur_path) {
        // In incremental mode the solver already holds all path constraints
        // (root length constraints at the base level, edge side_int and node
        // int_constraints pushed/popped as the DFS descends and backtracks).
        // A plain check() is therefore sufficient.
        return m_solver.check() != l_false;
    }

    bool nielsen_graph::check_lp_le(expr* lhs, expr* rhs,
                                     nielsen_node* node,
                                     svector<nielsen_edge*> const& cur_path) {
        ast_manager& m = m_sg.get_manager();
        arith_util arith(m);

        // The solver already holds all path constraints incrementally.
        // Temporarily add NOT(lhs <= rhs), i.e. lhs >= rhs + 1.
        // If that is unsat, then lhs <= rhs is entailed.
        expr_ref one(arith.mk_int(1), m);
        expr_ref rhs_plus_one(arith.mk_add(rhs, one), m);

        m_solver.push();
        m_solver.assert_expr(arith.mk_ge(lhs, rhs_plus_one));
        lbool result = m_solver.check();
        m_solver.pop(1);
        return result == l_false;
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

    bool nielsen_graph::solve_sat_path_ints(model_ref& mdl) {
        mdl = nullptr;
        if (m_sat_path.empty() && (!m_sat_node || m_sat_node->int_constraints().empty()))
            return false;

        // Re-assert the sat-path constraints into m_solver (which holds only root-level
        // constraints at this point) and extract a model via the injected simple_solver.
        // The sat path was found by DFS which verified feasibility at every step via
        // check_int_feasibility, so all constraints along this path are jointly satisfiable
        // and do not require incremental skipping.
        IF_VERBOSE(1, verbose_stream() << "solve_sat_path_ints: sat_path length=" << m_sat_path.size() << "\n";);
        m_solver.push();
        for (nielsen_edge* e : m_sat_path)
            for (auto const& ic : e->side_int())
                m_solver.assert_expr(int_constraint_to_expr(ic));
        if (m_sat_node)
            for (auto const& ic : m_sat_node->int_constraints())
                m_solver.assert_expr(int_constraint_to_expr(ic));
        lbool result = m_solver.check();
        IF_VERBOSE(1, verbose_stream() << "solve_sat_path_ints result: " << result << "\n";);
        if (result == l_true) {
            m_solver.get_model(mdl);
            IF_VERBOSE(1, if (mdl) {
                ast_manager& m = m_sg.get_manager();
                verbose_stream() << "  int_model:\n";
                for (unsigned i = 0; i < mdl->get_num_constants(); ++i) {
                    func_decl* fd = mdl->get_constant(i);
                    expr* val = mdl->get_const_interp(fd);
                    if (val) verbose_stream() << "    " << fd->get_name() << " = " << mk_bounded_pp(val, m, 3) << "\n";
                }
            });
        }
        m_solver.pop(1);
        return mdl.get() != nullptr;
    }

    // -----------------------------------------------------------------------
    // Regex widening: overapproximate string and check intersection emptiness
    // Mirrors ZIPT NielsenNode.CheckRegexWidening (NielsenNode.cs:1350-1380)
    // -----------------------------------------------------------------------

    bool nielsen_graph::check_regex_widening(nielsen_node const& node,
                                             euf::snode* str, euf::snode* regex) {
        SASSERT(str && regex && m_seq_regex);
        // Only apply to ground regexes with non-trivial strings
        if (!regex->is_ground())
            return false;

        seq_util& seq = m_sg.get_seq_util();
        ast_manager& mgr = m_sg.get_manager();

        // Build the overapproximation regex for the string.
        // Variables → intersection of their primitive regex constraints (or Σ*)
        // Symbolic chars → re.range from char_ranges (or full_char)
        // Concrete chars → to_re(unit(c))
        euf::snode_vector tokens;
        str->collect_tokens(tokens);
        if (tokens.empty())
            return false;

        euf::snode* approx = nullptr;
        for (euf::snode* tok : tokens) {
            euf::snode* tok_re = nullptr;

            if (tok->is_char()) {
                // Concrete character → to_re(unit(c))
                expr* te = tok->get_expr();
                SASSERT(te);
                expr_ref tre(seq.re.mk_to_re(te), mgr);
                tok_re = m_sg.mk(tre);
            }
            else if (tok->is_var()) {
                // Variable → intersection of primitive regex constraints, or Σ*
                euf::snode* x_range = m_seq_regex->collect_primitive_regex_intersection(tok, node);
                if (x_range)
                    tok_re = x_range;
                else {
                    // Unconstrained variable: approximate as Σ*
                    sort* str_sort = seq.str.mk_string_sort();
                    expr_ref all_re(seq.re.mk_full_seq(seq.re.mk_re(str_sort)), mgr);
                    tok_re = m_sg.mk(all_re);
                }
            }
            else if (tok->is_unit()) {
                // Symbolic char — try to get char_range
                if (node.char_ranges().contains(tok->id())) {
                    char_set const& cs = node.char_ranges()[tok->id()];
                    if (!cs.is_empty()) {
                        // Build union of re.range for each interval
                        euf::snode* range_re = nullptr;
                        for (auto const& r : cs.ranges()) {
                            expr_ref lo(seq.mk_char(r.m_lo), mgr);
                            expr_ref hi(seq.mk_char(r.m_hi - 1), mgr);
                            expr_ref rng(seq.re.mk_range(
                                seq.str.mk_string(zstring(r.m_lo)),
                                seq.str.mk_string(zstring(r.m_hi - 1))), mgr);
                            euf::snode* rng_sn = m_sg.mk(rng);
                            if (!range_re)
                                range_re = rng_sn;
                            else {
                                expr_ref u(seq.re.mk_union(range_re->get_expr(), rng_sn->get_expr()), mgr);
                                range_re = m_sg.mk(u);
                            }
                        }
                        tok_re = range_re;
                    }
                }
                if (!tok_re) {
                    // Unconstrained symbolic char: approximate as full_char (single char, any value)
                    sort* str_sort = seq.str.mk_string_sort();
                    expr_ref fc(seq.re.mk_full_char(seq.re.mk_re(str_sort)), mgr);
                    tok_re = m_sg.mk(fc);
                }
            }
            else {
                // Unknown token type — approximate as Σ*
                sort* str_sort = seq.str.mk_string_sort();
                expr_ref all_re(seq.re.mk_full_seq(seq.re.mk_re(str_sort)), mgr);
                tok_re = m_sg.mk(all_re);
            }

            SASSERT(tok_re);

            if (!approx)
                approx = tok_re;
            else {
                expr* ae = approx->get_expr();
                expr* te = tok_re->get_expr();
                SASSERT(ae && te);
                expr_ref cat(seq.re.mk_concat(ae, te), mgr);
                approx = m_sg.mk(cat);
            }
        }

        if (!approx)
            return false;

        // Check intersection(approx, regex) for emptiness
        // Build intersection regex
        expr* ae = approx->get_expr();
        expr* re = regex->get_expr();
        SASSERT(ae && re);
        expr_ref inter(seq.re.mk_inter(ae, re), mgr);
        euf::snode* inter_sn = m_sg.mk(inter);
        SASSERT(inter_sn);
        // std::cout << "HTML: " << snode_label_html(inter_sn, m()) << std::endl;
        lbool result = m_seq_regex->is_empty_bfs(inter_sn, 5000);
        return result == l_true;
    }

    // -----------------------------------------------------------------------
    // Leaf-node regex intersection emptiness check
    // Mirrors ZIPT NielsenNode.CheckRegex (NielsenNode.cs:1311-1329)
    // -----------------------------------------------------------------------

    bool nielsen_graph::check_leaf_regex(nielsen_node const& node) {
        if (!m_seq_regex)
            return true;

        // Group str_mem constraints by variable (primitive constraints only)
        u_map<ptr_vector<euf::snode>> var_regexes;

        for (auto const& mem : node.str_mems()) {
            if (!mem.m_str || !mem.m_regex)
                continue;
            if (!mem.is_primitive())
                continue;
            euf::snode* first = mem.m_str->first();
            if (!first || !first->is_var())
                continue;
            auto& list = var_regexes.insert_if_not_there(first->id(), ptr_vector<euf::snode>());
            list.push_back(mem.m_regex);
        }

        // For each variable with 2+ regex constraints, check intersection non-emptiness
        for (auto& [var_id, regexes] : var_regexes) {
            if (regexes.size() < 2)
                continue;
            lbool result = m_seq_regex->check_intersection_emptiness(regexes, 5000);
            if (result == l_true) {
                // Intersection is empty — infeasible
                return false;
            }
        }
        return true;
    }

    // -----------------------------------------------------------------------
    // Statistics collection
    // -----------------------------------------------------------------------

    void nielsen_graph::collect_statistics(::statistics& st) const {
        st.update("nseq solve calls",     m_stats.m_num_solve_calls);
        st.update("nseq dfs nodes",       m_stats.m_num_dfs_nodes);
        st.update("nseq sat",             m_stats.m_num_sat);
        st.update("nseq unsat",           m_stats.m_num_unsat);
        st.update("nseq unknown",         m_stats.m_num_unknown);
        st.update("nseq simplify clash",  m_stats.m_num_simplify_conflict);
        st.update("nseq extensions",      m_stats.m_num_extensions);
        st.update("nseq fresh vars",      m_stats.m_num_fresh_vars);
        st.update("nseq max depth",       m_stats.m_max_depth);

        // modifier breakdown
        st.update("nseq mod det",              m_stats.m_mod_det);
        st.update("nseq mod power epsilon",    m_stats.m_mod_power_epsilon);
        st.update("nseq mod num cmp",          m_stats.m_mod_num_cmp);
        st.update("nseq mod const num unwind", m_stats.m_mod_const_num_unwinding);
        st.update("nseq mod eq split",         m_stats.m_mod_eq_split);
        st.update("nseq mod star intr",        m_stats.m_mod_star_intr);
        st.update("nseq mod gpower intr",      m_stats.m_mod_gpower_intr);
        st.update("nseq mod const nielsen",    m_stats.m_mod_const_nielsen);
        st.update("nseq mod regex var",        m_stats.m_mod_regex_var_split);
        st.update("nseq mod power split",      m_stats.m_mod_power_split);
        st.update("nseq mod var nielsen",      m_stats.m_mod_var_nielsen);
        st.update("nseq mod var num unwind",   m_stats.m_mod_var_num_unwinding);
    }

}



