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

NSB review:

   ostrich\substring2b.smt2, ostrich\substring.smt2
   - We are missing rewrites for unit(x) = unit('a') that would eliminate x by a.


--*/

#include "smt/seq/seq_nielsen.h"
#include "smt/seq/seq_parikh.h"
#include "smt/seq/seq_regex.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/seq_skolem.h"
#include "ast/rewriter/var_subst.h"
#include "util/statistics.h"
#include <algorithm>
#include <cstdlib>
#include <unordered_map>

namespace seq {

    void deps_to_lits(dep_tracker const &deps, svector<enode_pair> &eqs, svector<sat::literal> &lits) {
        vector<dep_source, false> vs;
        dep_manager::s_linearize(deps, vs);
        for (dep_source const &d : vs) {
            if (std::holds_alternative<enode_pair>(d))
                eqs.push_back(std::get<enode_pair>(d));
            else
                lits.push_back(std::get<sat::literal>(d));
        }
    }

    // Normalize an arithmetic expression using th_rewriter.
    // Simplifies e.g. (n - 1 + 1) to n, preventing unbounded growth
    // of power exponents during unwind/merge cycles.
    static expr_ref normalize_arith(ast_manager &m, expr *e) {
        expr_ref result(e, m);
        th_rewriter rw(m);
        rw(result);
        return result;
    }

    // Directional helpers mirroring ZIPT's fwd flag:
    // fwd=true  -> left-to-right (prefix/head)
    // fwd=false -> right-to-left (suffix/tail)
    static euf::snode *dir_token(euf::snode *s, bool fwd) {
        if (!s)
            return nullptr;
        return fwd ? s->first() : s->last();
    }

    static euf::snode *dir_drop(euf::sgraph &sg, euf::snode *s, unsigned count, bool fwd) {
        if (!s || count == 0)
            return s;
        return fwd ? sg.drop_left(s, count) : sg.drop_right(s, count);
    }

    static euf::snode *dir_concat(euf::sgraph &sg, euf::snode *a, euf::snode *b, bool fwd) {
        if (!a)
            return b;
        if (!b)
            return a;
        return fwd ? sg.mk_concat(a, b) : sg.mk_concat(b, a);
    }

    static void collect_tokens_dir(euf::snode *s, bool fwd, euf::snode_vector &toks) {
        toks.reset();
        if (!s)
            return;
        s->collect_tokens(toks);
        if (!fwd)
            toks.reverse();
    }

    // Right-derivative helper used by backward str_mem simplification:
    // dR(re, c) = reverse( derivative(c, reverse(re)) ).
    static euf::snode *reverse_brzozowski_deriv(euf::sgraph &sg, euf::snode *re, euf::snode *elem) {
        if (!re || !elem || !re->get_expr() || !elem->get_expr())
            return nullptr;
        ast_manager &m = sg.get_manager();
        seq_util &seq = sg.get_seq_util();
        seq_rewriter rw(m);

        expr *elem_expr = elem->get_expr();
        expr *ch = nullptr;
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
        SASSERT(!m_lhs || !m_rhs || m_lhs->id() <= m_rhs->id());
    }

    bool str_eq::is_trivial() const {
        return m_lhs == m_rhs || (m_lhs && m_rhs && m_lhs->is_empty() && m_rhs->is_empty());
    }

    bool str_eq::contains_var(euf::snode *var) const {
        if (!var)
            return false;
        // check if var appears in the token list of lhs or rhs
        if (m_lhs) {
            euf::snode_vector tokens;
            m_lhs->collect_tokens(tokens);
            for (euf::snode *t : tokens) {
                if (t == var)
                    return true;
            }
        }
        if (m_rhs) {
            euf::snode_vector tokens;
            m_rhs->collect_tokens(tokens);
            for (euf::snode *t : tokens) {
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
        return m_str && m_str->length() == 1 && m_str->is_var() && m_regex->is_ground();
    }

    bool str_mem::is_trivial() const {
        return m_str && m_regex && m_str->is_empty() && m_regex->is_nullable();
    }

    bool str_mem::is_contradiction() const {
        return (m_str && m_regex && m_str->is_empty() && !m_regex->is_nullable());
    }

    bool str_mem::contains_var(euf::snode* var) const {
        SASSERT(var);
        if (m_str) {
            euf::snode_vector tokens;
            m_str->collect_tokens(tokens);
            return any_of(tokens, [var](auto t) { return t == var; });
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
        return all_of(tokens, [this](auto t) { return t != m_var; });
    }

    bool nielsen_subst::is_char_subst() const {
        SASSERT(m_var && m_replacement);
        SASSERT(!m_var->is_unit() || m_replacement->is_char_or_unit());
        return m_var->is_unit();
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
        m_constraints.reset();
        m_char_diseqs.reset();
        m_char_ranges.reset();
        m_str_eq.append(parent.m_str_eq);
        m_str_mem.append(parent.m_str_mem);
        m_constraints.append(parent.m_constraints);

        // clone character disequalities

        for (auto const &[k,v] : parent.m_char_diseqs)
            m_char_diseqs.insert(k, v);

        // clone character ranges
        for (auto const &[k, v] : parent.m_char_ranges)
            m_char_ranges.insert(k, std::make_pair(v.first.clone(), v.second));

        // clone regex occurrence tracking
        m_regex_occurrence = parent.m_regex_occurrence;

        SASSERT(m_str_eq.size() == parent.m_str_eq.size());
        SASSERT(m_str_mem.size() == parent.m_str_mem.size());
        SASSERT(m_constraints.size() == parent.m_constraints.size());
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

    bool nielsen_node::add_constraint(constraint const &c) {
        if (graph().get_manager().is_and(c.fml)) {
            for (const auto f : *to_app(c.fml)) {
                if (!add_constraint(constraint(f, c.dep, graph().get_manager())))
                    return false;
            }
            return true;
        }
        m_constraints.push_back(c);
        if (m_graph.m_literal_if_false) {
            auto lit = m_graph.m_literal_if_false(c.fml);
            if (lit != sat::null_literal) {
                set_external_conflict(lit);
                return false;
            }
        }
        return true;
    }

    void nielsen_node::apply_subst(euf::sgraph& sg, nielsen_subst const& s) {
        SASSERT(s.m_var);
        SASSERT(s.m_replacement != nullptr);
        for (auto &eq : m_str_eq) {
            auto new_lhs = sg.subst(eq.m_lhs, s.m_var, s.m_replacement);
            auto new_rhs = sg.subst(eq.m_rhs, s.m_var, s.m_replacement);
            if (new_lhs != eq.m_lhs || new_rhs != eq.m_rhs) {
                 eq.m_lhs = new_lhs;
                 eq.m_rhs = new_rhs;
                 eq.m_dep = m_graph.dep_mgr().mk_join(eq.m_dep, s.m_dep);
                 eq.sort();
            }
        }

        for (auto &mem : m_str_mem) {
            auto new_str = sg.subst(mem.m_str, s.m_var, s.m_replacement);
            auto new_regex = sg.subst(mem.m_regex, s.m_var, s.m_replacement);
            if (new_str != mem.m_str || new_regex != mem.m_regex) {
                 mem.m_str = new_str;
                 mem.m_regex = new_regex;
                 mem.m_dep = m_graph.dep_mgr().mk_join(mem.m_dep, s.m_dep);
            }
        }
        if (s.m_var->get_expr() && !sg.get_seq_util().is_seq(s.m_var->get_expr()) && !sg.get_seq_util().is_re(s.m_var->get_expr())) {
            expr* v = s.m_var->get_expr();
            expr* repl = s.m_replacement->get_expr();
            
            expr* eq = sg.get_manager().mk_eq(v, repl);
            add_constraint(constraint(eq, s.m_dep, sg.get_manager()));
        }
    }

    void nielsen_node::add_char_range(euf::snode* sym_char, char_set const& range, dep_tracker dep) {
        SASSERT(sym_char && sym_char->is_unit());
        unsigned id = sym_char->id();
        if (m_char_ranges.contains(id)) {
            auto& existing = m_char_ranges.find(id);
            char_set inter = existing.first.intersect_with(range);
            existing = std::make_pair(inter, graph().dep_mgr().mk_join(existing.second, dep));
            if (inter.is_empty()) {
                m_is_general_conflict = true;
                set_conflict(backtrack_reason::character_range, existing.second);
            }
        }
        else
            m_char_ranges.insert(id, std::make_pair(range.clone(), dep));
    }

    void nielsen_node::add_char_diseq(euf::snode* sym_char, euf::snode* other, dep_tracker dep) {
        SASSERT(sym_char && sym_char->is_unit());
        SASSERT(other && other->is_unit());
        unsigned id = sym_char->id();
        if (!m_char_diseqs.contains(id))
            m_char_diseqs.insert(id, vector<std::pair<euf::snode*, dep_tracker>>());
        vector<std::pair<euf::snode*, dep_tracker>>& existing = m_char_diseqs.find(id);
        // check for duplicates
        for (auto& s : existing) {
            if (s.first == other)
                return;
        }
        existing.push_back(std::make_pair(other, dep));
    }

    bool nielsen_node::lower_bound(expr* e, rational& lo) const {
        SASSERT(e);
        return m_graph.m_solver.lower_bound(e, lo);
    }


    bool nielsen_node::upper_bound(expr* e, rational& up) const {
        SASSERT(e);
        rational v;
        if (m_graph.a.is_numeral(e, v)) {
            up = v;
            return true;
        }
        return m_graph.m_solver.upper_bound(e, up);
    }

    void nielsen_node::apply_char_subst(euf::sgraph& sg, char_subst const& s, dep_tracker dep) {
        if (!s.m_var) return;

        // replace occurrences of s.m_var with s.m_val in all string constraints
        for (auto &eq : m_str_eq) {
            eq.m_lhs = sg.subst(eq.m_lhs, s.m_var, s.m_val);
            eq.m_rhs = sg.subst(eq.m_rhs, s.m_var, s.m_val);
            eq.sort();
        }
        for (auto &mem : m_str_mem) {
            mem.m_str = sg.subst(mem.m_str, s.m_var, s.m_val);
            mem.m_regex = sg.subst(mem.m_regex, s.m_var, s.m_val);
        }

        const unsigned var_id = s.m_var->id();

        if (s.m_val->is_unit()) {
            // symbolic char → symbolic char: check disequalities
            if (m_char_diseqs.contains(var_id)) {
                const auto& diseqs = m_char_diseqs.find(var_id);
                for (const auto& d : diseqs) {
                    if (d.first == s.m_val) {
                        m_is_general_conflict = true;
                        set_conflict(backtrack_reason::character_range, d.second);
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
                auto& range = m_char_ranges.find(var_id);
                unsigned ch_val = 0;
                seq_util& seq = sg.get_seq_util();
                expr* unit_expr = s.m_val->get_expr();
                expr* ch_expr = nullptr;
                bool have_char = unit_expr && seq.str.is_unit(unit_expr, ch_expr) && seq.is_const_char(ch_expr, ch_val);
                if (have_char && !range.first.contains(ch_val)) {
                    m_is_general_conflict = true;
                    set_conflict(backtrack_reason::character_range, graph().dep_mgr().mk_join(dep, range.second));
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

    nielsen_graph::nielsen_graph(euf::sgraph &sg, simple_solver &solver, simple_solver &core_solver):
        m(sg.get_manager()),
        a(sg.get_manager()),
        m_seq(sg.get_seq_util()),
        m_sg(sg),
        m_solver(solver),
        m_core_solver(core_solver),
        m_parikh(alloc(seq_parikh, sg)),
        m_seq_regex(alloc(seq::seq_regex, sg)) {
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
        SASSERT(n->id() == m_nodes.size() - 1);
        return n;
    }

    nielsen_node* nielsen_graph::mk_child(nielsen_node* parent) {
        nielsen_node* child = mk_node();
        child->clone_from(*parent);
        child->m_parent_ic_count = parent->constraints().size();
        return child;
    }

    nielsen_edge* nielsen_graph::mk_edge(nielsen_node* src, nielsen_node* tgt, bool is_progress) {
        SASSERT(src != nullptr);
        SASSERT(tgt != nullptr);
        nielsen_edge* e = alloc(nielsen_edge, src, tgt, is_progress);
        m_edges.push_back(e);
        src->add_outgoing(e);
        return e;
    }

    void nielsen_graph::add_str_eq(euf::snode* lhs, euf::snode* rhs, smt::enode* l, smt::enode* r) {
        if (!root())
            create_root();
        dep_tracker dep = m_dep_mgr.mk_leaf(enode_pair(l, r));
        str_eq eq(lhs, rhs, dep);
        eq.sort();
        m_root->add_str_eq(eq);
    }

    void nielsen_graph::add_str_mem(euf::snode* str, euf::snode* regex, sat::literal l) {
        if (!root())
            create_root();
        dep_tracker dep = m_dep_mgr.mk_leaf(l);
        euf::snode* history = m_sg.mk_empty_seq(str->get_sort());
        unsigned id = next_mem_id();
        m_root->add_str_mem(str_mem(str, regex, history, id, dep));
    }

    // test-friendly overloads (no external dependency tracking)
    void nielsen_graph::add_str_eq(euf::snode* lhs, euf::snode* rhs) {
        if (!root())
            create_root();
        dep_tracker dep = m_dep_mgr.mk_leaf(enode_pair(nullptr, nullptr));
        str_eq eq(lhs, rhs, dep);
        eq.sort();
        m_root->add_str_eq(eq);
    }

    void nielsen_graph::add_str_mem(euf::snode* str, euf::snode* regex) {
        if (!root())
            create_root();
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
        m_dep_mgr.reset();
        m_solver.reset();
        m_core_solver.reset();
        SASSERT(m_nodes.empty());
        SASSERT(m_edges.empty());
        SASSERT(m_root == nullptr);
        SASSERT(m_sat_node == nullptr);
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
            return t->is_var() || t->is_power();
        });
        if (has_char || !all_eliminable) {
            m_is_general_conflict = true;
            set_conflict(backtrack_reason::symbol_clash, dep);
            return true;
        }
        ast_manager& m = sg.get_manager();
        seq_util& seq = sg.get_seq_util();
        arith_util a(m);
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
                if (seq.str.is_power(e, pow_base, pow_exp) && pow_exp) 
                    add_constraint(constraint(m.mk_eq(pow_exp, a.mk_int(0)), dep, m));
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
        expr* x = nullptr, *y = nullptr;
        rational val;
        // b = (+ a k) ?
        if (arith.is_add(b, x, y)) {
            if (x == a && arith.is_numeral(y, val)) { diff = val; return true; }
            if (y == a && arith.is_numeral(x, val)) { diff = val; return true; }
        }
        // a = (+ b k) → diff = -k
        if (arith.is_add(a, x, y)) {
            if (x == b && arith.is_numeral(y, val)) { diff = -val; return true; }
            if (y == b && arith.is_numeral(x, val)) { diff = -val; return true; }
        }
        // b = (- a k) → diff = -k
        if (arith.is_sub(b, x, y) && x == a && arith.is_numeral(y, val)) { diff = -val; return true; }
        // a = (- b k) → diff = k
        if (arith.is_sub(a, x, y) && x == b && arith.is_numeral(y, val)) { diff = val; return true; }
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
        if (!power->is_power()) return nullptr;
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
        if (tokens.size() < 2) 
            return nullptr;

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

        if (!merged) 
            return nullptr;

        euf::snode* rebuilt = nullptr;
        for (auto tok : result) 
            rebuilt = rebuilt ? sg.mk_concat(rebuilt, tok) : tok;        
        if (!rebuilt) 
            rebuilt = sg.mk_empty_seq(side->get_sort());
        return rebuilt;
    }

    // Simplify constant-exponent powers: base^0 → ε, base^1 → base.
    // Returns new snode if any simplification happened, nullptr otherwise.
    static euf::snode* simplify_const_powers(nielsen_node* node, euf::sgraph& sg, euf::snode* side) {
        SASSERT(side);
        if (side->is_empty())
            return nullptr;

        euf::snode_vector tokens;
        side->collect_tokens(tokens);

        seq_util& seq = sg.get_seq_util();

        bool simplified = false;
        euf::snode_vector result;

        for (euf::snode* tok : tokens) {
            if (tok->is_power()) {
                expr* exp_e = get_power_exp_expr(tok, seq);
                rational ub;
                if (exp_e && node->upper_bound(exp_e, ub)) {
                    if (ub.is_zero()) {
                        // base^0 → ε (skip this token entirely)
                        simplified = true;
                        continue;
                    }
                    if (ub.is_one()) {
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
            // Skip at leading position (i == 0) to avoid undoing power unwinding:
            // unwind produces u · u^(n-1); merging it back to u^n creates an infinite cycle.
            if (i > 0 && t->is_power()) {
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

    simplify_result nielsen_node::simplify_and_init(ptr_vector<nielsen_edge> const& cur_path) {
        if (m_is_extended)
            return simplify_result::proceed;

        euf::sgraph& sg = m_graph.sg();
        ast_manager& m = sg.get_manager();
        seq_util& seq = this->graph().seq();
        bool changed = true;

        // DON'T add rules here that add new constraints or apply substitutions
        // add them to apply_det_modifier instead

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
                        if (m.are_equal(lt->get_expr(), rt->get_expr())) {
                            ++prefix;
                        }
                        else if (sg.are_unit_distinct(lt, rt)) {
                            m_is_general_conflict = true;
                            set_conflict(backtrack_reason::symbol_clash, eq.m_dep);
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
                        if (m.are_equal(lt->get_expr(), rt->get_expr())) {
                            ++suffix;
                        } else if (sg.are_unit_distinct(lt, rt)) {
                            m_is_general_conflict = true;
                            set_conflict(backtrack_reason::symbol_clash, eq.m_dep);
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
            }

            // pass 3: power simplification (mirrors ZIPT's LcpCompression +
            // SimplifyPowerElim + SimplifyPowerSingle)
            for (str_eq& eq : m_str_eq) {
                if (eq.is_trivial() || !eq.m_lhs || !eq.m_rhs)
                    continue;

                // 3a: simplify constant-exponent powers (base^0 → ε, base^1 → base)
                if (euf::snode* s = simplify_const_powers(this, sg, eq.m_lhs))
                    { eq.m_lhs = s; changed = true; }
                if (euf::snode* s = simplify_const_powers(this, sg, eq.m_rhs))
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
                        if (get_const_power_diff(norm_count, pow_exp, m_graph.a, diff)) {
                            count_le_pow = diff.is_nonpos();
                            pow_le_count = diff.is_nonneg();
                        }
                        else if (!cur_path.empty()) {
                            pow_le_count = m_graph.check_lp_le(pow_exp, norm_count);
                            count_le_pow = m_graph.check_lp_le(norm_count, pow_exp);
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
                            expr_ref rem = normalize_arith(m, m_graph.a.mk_sub(norm_count, pow_exp));
                            expr_ref pw(seq.str.mk_power(base_e, rem), m);
                            other_side = dir_concat(sg, sg.mk(pw), other_side, fwd);
                        }
                        else {
                            // count <= pow: remainder goes to pow_side
                            expr_ref rem = normalize_arith(m, m_graph.a.mk_sub(pow_exp, norm_count));
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
                    if (lp && rp && get_const_power_diff(rp, lp, m_graph.a, diff)) {
                        // rp = lp + diff (constant difference)
                        eq.m_lhs = dir_drop(sg, eq.m_lhs, 1, fwd);
                        eq.m_rhs = dir_drop(sg, eq.m_rhs, 1, fwd);
                        if (diff.is_pos()) {
                            // rp > lp: put base^diff on RHS (direction-aware prepend/append)
                            expr_ref de(m_graph.a.mk_int(diff), m);
                            expr_ref pw(seq.str.mk_power(lb, de), m);
                            eq.m_rhs = dir_concat(sg, sg.mk(pw), eq.m_rhs, fwd);
                        }
                        else if (diff.is_neg()) {
                            // lp > rp: put base^(-diff) on LHS
                            expr_ref de(m_graph.a.mk_int(-diff), m);
                            expr_ref pw(seq.str.mk_power(lb, de), m);
                            eq.m_lhs = dir_concat(sg, sg.mk(pw), eq.m_lhs, fwd);
                        }
                        // diff == 0: both powers cancel completely
                        changed = true;
                    }
                    // 3e: LP-aware power directional elimination
                    else if (lp && rp && !cur_path.empty()) {
                        bool lp_le_rp = m_graph.check_lp_le(lp, rp);
                        bool rp_le_lp = m_graph.check_lp_le(rp, lp);
                        if (lp_le_rp || rp_le_lp) {
                            expr* smaller_exp = lp_le_rp ? lp : rp;
                            expr* larger_exp  = lp_le_rp ? rp : lp;
                            eq.m_lhs = dir_drop(sg, eq.m_lhs, 1, fwd);
                            eq.m_rhs = dir_drop(sg, eq.m_rhs, 1, fwd);
                            if (lp_le_rp && rp_le_lp) {
                                // both ≤ -> equal -> both cancel completely
                                add_constraint(m_graph.mk_constraint(m.mk_eq(lp, rp), eq.m_dep));
                            }
                            else {
                                // we only know for sure that one is smaller than the other
                                expr_ref d(m_graph.mk_fresh_int_var());
                                expr_ref zero_e(m_graph.a.mk_int(0), m);
                                expr_ref d_plus_smaller(m_graph.a.mk_add(d, smaller_exp), m);
                                add_constraint(m_graph.mk_constraint(m_graph.a.mk_ge(d, zero_e), eq.m_dep));
                                add_constraint(m_graph.mk_constraint(m.mk_eq(d_plus_smaller, larger_exp), eq.m_dep));
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
                        set_conflict(backtrack_reason::regex, mem.m_dep);
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

        // consume symbolic characters via uniform derivatives
        for (str_mem& mem : m_str_mem) {
            SASSERT(mem.m_str && mem.m_regex);
            if (mem.is_primitive())
                continue;
            while (mem.m_str && !mem.m_str->is_empty()) {

                // TODO: generalize this to work for reverse derivative as well.
                euf::snode *tok = mem.m_str->first();
                if (!tok || !tok->is_char_or_unit())
                    break;

                seq_rewriter rw(m);
                expr_ref d(rw.mk_derivative(mem.m_regex->get_expr()), m);

                // Extract the inner char expression from seq.unit(?inner)
                expr *inner_char = tok->arg(0)->get_expr();
               
                // substitute the inner char for the derivative variable in d
                var_subst vs(m);
                d = vs(d, inner_char);

                th_rewriter thrw(m);
                thrw(d);

                auto next = sg.mk(d);
                if (next->is_fail()) {
                    m_is_general_conflict = true;
                    set_conflict(backtrack_reason::regex, mem.m_dep);
                    return simplify_result::conflict;
                }

                mem.m_str = sg.drop_left(mem.m_str, 1);
                mem.m_regex = next;
                mem.m_history = sg.mk_concat(mem.m_history, tok);
            }
        }

        // check for regex memberships that are immediately infeasible
        for (str_mem& mem : m_str_mem) {
            if (mem.is_contradiction()) {
                m_is_general_conflict = true;
                set_conflict(backtrack_reason::regex, mem.m_dep);
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
            dep_tracker dep = mem.m_dep;
            if (m_graph.check_regex_widening(*this, mem.m_str, mem.m_regex, dep)) {
                m_is_general_conflict = true;
                set_conflict(backtrack_reason::regex, dep);
                return simplify_result::conflict;
            }
        }


        if (is_satisfied()) {
            // pass 1 removed all trivial str_eq entries; is_satisfied() requires
            // the remainder to be trivial, so the vector must be empty here.
            SASSERT(m_str_eq.empty());
            return simplify_result::satisfied;
        }
        return simplify_result::proceed;
    }

    bool nielsen_node::is_satisfied() const {
        if (any_of(m_str_eq, [](auto const &eq) { return !eq.is_trivial(); }))
            return false;
        if (any_of(m_str_mem, [](auto const &m) { return !m.is_trivial() && !m.is_primitive();}))
            return false;
        return true;
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
        str_mem const* confl_cnstr;
        if (!node.is_currently_conflict() && (confl_cnstr = m_parikh->check_parikh_conflict(node)) != nullptr) {
            node.set_general_conflict(true);
            node.set_conflict(backtrack_reason::parikh_image, confl_cnstr->m_dep);
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
            m_root->add_constraint(lc.to_constraint());
        }
    }

    template<typename T> class scoped_push {
        T &t;
    public:
        scoped_push(T& t) : t(t) {
            t.push_scope();
        }
        ~scoped_push() {
            t.pop_scope(1);
        }
    };

    nielsen_graph::search_result nielsen_graph::solve() {
        SASSERT(m_root);

        try {
            ++m_stats.m_num_solve_calls;
            m_sat_node = nullptr;
            m_sat_path.reset();
            m_conflict_sources.reset();

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
                    IF_VERBOSE(1, display(verbose_stream()));
#endif
                    break;
                }
                if (m_max_search_depth > 0 && m_depth_bound > m_max_search_depth)
                    break;
                inc_run_idx();
                ptr_vector<nielsen_edge> cur_path;
                // scoped_push _scoped_push(m_dep_mgr); // gc dependencies after search
                const search_result r = search_dfs(m_root, cur_path);
                IF_VERBOSE(1, verbose_stream()
                                  << " depth_bound=" << m_depth_bound << " dfs_nodes=" << m_stats.m_num_dfs_nodes
                                  << " max_depth=" << m_stats.m_max_depth << " extensions=" << m_stats.m_num_extensions
                                  << " arith_prune=" << m_stats.m_num_arith_infeasible << " result="
                                  << (r == search_result::sat     ? "SAT"
                                      : r == search_result::unsat ? "UNSAT"
                                                                  : "UNKNOWN")
                                  << "\n";);
                if (r == search_result::sat) {
                    IF_VERBOSE(
                        1,
                        verbose_stream() << "side constraints: \n";
                        for (auto const &c : cur_path.back()->side_constraints()) {
                            verbose_stream() << "  side constraint: " << c.fml << "\n";
                        });
                    ++m_stats.m_num_sat;
                    SASSERT(m_sat_node != nullptr);
                    return r;
                }
                if (r == search_result::unsat) {
                    ++m_stats.m_num_unsat;
                    auto deps = collect_conflict_deps();
                    m_dep_mgr.linearize(deps, m_conflict_sources);
                    return r;
                }
                // depth limit hit – double the bound and retry
                m_depth_bound *= 2;
                SASSERT(m_depth_bound < INT_MAX);
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

    nielsen_graph::search_result nielsen_graph::search_dfs(nielsen_node* node,
        ptr_vector<nielsen_edge>& cur_path, unsigned depth) {

        ++m_stats.m_num_dfs_nodes;
        // std::cout << m_stats.m_num_dfs_nodes << std::endl;
        // depth is NOT necessarily the length of the path
        // Reason: Progress nodes are not counted towards the depth limit
        // Otw. problems with a lot of variables would barely terminate
        SASSERT(depth <= cur_path.size());
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
        // we might need to tell the SAT solver about the new integer inequalities
        // that might have been added by an extension step
        assert_node_new_int_constraints(node);

        // simplify constraints (idempotent after first call)
        const simplify_result sr = node->simplify_and_init(cur_path);

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

        if (node->is_currently_conflict())
            return search_result::unsat;

        // integer feasibility check: the solver now holds all path constraints
        // incrementally; just query the solver directly
        if (!cur_path.empty() && !check_int_feasibility()) {
            dep_tracker dep = get_subsolver_dependency(node);
            node->set_conflict(backtrack_reason::arithmetic, dep);
            node->set_general_conflict(true);
            ++m_stats.m_num_arith_infeasible;
            return search_result::unsat;
        }

        SASSERT(sr != simplify_result::satisfied || node->is_satisfied());
        SASSERT(!node->is_currently_conflict());

        if (node->is_satisfied()) {
            // Before declaring SAT, check leaf-node regex feasibility:
            // for each variable with multiple regex constraints, verify
            // that the intersection of all its regexes is non-empty.
            // Mirrors ZIPT NielsenNode.CheckRegex.
            dep_tracker dep;
            if (!check_leaf_regex(*node, dep)) {
                node->set_general_conflict(true);
                node->set_conflict(backtrack_reason::regex, dep);
                return search_result::unsat;
            }
            m_sat_node = node;
            m_sat_path = cur_path;
            return search_result::sat;
        }

        // depth bound check
        if (depth >= m_depth_bound)
            return search_result::unknown;

        SASSERT(!node->is_currently_conflict());

        // generate extensions only once per node; children persist across runs
        if (!node->is_extended()) {
            bool ext = generate_extensions(node);
            IF_VERBOSE(1, display(verbose_stream(), node));
            CTRACE(seq, !ext, display(tout, node) << to_dot() << "\n");
            if (!ext) {
                node->to_html(std::cout, m);
                std::cout << std::endl;
                display(std::cout, node);
            }
            VERIFY(ext);
            node->set_extended(true);
            ++m_stats.m_num_extensions;
        }

        SASSERT(!node->is_currently_conflict());

        // explore children
        bool any_unknown = false;
        for (nielsen_edge *e : node->outgoing()) {
            cur_path.push_back(e);
            // Push a solver scope for this edge and assert its side integer
            // constraints.  The child's own new constraints will be asserted
            // inside the recursive call (above).  On return, pop the scope so
            // that backtracking removes those assertions.
            m_solver.push();

            // Lazily compute substitution length constraints (|x| = |u|) on first
            // traversal. This must happen before asserting side_constraints and before
            // bumping mod counts, so that LHS uses the parent's counts and RHS
            // uses the temporarily-bumped counts.
            if (!e->len_constraints_computed()) {
                add_subst_length_constraints(e);
                e->set_len_constraints_computed(true);

                for (const auto& sc : e->side_constraints()) {
                    e->tgt()->add_constraint(sc);
                }
            }

            // Bump modification counts for the child's context.
            inc_edge_mod_counts(e);

            const search_result r = search_dfs(e->tgt(), cur_path,
                e->is_progress() ? depth : (depth + 1)
            );

            // Restore modification counts on backtrack.
            dec_edge_mod_counts(e);

            m_solver.pop(1);
            if (r == search_result::sat)
                return search_result::sat;
            cur_path.pop_back();
            if (r == search_result::unknown)
                any_unknown = true;
        }

        if (!any_unknown) {
            node->set_child_conflict();
            return search_result::unsat;
        }
        return search_result::unknown;
    }

    // Returns true if variable snode `var` appears anywhere in the token list of `n`.
    static bool snode_contains_var(euf::snode const* n, euf::snode const* var) {
        SASSERT(n && var);
        euf::snode_vector tokens;
        n->collect_tokens(tokens);
        return any_of(tokens, [var](auto const &t) { return t == var; });
    }

    bool nielsen_graph::apply_det_modifier(nielsen_node* node) {
        // resist the temptation to add rules that "simplify" primitive membership constraints!
        // pretty much all of them could cause divergence!
        // e.g., x \in aa* => don't apply substitution x / ax even though it looks "safe" to do
        // there might be another constraint x \in a* and they would just push the "a" back and forth!

        for (unsigned eq_idx = 0; eq_idx < node->str_eqs().size(); ++eq_idx) {
            str_eq const& eq = node->str_eqs()[eq_idx];
            if (eq.is_trivial())
                continue; // We should have simplified it away before
            auto l = eq.m_lhs, r = eq.m_rhs;
            if (!l || !r)
                continue;

            // 1. unit equalities produced by unit-unit prefix/suffix splits
            {
                euf::snode_vector lhs_toks, rhs_toks;
                l->collect_tokens(lhs_toks);
                r->collect_tokens(rhs_toks);

                // --- prefix ---
                unsigned prefix = 0;
                while (prefix < lhs_toks.size() && prefix < rhs_toks.size()) {
                    euf::snode* lt = lhs_toks[prefix];
                    euf::snode* rt = rhs_toks[prefix];
                    if (m.are_equal(lt->get_expr(), rt->get_expr()))
                        ++prefix;
                    else if (m_sg.are_unit_distinct(lt, rt))
                        break;
                    else if (lt->is_char_or_unit() && rt->is_char_or_unit()) {
                        nielsen_node* child = mk_child(node);
                        nielsen_edge* e = mk_edge(node, child, true);

                        if (lt->is_char()) {
                            std::swap(lt, rt);
                            std::swap(l, r);
                        }
                        SASSERT(lt->is_unit());

                        euf::snode* lhs_rest = m_sg.drop_left(l, prefix + 1);
                        euf::snode* rhs_rest = m_sg.drop_left(r, prefix + 1);

                        auto& eqs = child->str_eqs();
                        eqs[eq_idx] = eqs.back();
                        eqs.pop_back();

                        if (lt->is_char())
                            std::swap(lt, rt);
                        nielsen_subst subst(lt, rt, eq.m_dep);
                        e->add_subst(subst);
                        child->apply_subst(m_sg, subst);

                        if (!lhs_rest->is_empty() && !rhs_rest->is_empty())
                            eqs.push_back(str_eq(lhs_rest, rhs_rest, eq.m_dep));
                        return true;
                    }
                    else
                        break;
                }

                // --- suffix ---
                unsigned lsz = lhs_toks.size(), rsz = rhs_toks.size();
                unsigned suffix = 0;
                while (suffix < lsz - prefix && suffix < rsz - prefix) {
                    euf::snode* lt = lhs_toks[lsz - 1 - suffix];
                    euf::snode* rt = rhs_toks[rsz - 1 - suffix];
                    if (m.are_equal(lt->get_expr(), rt->get_expr()))
                        ++suffix;
                    else if (m_sg.are_unit_distinct(lt, rt))
                        break;
                    else if (lt->is_char_or_unit() && rt->is_char_or_unit()) {
                        nielsen_node* child = mk_child(node);
                        nielsen_edge* e = mk_edge(node, child, true);

                        euf::snode* lhs_rest = m_sg.drop_right(l, suffix + 1);
                        euf::snode* rhs_rest = m_sg.drop_right(r, suffix + 1);

                        auto& eqs = child->str_eqs();
                        eqs[eq_idx] = eqs.back();
                        eqs.pop_back();

                        if (lt->is_char())
                            std::swap(lt, rt);
                        nielsen_subst subst(lt, rt, eq.m_dep);
                        e->add_subst(subst);
                        child->apply_subst(m_sg, subst);

                        if (!lhs_rest->is_empty() && !rhs_rest->is_empty())
                            eqs.push_back(str_eq(lhs_rest, rhs_rest, eq.m_dep));
                        return true;
                    }
                    else
                        break;
                }
            }

            // 2. power-character directional inconsistency
            for (unsigned od = 0; od < 2; ++od) {
                bool fwd = (od == 0);
                euf::snode* lh = dir_token(l, fwd);
                euf::snode* rh = dir_token(r, fwd);
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
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, true);
                    nielsen_subst s(pow_head, m_sg.mk_empty_seq(pow_head->get_sort()), eq.m_dep);
                    e->add_subst(s);
                    child->apply_subst(m_sg, s);
                    expr* pow_exp = get_power_exp_expr(pow_head, m_seq);
                    if (pow_exp) {
                        expr *zero = a.mk_int(0);
                        e->add_side_constraint(mk_constraint(m.mk_eq(pow_exp, zero), eq.m_dep));
                    }
                    return true;
                }
            }

            // 3. variable-character look-ahead substitution
            for (unsigned od = 0; od < 2; ++od) {
                bool fwd = od == 0;

                euf::snode* var_side = nullptr;
                euf::snode* char_side = nullptr;
                euf::snode* lhead = dir_token(l, fwd);
                euf::snode* rhead = dir_token(r, fwd);
                if (!lhead || !rhead) continue;

                if (lhead->is_var() && rhead->is_char()) {
                    var_side = l;
                    char_side = r;
                }
                else if (rhead->is_var() && lhead->is_char()) {
                    var_side = r;
                    char_side = l;
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

                unsigned i = 0;
                for (; i < char_toks.size() && char_toks[i]->is_char(); ++i) {
                    unsigned j1 = 1;
                    unsigned j2 = i;
                    bool failed = false;

                    while (j1 < var_toks.size() && j2 < char_toks.size()) {
                        euf::snode* st1 = var_toks[j1];
                        euf::snode* st2 = char_toks[j2];

                        if (!st2->is_char()) break;
                        if (st1->is_char()) {
                            if (st1->id() == st2->id()) {
                                j1++; j2++;
                                continue;
                            }
                            failed = true; break;
                        }
                        if (st1->id() != var_node->id()) break;

                        bool inner_indet = false;
                        for (unsigned l_idx = 0; j2 < char_toks.size() && l_idx < i; ++l_idx) {
                            st2 = char_toks[j2];
                            if (!st2->is_char()) {
                                inner_indet = true; break;
                            }
                            if (st2->id() == char_toks[l_idx]->id()) {
                                j2++; continue;
                            }
                            failed = true; break;
                        }
                        if (inner_indet || failed) break;
                        j1++;
                    }

                    if (failed) continue;
                    break;
                }

                if (i == 0) continue;

                bool skip_dir = false;
                euf::snode* next_var = nullptr;
                for (unsigned k = i; k < char_toks.size(); ++k) {
                    euf::snode* t = char_toks[k];
                    if (t->is_power()) {
                        skip_dir = true;
                        break;
                    }
                    if (t->is_var()) {
                        next_var = t;
                        break;
                    }
                }
                if (skip_dir) continue;

                if (next_var) {
                    u_map<unsigned> dep_edges;
                    for (str_eq const& other_eq : node->str_eqs()) {
                        if (other_eq.is_trivial() || !other_eq.m_lhs || !other_eq.m_rhs)
                            continue;
                        euf::snode* lh2 = dir_token(other_eq.m_lhs, fwd);
                        euf::snode* rh2 = dir_token(other_eq.m_rhs, fwd);
                        if (!lh2 || !rh2) continue;

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
                        else if (lh2->is_var() && !rh2->is_var()) record_dep(lh2, other_eq.m_rhs);
                        else if (rh2->is_var() && !lh2->is_var()) record_dep(rh2, other_eq.m_lhs);
                    }

                    uint_set visited;
                    svector<unsigned> worklist;
                    worklist.push_back(next_var->id());
                    bool cycle_found = false;
                    while (!worklist.empty() && !cycle_found) {
                        unsigned cur = worklist.back();
                        worklist.pop_back();
                        if (cur == var_node->id()) {
                            cycle_found = true; break;
                        }
                        if (visited.contains(cur)) continue;
                        visited.insert(cur);
                        unsigned dep_id;
                        if (dep_edges.find(cur, dep_id))
                            worklist.push_back(dep_id);
                    }
                    if (cycle_found) continue;
                }

                euf::snode* prefix_sn = char_toks[0];
                for (unsigned j = 1; j < i; ++j) {
                    prefix_sn = dir_concat(m_sg, prefix_sn, char_toks[j], fwd);
                }
                euf::snode* replacement = dir_concat(m_sg, prefix_sn, var_node, fwd);
                nielsen_subst s(var_node, replacement, eq.m_dep);
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
                return true;
            }

            // variable definition: x = t where x is a single var and x ∉ vars(t)
            // → deterministically substitute x → t throughout the node
            euf::snode* var = nullptr;
            euf::snode* def;

            if (l->is_var() && !snode_contains_var(r, l)) {
                var = l;
                def = r;
            }
            else if (r->is_var() && !snode_contains_var(l, r)) {
                var = r;
                def = l;
            }
            else if (l->is_unit() && l->arg(0)->is_var() && r->is_char_or_unit()) {
                var = l->arg(0);
                def = r->arg(0);
            }
            else if (r->is_unit() && r->arg(0)->is_var() && l->is_char_or_unit()) {
                var = r->arg(0);
                def = l->arg(0);
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
                euf::snode* char_head = lhead->is_char_or_unit() ? lhead : (rhead->is_char_or_unit() ? rhead : nullptr);
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
        if (tok->is_char_or_unit())
            return false;
        // Variables and powers have symbolic/unknown length.
        if (tok->is_var() || tok->is_power())
            return true;
        // For s_var string literals: check if it's a string literal (known constant length).
        if (tok->get_expr()) {
            zstring s;
            if (m_seq.str.is_string(tok->get_expr(), s))
                return false;
        }
        // Everything else is treated as variable length.
        return true;
    }

    unsigned nielsen_graph::token_const_length(euf::snode* tok) const {
        if (tok->is_char_or_unit())
            return 1;
        if (tok->get_expr()) {
            zstring s;
            if (m_seq.str.is_string(tok->get_expr(), s))
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
            th_rewriter rw(m);
          

            euf::snode* pad = nullptr;
            if (padding != 0) {
                expr *pad_var = skolem(m, rw).mk("eq-split", a.mk_int(padding), eq.m_lhs->get_expr(),
                                                 eq.m_rhs->get_expr(), eq.m_lhs->get_sort()); 
                pad = m_sg.mk(pad_var);
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
                expr_ref len_pad(m_seq.str.mk_length(pad->get_expr()), m);
                expr_ref abs_pad(a.mk_int(std::abs(padding)), m);
                e->add_side_constraint(mk_constraint(m.mk_eq(len_pad, abs_pad), eq.m_dep));
            }
            // 2) len(eq1_lhs) = len(eq1_rhs)
            expr_ref l1 = compute_length_expr(eq1_lhs);
            expr_ref r1 = compute_length_expr(eq1_rhs);
            e->add_side_constraint(mk_constraint(m.mk_eq(l1, r1), eq.m_dep));

            // 3) len(eq2_lhs) = len(eq2_rhs)
            expr_ref l2 = compute_length_expr(eq2_lhs);
            expr_ref r2 = compute_length_expr(eq2_rhs);
            e->add_side_constraint(mk_constraint(m.mk_eq(l2, r2), eq.m_dep));

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

    bool nielsen_graph::generate_extensions(nielsen_node *node) {
        SASSERT(node != nullptr);
        SASSERT(!node->is_currently_conflict());
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
        // if (apply_star_intr(node))
        //     return ++m_stats.m_mod_star_intr, true;

        // Priority 7: GPowerIntr - ground power introduction
        if (apply_gpower_intr(node))
            return ++m_stats.m_mod_gpower_intr, true;
        
        // Priority 8: Regex Factorization (Boolean Closure)
        if (apply_regex_factorization(node))
            return ++m_stats.m_mod_regex_factorization, true;

        // Priority 8b: ConstNielsen - char vs var (2 children)
        if (apply_const_nielsen(node))
            return ++m_stats.m_mod_const_nielsen, true;
        
        // Priority 9: RegexIfSplit - split str_mem s ∈ ite(c,th,el) by branching on c
        if (apply_regex_if_split(node))
            return ++m_stats.m_mod_regex_if_split, true;

        // Priority 9b: SignatureSplit - heuristic string equation splitting
        if (m_signature_split && apply_signature_split(node))
            return ++m_stats.m_mod_signature_split, true;

        // Priority 10: RegexVarSplit - split str_mem by minterms
        if (apply_regex_var_split(node))
            return ++m_stats.m_mod_regex_var_split, true;

        // Priority 11: PowerSplit - power unwinding with bounded prefix
        if (apply_power_split(node))
            return ++m_stats.m_mod_power_split, true;

        // Priority 12: VarNielsen - var vs var, all progress (classic Nielsen)
        if (apply_var_nielsen(node))
            return ++m_stats.m_mod_var_nielsen, true;

        // Priority 13: VarNumUnwinding - variable power unwinding for equality constraints
        if (apply_var_num_unwinding_eq(node))
            return ++m_stats.m_mod_var_num_unwinding_eq, true;

        // Priority 14: variable power unwinding for membership constraints
        if (apply_var_num_unwinding_mem(node))
            return ++m_stats.m_mod_var_num_unwinding_mem, true;

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
            SASSERT(eq.m_lhs && eq.m_rhs && !eq.is_trivial());

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

    bool nielsen_graph::find_power_vs_var(nielsen_node* node,
                                          euf::snode*& power,
                                          str_mem const*& mem_out,
                                          bool& fwd) const {
        for (str_mem const& mem : node->str_mems()) {
            SASSERT(mem.m_str && mem.m_regex && !mem.is_trivial());

            for (unsigned od = 0; od < 2; ++od) {
                bool local_fwd = (od == 0);
                euf::snode* lhead = dir_token(mem.m_str, local_fwd);
                if (lhead && lhead->is_power()) {
                    power = lhead;
                    mem_out = &mem;
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
                if (lhead->arg(0) != rhead->arg(0))
                    continue;

                // Skip if the exponents differ by a constant — simplify_and_init's
                // directional power elimination already handles that case.
                expr* exp_m = get_power_exponent(lhead);
                expr* exp_n = get_power_exponent(rhead);
                if (!exp_m || !exp_n)
                    continue;
                rational diff;
                SASSERT(!get_const_power_diff(exp_n, exp_m, a, diff)); // handled by simplification

                // Branch 1 (explored first): n < m  (add constraint c ≥ p + 1)
                {
                    nielsen_edge *e = mk_edge(node, mk_child(node), true);
                    expr_ref n_plus_1(a.mk_add(exp_n, a.mk_int(1)), m);
                    e->add_side_constraint(mk_constraint(a.mk_ge(exp_m, n_plus_1), eq.m_dep));
                }
                // Branch 2 (explored second): m <= n  (add constraint p ≥ c)
                {
                    nielsen_edge *e = mk_edge(node, mk_child(node), true);
                    e->add_side_constraint(mk_constraint(a.mk_ge(exp_n, exp_m), eq.m_dep));
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

        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial())
                continue;
            // NB: Shuvendu - this test is always false based on how str_eqs are constructed
            // it can be an assertion to force the invariant that str_eqs always have both sides non-null.          
            if (!eq.m_lhs || !eq.m_rhs)
                continue;

            for (int side = 0; side < 2; ++side) {
                euf::snode* pow_side   = (side == 0) ? eq.m_lhs : eq.m_rhs;
                euf::snode* other_side = (side == 0) ? eq.m_rhs : eq.m_lhs;
                // NB: Shuvendu - this test is always false
                if (!pow_side || !other_side)
                    continue;

                for (unsigned od = 0; od < 2; ++od) {
                    bool fwd = od == 0;
                    euf::snode* end_tok = dir_token(pow_side, fwd);
                    if (!end_tok || !end_tok->is_power())
                        continue;
                    euf::snode* base_sn = end_tok->arg(0);
                    expr* pow_exp = get_power_exp_expr(end_tok, m_seq);
                    // NB: Shuvendu - this test is also redundant
                    if (!base_sn || !pow_exp)
                        continue;

                    auto [count, consumed] = comm_power(base_sn, other_side, m, m_seq, fwd);
                    if (!count.get() || consumed == 0)
                        continue;

                    expr_ref norm_count = normalize_arith(m, count);

                    // Skip if ordering is already deterministic — simplify_and_init
                    // pass 3c should have handled it.
                    rational diff;
                    if (get_const_power_diff(norm_count, pow_exp, a, diff))
                        continue;

                    // Branch 1: pow_exp < count (i.e., count >= pow_exp + 1)
                    {
                        nielsen_edge *e = mk_edge(node, mk_child(node), true);
                        expr_ref pow_plus1(a.mk_add(pow_exp, a.mk_int(1)), m);
                        e->add_side_constraint(mk_constraint(a.mk_ge(norm_count, pow_plus1), eq.m_dep));
                    }
                    // Branch 2: count <= pow_exp (i.e., pow_exp >= count)
                    {
                        nielsen_edge *e = mk_edge(node, mk_child(node), true);
                        e->add_side_constraint(mk_constraint(a.mk_ge(pow_exp, norm_count), eq.m_dep));
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

        euf::snode *power = nullptr;
        euf::snode *other_head = nullptr;
        str_eq const *eq = nullptr;
        bool fwd = true;
        if (!find_power_vs_non_var(node, power, other_head, eq, fwd))
            return false;

        SASSERT(power->is_power() && power->num_args() >= 1);
        euf::snode *base = power->arg(0);
        expr *exp_n = get_power_exponent(power);
        expr *zero = a.mk_int(0);
        expr *one = a.mk_int(1);

        // Branch 1 (explored first): n = 0 → replace power with ε (progress)
        // Side constraint: n = 0
        nielsen_node *child = mk_child(node);
        nielsen_edge *e = mk_edge(node, child, true);
        nielsen_subst s1(power, m_sg.mk_empty_seq(power->get_sort()), eq->m_dep);
        e->add_subst(s1);
        child->apply_subst(m_sg, s1);
        if (exp_n)
            e->add_side_constraint(mk_constraint(m.mk_eq(exp_n, zero), eq->m_dep));

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
        expr_ref n_minus_1 = normalize_arith(m, a.mk_sub(exp_n, one));
        expr_ref nested_pow(seq.str.mk_power(base_expr, n_minus_1), m);
        euf::snode* nested_power_snode = m_sg.mk(nested_pow);

        euf::snode* replacement = dir_concat(m_sg, base, nested_power_snode, fwd);
        child = mk_child(node);
        e = mk_edge(node, child, true);
        nielsen_subst s2(power, replacement, eq->m_dep);
        e->add_subst(s2);
        child->apply_subst(m_sg, s2);
        if (exp_n)
            e->add_side_constraint(mk_constraint(a.mk_ge(exp_n, one), eq->m_dep));

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
        return false;
        // Only fire if a backedge was set (cycle detected)
        if (!node->backedge())
            return false;

        // Look for a str_mem with a variable-headed string
        for (unsigned mi = 0; mi < node->str_mems().size(); ++mi) {
            str_mem const& mem = node->str_mems()[mi];
            if (!mem.m_str || !mem.m_regex) 
                continue;
            if (mem.is_primitive()) 
                continue;
            euf::snode* first = mem.m_str->first();
            if (!first || !first->is_var()) 
                continue;

            euf::snode* x = first;
            expr* re_expr = mem.m_regex->get_expr();
            if (!re_expr)
                continue;
            expr *str_expr = mem.m_str->get_expr();

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
            SASSERT(stab_base);

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
            expr_ref star_re(m_seq.re.mk_star(stab_expr), m);
            euf::snode* star_sn = m_sg.mk(star_re);
            if (!star_sn)
                continue;

            // Try subsumption: if L(x_range) ⊆ L(stab_star), drop the constraint
            if (m_seq_regex && m_seq_regex->try_subsume(mem, *node))
                continue;

            // Create child: x → pr · po
            
            th_rewriter rw(m);
            auto pr_e = skolem(m, rw).mk("star-intro-left", str_expr, re_expr, str_expr->get_sort());
            auto po_e = skolem(m, rw).mk("star-intro-right", str_expr, re_expr, str_expr->get_sort());
            euf::snode *pr = m_sg.mk(pr_e);
            euf::snode *po = m_sg.mk(po_e);
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
                sort* str_sort = m_seq.str.mk_string_sort();
                expr_ref full_seq(m_seq.re.mk_full_seq(m_seq.re.mk_re(str_sort)), m);
                expr_ref base_then_all(m_seq.re.mk_concat(stab_expr, full_seq), m);
                expr_ref block_re(m_seq.re.mk_complement(base_then_all), m);
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

    // -----------------------------------------------------------------------
    // Modifier: apply_regex_factorization (Boolean Closure)
    // -----------------------------------------------------------------------

    struct tau_pair {
        expr_ref m_p;
        expr_ref m_q;
        tau_pair(expr* p, expr* q, ast_manager& m) : m_p(p, m), m_q(q, m) {
            SASSERT(p);
            SASSERT(q);
        }
    };
    typedef vector<tau_pair> tau_pairs;

    static void compute_tau(ast_manager& m, seq_util& seq, euf::sgraph& sg, expr* r, tau_pairs& result) {
        SASSERT(r);
        sort* str_sort = nullptr;
        if (!seq.is_re(r, str_sort)) return;
        expr *body = nullptr;

        if (seq.re.is_epsilon(r)) {
            expr_ref eps(seq.re.mk_epsilon(str_sort), m);
            result.push_back(tau_pair(eps, eps, m));
        }
        else if (seq.str.is_unit(r) || seq.str.is_string(r) || seq.re.is_range(r) || seq.re.is_full_char(r) ||
                 (seq.re.is_to_re(r) && seq.str.is_string(to_app(r)->get_arg(0)))) {
            if (seq.re.is_to_re(r)) {
                expr* arg = to_app(r)->get_arg(0);
                zstring s;
                if (seq.str.is_string(arg, s) && s.length() > 1) {
                    for (unsigned i = 0; i <= s.length(); ++i) {
                        expr_ref p(seq.re.mk_to_re(seq.str.mk_string(s.extract(0, i))), m);
                        expr_ref q(seq.re.mk_to_re(seq.str.mk_string(s.extract(i, s.length() - i))), m);
                        result.push_back(tau_pair(p, q, m));
                    }
                    return;
                }
            }
            expr_ref eps(seq.re.mk_epsilon(str_sort), m);
            result.push_back(tau_pair(eps, r, m));
            result.push_back(tau_pair(r, eps, m));
        }
        else if (seq.re.is_empty(r)) {
            // empty set has no splits
        }
        else if (seq.re.is_union(r)) {
            for (expr* arg : *to_app(r)) {
                compute_tau(m, seq, sg, arg, result);
            }
        }
        else if (seq.re.is_concat(r)) {
            unsigned num_args = to_app(r)->get_num_args();
            if (num_args == 0) {
                expr_ref eps(seq.re.mk_epsilon(str_sort), m);
                result.push_back(tau_pair(eps, eps, m));
                return;
            }
            for (unsigned i = 0; i < num_args; ++i) {
                tau_pairs tau_arg;
                compute_tau(m, seq, sg, to_app(r)->get_arg(i), tau_arg);
                
                expr_ref left(m);
                expr_ref right(m);
                
                if (i == 0) left = seq.re.mk_epsilon(str_sort);
                else {
                    expr_ref_vector left_args(m);
                    for (unsigned j = 0; j < i; ++j) left_args.push_back(to_app(r)->get_arg(j));
                    if (left_args.size() == 1) left = left_args.get(0);
                    else left = m.mk_app(seq.get_family_id(), OP_RE_CONCAT, left_args.size(), left_args.data());
                }

                if (i == num_args - 1) right = seq.re.mk_epsilon(str_sort);     
                else {
                    expr_ref_vector right_args(m);
                    for (unsigned j = i + 1; j < num_args; ++j) right_args.push_back(to_app(r)->get_arg(j));
                    if (right_args.size() == 1) right = right_args.get(0);
                    else right = m.mk_app(seq.get_family_id(), OP_RE_CONCAT, right_args.size(), right_args.data());
                }

                for (auto const& pair : tau_arg) {
                    expr_ref p(m), q(m);
                    if (seq.re.is_epsilon(left)) p = pair.m_p;
                    else if (seq.re.is_epsilon(pair.m_p)) p = left;
                    else p = seq.re.mk_concat(left, pair.m_p);
                    
                    if (seq.re.is_epsilon(right)) q = pair.m_q;
                    else if (seq.re.is_epsilon(pair.m_q)) q = right;
                    else q = seq.re.mk_concat(pair.m_q, right);
                    
                    result.push_back(tau_pair(p, q, m));
                }
            }
        }
        else if (seq.re.is_star(r, body) || seq.re.is_plus(r, body)) {
            if (seq.re.is_plus(r)) {
                expr_ref star(seq.re.mk_star(body), m);
                expr_ref concat(seq.re.mk_concat(body, star), m);
                compute_tau(m, seq, sg, concat, result);
                return;
            }
            
            expr_ref eps(seq.re.mk_epsilon(str_sort), m);
            result.push_back(tau_pair(eps, eps, m));
            
            tau_pairs tau_body;
            compute_tau(m, seq, sg, body, tau_body);
            for (auto const& pair : tau_body) {
                expr_ref p(m), q(m);
                if (seq.re.is_epsilon(pair.m_p)) p = r;
                else p = seq.re.mk_concat(r, pair.m_p); 
                
                if (seq.re.is_epsilon(pair.m_q)) q = r;
                else q = seq.re.mk_concat(pair.m_q, r); 
                
                result.push_back(tau_pair(p, q, m));
            }
        }
        else if (seq.re.is_opt(r, body)) {
            expr_ref eps(seq.re.mk_epsilon(str_sort), m);
            result.push_back(tau_pair(eps, eps, m));
            compute_tau(m, seq, sg, body, result);
        }
        else {
            expr_ref eps(seq.re.mk_epsilon(str_sort), m);
            result.push_back(tau_pair(eps, r, m));
            result.push_back(tau_pair(r, eps, m));
        }
    }

    bool nielsen_graph::apply_regex_factorization(nielsen_node* node) {
        if (!m_regex_factorization)
            return false;

        for (str_mem const& mem : node->str_mems()) {
            SASSERT(mem.m_str && mem.m_regex);
            
            if (mem.is_primitive() || !mem.m_regex->is_classical())
                continue;

            euf::snode* first = mem.m_str->first();
            SASSERT(first);
            euf::snode* tail = m_sg.drop_first(mem.m_str);
            SASSERT(tail);

            tau_pairs pairs;
            compute_tau(m, m_seq, m_sg, mem.m_regex->get_expr(), pairs);

            for (auto const& pair : pairs) {
                euf::snode* sn_p = m_sg.mk(pair.m_p);
                euf::snode* sn_q = m_sg.mk(pair.m_q);
                
                // Eagerly eliminate contradictory cases
                // e.g. check intersection emptiness with max_states = 100
                if (m_seq_regex->is_empty_bfs(sn_p, 100) == l_true)
                    continue;
                if (m_seq_regex->is_empty_bfs(sn_q, 100) == l_true)
                    continue;
                
                // Also check intersection with other primitive constraints on `first`
                ptr_vector<euf::snode> regexes_p;
                regexes_p.push_back(sn_p);
                for (auto const& prev_mem : node->str_mems()) {
                    if (prev_mem.m_str == first)
                        regexes_p.push_back(prev_mem.m_regex);
                }
                if (regexes_p.size() > 1 && m_seq_regex->check_intersection_emptiness(regexes_p, 100) == l_true)
                    continue;

                nielsen_node* child = mk_child(node);
                mk_edge(node, child, true);
                
                // remove the original mem from child
                auto& child_mems = child->str_mems();
                for (unsigned k = 0; k < child_mems.size(); ++k) {
                    if (child_mems[k].m_id == mem.m_id) {
                        child_mems[k] = child_mems.back();
                        child_mems.pop_back();
                        break;
                    }
                }
                
                child->add_str_mem(str_mem(first, sn_p, mem.m_history, next_mem_id(), mem.m_dep));
                child->add_str_mem(str_mem(tail, sn_q, mem.m_history, next_mem_id(), mem.m_dep));
            }
            
            return true;
        }
        return false;
    }

    bool nielsen_graph::fire_gpower_intro(
            nielsen_node* node, str_eq const& eq,
            euf::snode* var, euf::snode_vector const& ground_prefix_orig, bool fwd) {

        // Compress repeated patterns in the ground prefix (mirrors ZIPT's LcpCompressionFull).
        // E.g., [a,b,a,b] has minimal period 2 → use [a,b] as the power base.
        // This ensures we use the minimal repeating unit: x = (ab)^n · suffix
        // instead of x = (abab)^n · suffix.
        // (mirrors ZIPT: if b.Length == 1 && b is PowerToken pt => b = pt.Base)
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
            expr* base_e = get_power_base_expr(ground_prefix[0], m_seq);
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
                base_str = m_seq.str.mk_concat(base_str, tok_expr);
            else
                base_str = m_seq.str.mk_concat(tok_expr, base_str);
        }

        unsigned mc = 0;
        m_mod_cnt.find(var->id(), mc);

        // Create fresh exponent variable and power expression: base^n
        expr_ref fresh_n = get_or_create_gpower_n_var(var, mc);
        expr_ref power_expr(m_seq.str.mk_power(base_str, fresh_n), m);
        euf::snode* power_snode = m_sg.mk(power_expr);
        if (!power_snode)
            return false;

        expr_ref zero(a.mk_int(0), m);

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
                expr* inner_base = get_power_base_expr(tok, m_seq);
                if (inner_exp && inner_base) {
                    fresh_m = get_or_create_gpower_m_var(var, mc);
                    expr_ref partial_pow(m_seq.str.mk_power(inner_base, fresh_m), m);
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
            e->add_side_constraint(mk_constraint(a.mk_ge(fresh_n, zero), eq.m_dep));

            // Side constraints for fresh partial exponent
            if (fresh_m.get()) {
                expr* inner_exp = get_power_exponent(tok);
                // m' >= 0
                e->add_side_constraint(mk_constraint(a.mk_ge(fresh_m, zero), eq.m_dep));
                // m' <= inner_exp
                e->add_side_constraint(mk_constraint(a.mk_ge(inner_exp, fresh_m), eq.m_dep));
            }
        }

        return true;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_signature_split
    // Heuristic equation split based on a shortest prefix signature (i, j):
    // prefixes u[0..i-1], v[0..j-1] must contain at least one variable and
    // every variable in one prefix must occur in the other prefix.
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_signature_split(nielsen_node* node) {
        auto first_var_pos = [](euf::snode_vector const& toks) {
            for (unsigned k = 0; k < toks.size(); ++k)
                if (toks[k]->is_var())
                    return k;
            return toks.size();
        };

        auto const& eqs = node->str_eqs();
        for (unsigned eq_idx = 0; eq_idx < eqs.size(); ++eq_idx) {
            str_eq const& eq = eqs[eq_idx];
            SASSERT(eq.m_lhs && eq.m_rhs);
            if (eq.is_trivial())
                continue;

            euf::snode_vector lhs_toks, rhs_toks;
            eq.m_lhs->collect_tokens(lhs_toks);
            eq.m_rhs->collect_tokens(rhs_toks);

            // Start from the first variable on each side; if one side has no
            // variable, this equation has no usable signature.
            unsigned i0 = first_var_pos(lhs_toks);
            unsigned j0 = first_var_pos(rhs_toks);
            if (i0 == lhs_toks.size() || j0 == rhs_toks.size())
                continue;

            std::unordered_map<expr*, unsigned> lhs_first, rhs_first;
            lhs_first.reserve(lhs_toks.size());
            rhs_first.reserve(rhs_toks.size());

            for (unsigned k = 0; k < lhs_toks.size(); ++k) {
                if (!lhs_toks[k]->is_var())
                    continue;
                expr* x = lhs_toks[k]->get_expr();
                if (!lhs_first.contains(x))
                    lhs_first.emplace(x, k);
            }
            for (unsigned k = 0; k < rhs_toks.size(); ++k) {
                if (!rhs_toks[k]->is_var())
                    continue;
                expr* x = rhs_toks[k]->get_expr();
                if (!rhs_first.contains(x))
                    rhs_first.emplace(x, k);
            }

            svector<unsigned> lhs_need_j(lhs_toks.size(), UINT_MAX);
            svector<unsigned> rhs_need_i(rhs_toks.size(), UINT_MAX);

            // Prefix summary arrays:
            // lhs_need_j[k] = maximum first-occurrence index in rhs for any
            // variable seen in lhs[0..k]. Symmetric for rhs_need_i.
            // A value of UINT_MAX means "no variable requirement yet".
            // A value of UINT_MAX-1 means "fail: some prefix variable does not
            // occur on the opposite side at all".
            unsigned const FAIL_MARK = UINT_MAX - 1;
            unsigned need = UINT_MAX;
            for (unsigned k = 0; k < lhs_toks.size(); ++k) {
                if (lhs_toks[k]->is_var()) {
                    auto it = rhs_first.find(lhs_toks[k]->get_expr());
                    if (it == rhs_first.end())
                        need = FAIL_MARK;
                    else if (need != FAIL_MARK)
                        need = (need == UINT_MAX) ? it->second : std::max(need, it->second);
                }
                lhs_need_j[k] = need;
            }

            need = UINT_MAX;
            for (unsigned k = 0; k < rhs_toks.size(); ++k) {
                if (rhs_toks[k]->is_var()) {
                    auto it = lhs_first.find(rhs_toks[k]->get_expr());
                    if (it == lhs_first.end())
                        need = FAIL_MARK;
                    else if (need != FAIL_MARK)
                        need = (need == UINT_MAX) ? it->second : std::max(need, it->second);
                }
                rhs_need_i[k] = need;
            }

            unsigned i = i0 + 1;
            unsigned j = j0 + 1;

            // Compute least fixpoint for (i, j): grow one side only when the
            // current prefix on the other side requires it.
            bool changed = true;
            while (changed) {
                changed = false;

                unsigned req_j = lhs_need_j[i - 1];
                if (req_j == FAIL_MARK) {
                    i = lhs_toks.size();
                    break;
                }
                if (req_j != UINT_MAX && req_j + 1 > j) {
                    j = req_j + 1;
                    changed = true;
                }

                unsigned req_i = rhs_need_i[j - 1];
                if (req_i == FAIL_MARK) {
                    j = rhs_toks.size();
                    break;
                }
                if (req_i != UINT_MAX && req_i + 1 > i) {
                    i = req_i + 1;
                    changed = true;
                }
            }

            if (i >= lhs_toks.size() || j >= rhs_toks.size())
                continue;

            // Decompose u = u1·u2 and v = v1·v2 at signature indices.
            euf::snode* u1 = m_sg.drop_right(eq.m_lhs, lhs_toks.size() - i);
            euf::snode* u2 = m_sg.drop_left(eq.m_lhs, i);
            euf::snode* v1 = m_sg.drop_right(eq.m_rhs, rhs_toks.size() - j);
            euf::snode* v2 = m_sg.drop_left(eq.m_rhs, j);
            th_rewriter rw(m);
            auto x_e = skolem(m, rw).mk("signature-split", eq.m_lhs->get_expr(), eq.m_rhs->get_expr(), eq.m_lhs->get_sort());
            euf::snode *x = m_sg.mk(x_e);

            for (unsigned branch = 0; branch < 2; ++branch) {
                nielsen_node* child = mk_child(node);
                mk_edge(node, child, true);

                auto& child_eqs = child->str_eqs();
                child_eqs[eq_idx] = child_eqs.back();
                child_eqs.pop_back();

                // Two-way split:
                // (1) u1·x = v1   and   u2 = x·v2
                // (2) u1 = v1·x   and   x·u2 = v2
                if (branch == 0) {
                    child_eqs.push_back(str_eq(m_sg.mk_concat(u1, x), v1, eq.m_dep));
                    child_eqs.push_back(str_eq(u2, m_sg.mk_concat(x, v2), eq.m_dep));
                }
                else {
                    child_eqs.push_back(str_eq(u1, m_sg.mk_concat(v1, x), eq.m_dep));
                    child_eqs.push_back(str_eq(m_sg.mk_concat(x, u2), v2, eq.m_dep));
                }
            }
            return true;
        }
        return false;
    }
    
    bool nielsen_graph::apply_regex_if_split(nielsen_node *node) {
        for (str_mem const &mem : node->str_mems()) {
            SASSERT(mem.m_str && mem.m_regex);

            expr *r_expr = mem.m_regex->get_expr();
            expr_ref c(m), th(m), el(m);
            if (!bool_rewriter(m).decompose_ite(r_expr, c, th, el))
                continue;

            bool created = false;

            // Worklist: (regex_expr, accumulated_conditions).
            // Call decompose_ite in a loop until no more ite sub-expressions,
            // branching on c=true and c=false and accumulating conditions.
            vector<std::pair<expr_ref, expr_ref_vector>> worklist;
            worklist.push_back({expr_ref(r_expr, m), expr_ref_vector(m)});

            while (!worklist.empty()) {
                auto [r, cs] = std::move(worklist.back());
                worklist.pop_back();

                if (m_seq.re.is_empty(r))
                    continue;

                expr_ref c2(m), th2(m), el2(m);
                if (!bool_rewriter(m).decompose_ite(r, c2, th2, el2)) {
                    // No ite remaining: leaf → create child node with regex updated to r
                    euf::snode *new_regex_snode = m_sg.mk(r);
                    nielsen_node *child = mk_child(node);
                    for (auto f : cs)
                        child->add_constraint(constraint(f, mem.m_dep, m));
                    mk_edge(node, child, true);
                    for (str_mem &cm : child->str_mems())
                        if (cm.m_id == mem.m_id) {
                            cm.m_regex = new_regex_snode;
                            break;
                        }
                    created = true;
                    continue;
                }

                th_rewriter tr(m);
                expr_ref c_simp(c2, m);
                tr(c_simp);

                if (m.is_true(c_simp)) {
                    if (!m_seq.re.is_empty(th2))
                        worklist.push_back({th2, std::move(cs)});
                }
                else if (m.is_false(c_simp)) {
                    if (!m_seq.re.is_empty(el2))
                        worklist.push_back({el2, std::move(cs)});
                }
                else {
                    if (!m_seq.re.is_empty(th2)) {
                        expr_ref_vector cs_true(cs);
                        cs_true.push_back(c2);
                        worklist.push_back({th2, std::move(cs_true)});
                    }
                    if (!m_seq.re.is_empty(el2)) {
                        expr_ref_vector cs_false(cs);
                        cs_false.push_back(mk_not(c2));
                        worklist.push_back({el2, std::move(cs_false)});
                    }
                }
            }

            if (created)
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
            SASSERT(mem.m_str && mem.m_regex);
            if (mem.is_primitive())
                continue;
            euf::snode* first = mem.m_str->first();
            if (!first || !first->is_var())
                continue;

            // Compute minterms from the regex
            euf::snode_vector minterms;
            m_sg.compute_minterms(mem.m_regex, minterms);
            VERIFY(!minterms.empty());

            bool created = false;
            // std::cout << "Considering regex: " << mk_pp(mem.m_regex->get_expr(), m) << std::endl;

            // Branch 1: x → ε (progress)
            {
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                nielsen_subst s(first, m_sg.mk_empty_seq(first->get_sort()), mem.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
                created = true;
            }

            // TODO: replace this with a version that just uses symbolic derivatives
            // and not min-terms.
            // It solves x -> unit(nth(x, 0)) ++ x
            // Then the split_regex_unit can solve process the node further.

            // Branch 2+: for each minterm m_i, x → ?c · x
            // where ?c is a symbolic char constrained by the minterm
            for (euf::snode* mt : minterms) {
                // std::cout << "Processing minterm: " << mk_pp(mt->get_expr(), m) << std::endl;
                SASSERT(mt);
                SASSERT(mt->get_expr());
                SASSERT(!mt->is_fail());

                // Try Brzozowski derivative with respect to this minterm
                // If the derivative is fail (empty language), skip this minterm
                euf::snode* deriv = m_sg.brzozowski_deriv(mem.m_regex, mt);
                SASSERT(deriv);
                if (deriv->is_fail())
                    continue;
                // std::cout << "Result: " << mk_pp(deriv->get_expr(), m) << std::endl;

                SASSERT(m_seq_regex);
                char_set cs = m_seq_regex->minterm_to_char_set(mt->get_expr());
                // std::cout << "char_set:\n";
                // for (auto& r : cs.ranges()) {
                //     std::cout << "\t[" << r.m_lo << "; " << r.m_hi - 1 << "]" << std::endl;
                // }

                euf::snode* fresh_char = nullptr;
                if (cs.is_unit()) {
                    expr_ref char_expr(m_sg.get_seq_util().str.mk_string(zstring(cs.first_char())), m);
                    fresh_char = m_sg.mk(char_expr);
                }
                else {
                    unsigned mc = 0;
                    m_mod_cnt.find(first->id(), mc);
                    fresh_char = get_or_create_char_var(first, mc);
                }

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
                    child->add_char_range(fresh_char, cs, mem.m_dep);
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

        euf::snode* power = nullptr;
        euf::snode* var_head = nullptr;
        str_eq const* eq = nullptr;
        bool fwd = true;
        if (!find_power_vs_var(node, power, var_head, eq, fwd))
            return false;

        SASSERT(power->is_power() && power->num_args() >= 1);
        euf::snode* base = power->arg(0);
        expr* zero = a.mk_int(0);

        // Branch 1: enumerate all decompositions of the base.
        // x = base^m · prefix_i(base) where 0 <= m < n
        // Uses the same GetDecompose pattern as fire_gpower_intro.
        {
            euf::snode_vector base_toks;
            collect_tokens_dir(base, fwd, base_toks);
            unsigned base_len = base_toks.size();
            expr* base_expr = get_power_base_expr(power, m_seq);
            if (!base_expr || base_len == 0)
                return false;

            unsigned mc = 0;
            m_mod_cnt.find(var_head->id(), mc);
            
            expr_ref fresh_m = get_or_create_gpower_n_var(var_head, mc);
            expr_ref power_m_expr(m_seq.str.mk_power(base_expr, fresh_m), m);
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
                    expr* inner_base = get_power_base_expr(tok, m_seq);
                    if (inner_exp && inner_base) {
                        fresh_inner_m = get_or_create_gpower_m_var(var_head, mc);
                        expr_ref partial_pow(m_seq.str.mk_power(inner_base, fresh_inner_m), m);
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
                    // Token is a char: P(char) = ε, suffix is just the prefix
                    replacement = prefix_sn ? dir_concat(m_sg, power_m_sn, prefix_sn, fwd) : power_m_sn;

                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, true);
                nielsen_subst s(var_head, replacement, eq->m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);

                // Side constraint: n >= 0
                e->add_side_constraint(mk_constraint(a.mk_ge(fresh_m, zero), eq->m_dep));

                // Side constraints for fresh partial exponent
                if (fresh_inner_m.get()) {
                    expr* inner_exp = get_power_exponent(tok);
                    // m' >= 0
                    e->add_side_constraint(mk_constraint(a.mk_ge(fresh_inner_m, zero), eq->m_dep));
                    // m' <= inner_exp
                    e->add_side_constraint(mk_constraint(a.mk_ge(inner_exp, fresh_inner_m), eq->m_dep));
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

    bool nielsen_graph::apply_var_num_unwinding_eq(nielsen_node* node) {

        euf::snode* power = nullptr;
        euf::snode* var_head = nullptr;
        str_eq const* eq = nullptr;
        bool fwd = true;
        if (!find_power_vs_var(node, power, var_head, eq, fwd))
            return false;

        SASSERT(power->is_power() && power->num_args() >= 1);
        euf::snode* base = power->arg(0);
        expr* exp_n = get_power_exponent(power);
        expr_ref zero(a.mk_int(0), m);
        expr_ref one(a.mk_int(1), m);

        // Branch 1: n = 0 → replace u^n with ε (progress)
        // Side constraint: n = 0
        {
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, true);
            nielsen_subst s(power, m_sg.mk_empty_seq(power->get_sort()), eq->m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
            if (exp_n)
                e->add_side_constraint(mk_constraint(m.mk_eq(exp_n, zero), eq->m_dep));
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
                e->add_side_constraint(mk_constraint(a.mk_ge(exp_n, one), eq->m_dep));
        }

        return true;
    }

    bool nielsen_graph::apply_var_num_unwinding_mem(nielsen_node* node) {

        euf::snode* power = nullptr;
        str_mem const* mem = nullptr;
        bool fwd = true;
        if (!find_power_vs_var(node, power, mem, fwd))
            return false;

        SASSERT(power->is_power() && power->num_args() >= 1);
        euf::snode* base = power->arg(0);
        expr* exp_n = get_power_exponent(power);
        expr_ref zero(a.mk_int(0), m);
        expr_ref one(a.mk_int(1), m);

        // Branch 1: n = 0 → replace u^n with ε (progress)
        // Side constraint: n = 0
        {
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, true);
            nielsen_subst s(power, m_sg.mk_empty_seq(power->get_sort()), mem->m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
            if (exp_n)
                e->add_side_constraint(mk_constraint(m.mk_eq(exp_n, zero), mem->m_dep));
        }

        // Branch 2: n >= 1 → peel one u: u^n → u · u^(n-1)
        // Side constraint: n >= 1
        {
            euf::snode* fresh = mk_fresh_var(power->get_sort());
            euf::snode* replacement = dir_concat(m_sg, base, fresh, fwd);
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, false);
            nielsen_subst s(power, replacement, mem->m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
            if (exp_n)
                e->add_side_constraint(mk_constraint(a.mk_ge(exp_n, one), mem->m_dep));
        }

        return true;
    }

    dep_tracker nielsen_graph::collect_conflict_deps() const {
        dep_tracker deps = nullptr;
        // We enumerate all nodes rather than having a "todo"-list, as
        // hypothetically the graph could contain cycles in the future
        for (nielsen_node const* n : m_nodes) {
            if (n->eval_idx() != m_run_idx)
                continue;
            if (n->reason() == backtrack_reason::children_failed)
                continue;

            SASSERT(n->is_currently_conflict());
            if (n->m_conflict_external_literal != sat::null_literal) {
                // We know from the outer solver that this literal is assigned false
                deps = m_dep_mgr.mk_join(deps, m_dep_mgr.mk_leaf(n->m_conflict_external_literal));
                continue;
            }
            SASSERT(n->outgoing().empty());
            SASSERT(n->m_conflict_internal);
            deps = m_dep_mgr.mk_join(deps, n->m_conflict_internal);
            // for (str_eq const& eq : n->str_eqs())
            //     deps = m_dep_mgr.mk_join(deps, eq.m_dep);
            // for (str_mem const& mem : n->str_mems())
            //     deps = m_dep_mgr.mk_join(deps, mem.m_dep);
        }
        return deps;
    }


    // NSB review: this is one of several methods exposed for testing
    void nielsen_graph::explain_conflict(svector<enode_pair>& eqs,
        svector<sat::literal>& mem_literals) const {
        SASSERT(m_root);
        auto deps = collect_conflict_deps();
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

        if (n->is_empty())
            return expr_ref(a.mk_int(0), m);

        if (n->is_char_or_unit())
            return expr_ref(a.mk_int(1), m);

        if (n->is_concat()) {
            expr_ref left = compute_length_expr(n->arg(0));
            expr_ref right = compute_length_expr(n->arg(1));
            return expr_ref(a.mk_add(left, right), m);
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
        return expr_ref(m_seq.str.mk_length(n->get_expr()), m);
    }

    void
nielsen_graph::generate_length_constraints(vector<length_constraint>& constraints) {
    if (!m_root) return;
        uint_set seen_vars;

        seq_util& seq = m_sg.get_seq_util();
        for (str_eq const& eq : m_root->str_eqs()) {
            if (eq.is_trivial())
                continue;

            expr_ref len_lhs = compute_length_expr(eq.m_lhs);
            expr_ref len_rhs = compute_length_expr(eq.m_rhs);
            // std::cout << "Length constraint from LHS " << snode_label_html(eq.m_lhs, m) << " to " << mk_pp(len_lhs, m) << ":\n";
            // std::cout << "Length constraint from RHS " << snode_label_html(eq.m_rhs, m) << " to " << mk_pp(len_rhs, m) << std::endl;
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
                    expr_ref ge_zero(a.mk_ge(len_var, a.mk_int(0)), m);
                    constraints.push_back(length_constraint(ge_zero, eq.m_dep, length_kind::nonneg, m));
                }
            }
        }

        // Parikh interval reasoning for regex memberships
        for (str_mem const& mem : m_root->str_mems()) {
            expr* re_expr = mem.m_regex->get_expr();
            if (!re_expr || !seq.is_re(re_expr))
                continue;

            unsigned min_len = 0, max_len = UINT_MAX;
            compute_regex_length_interval(mem.m_regex, min_len, max_len);

            expr_ref len_str = compute_length_expr(mem.m_str);

            // generate len(str) >= min_len when min_len > 0
            if (min_len > 0) {
                expr_ref bound(a.mk_ge(len_str, a.mk_int(min_len)), m);
                constraints.push_back(length_constraint(bound, mem.m_dep, length_kind::bound, m));
            }

            // generate len(str) <= max_len when bounded
            if (max_len < UINT_MAX) {
                expr_ref bound(a.mk_le(len_str, a.mk_int(max_len)), m);
                constraints.push_back(length_constraint(bound, mem.m_dep, length_kind::bound, m));
            }
        }
    }

    void nielsen_graph::compute_regex_length_interval(euf::snode* regex, unsigned& min_len, unsigned& max_len) {
        seq_util& seq = m_sg.get_seq_util();
        expr* e = regex->get_expr();
        SASSERT(e && seq.is_re(e));
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

    std::ostream& constraint::display(std::ostream& out) const {
        if (fml) out << mk_pp(fml, fml.get_manager());
        else out << "null";
        return out;
    }

    // -----------------------------------------------------------------------
    // Integer feasibility subsolver implementation
    // Uses the injected simple_solver (default: lp_simple_solver).
    // -----------------------------------------------------------------------

    // -----------------------------------------------------------------------
    // Modification counter: substitution length tracking
    // mirrors ZIPT's LocalInfo.CurrentModificationCnt + NielsenEdge.IncModCount/DecModCount
    // + NielsenNode constructor length assertion logic
    // -----------------------------------------------------------------------

    expr_ref nielsen_graph::get_or_create_len_var(euf::snode* var, unsigned mod_count) {
        th_rewriter rw(m);
        return skolem(m, rw).mk("len!", var->get_expr(), a.mk_int(mod_count), a.mk_int());
    }

    euf::snode* nielsen_graph::get_or_create_char_var(euf::snode* var, unsigned mod_count) {
        th_rewriter rw(m);
        sort *char_sort = m_seq.mk_char_sort();
        auto char_var = skolem(m, rw).mk("char!", var->get_expr(), a.mk_int(mod_count), char_sort);
        expr_ref unit(m_seq.str.mk_unit(char_var), m);
        return m_sg.mk(unit);
    }

    expr_ref nielsen_graph::get_or_create_gpower_n_var(euf::snode* var, unsigned mod_count) {
        SASSERT(var && var->is_var());
        th_rewriter rw(m);
        return skolem(m, rw).mk("gpn!", var->get_expr(), a.mk_int(mod_count), a.mk_int());
    }

    expr_ref nielsen_graph::get_or_create_gpower_m_var(euf::snode* var, unsigned mod_count) {
        SASSERT(var && var->is_var());
        th_rewriter rw(m);
        return skolem(m, rw).mk("gpm!", var->get_expr(), a.mk_int(mod_count), a.mk_int());
    }

    void nielsen_graph::add_subst_length_constraints(nielsen_edge* e) {
        auto const& substs = e->subst();
        bool has_non_elim = false;


        // Step 1: Compute LHS (|x|) for each non-eliminating substitution
        // using current m_mod_cnt (before bumping).
        // Also assert |x|_k >= 0 (mirrors ZIPT's NielsenNode constructor line 172).
        svector<std::pair<unsigned, expr*>> lhs_exprs;
        for (unsigned i = 0; i < substs.size(); ++i) {
            auto const& s = substs[i];
            if (!s.m_var->is_var())
                continue;
            if (!m_seq.is_seq(s.m_var->get_expr()))
                continue;
            expr_ref lhs = compute_length_expr(s.m_var);
            lhs_exprs.push_back({i, lhs.get()});
            if (s.is_eliminating())
                continue;
            has_non_elim = true;
            // Assert LHS >= 0
            e->add_side_constraint(mk_constraint(a.mk_ge(lhs, a.mk_int(0)), s.m_dep));
        }

        // Step 2: Bump mod counts for all non-eliminating variables at once.
        if (has_non_elim)
            inc_edge_mod_counts(e);


        // Step 3: Compute RHS (|u|) with bumped mod counts and add |x| = |u|.
        for (auto const& p : lhs_exprs) {
            unsigned idx = p.first;
            expr* lhs_expr = p.second;
            auto const& s = substs[idx];
            expr_ref rhs = compute_length_expr(s.m_replacement);
            e->add_side_constraint(mk_constraint(m.mk_eq(lhs_expr, rhs), s.m_dep));
        }

        // Step 4: Restore mod counts (temporary bump for computing RHS only).
        if (has_non_elim)
            dec_edge_mod_counts(e);
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
            VERIFY(m_mod_cnt.find(id, prev));
            SASSERT(prev >= 1);
            if (prev <= 1)
                m_mod_cnt.remove(id);
            else
                m_mod_cnt.insert(id, prev - 1);
        }
    }

    void nielsen_graph::assert_node_new_int_constraints(nielsen_node* node) {
        // Assert only the constraints that are new to this node (beyond those
        // inherited from its parent via clone_from).  The parent's constraints are
        // already present in the enclosing solver scope; asserting them again would
        // be redundant (though harmless).  This is called by search_dfs right after
        // simplify_and_init, which is where new constraints are produced.
        for (unsigned i = node->m_parent_ic_count; i < node->constraints().size(); ++i) {
            m_solver.assert_expr(node->constraints()[i].fml);
        }
    }

    void nielsen_graph::generate_node_length_constraints(nielsen_node* node) {
        if (node->m_node_len_constraints_generated)
            return;
        node->m_node_len_constraints_generated = true;

        // Skip the root node — its length constraints are already asserted
        // at the base solver level by assert_root_constraints_to_solver().
        if (node == m_root)
            return;

        uint_set seen_vars;

        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial())
                continue;

            expr_ref len_lhs = compute_length_expr(eq.m_lhs);
            expr_ref len_rhs = compute_length_expr(eq.m_rhs);
            node->add_constraint(mk_constraint(m.mk_eq(len_lhs, len_rhs), eq.m_dep));

            // non-negativity for each variable (mod-count-aware)
            euf::snode_vector tokens;
            eq.m_lhs->collect_tokens(tokens);
            eq.m_rhs->collect_tokens(tokens);
            for (euf::snode* tok : tokens) {
                if (tok->is_var() && !seen_vars.contains(tok->id())) {
                    seen_vars.insert(tok->id());
                    expr_ref len_var = compute_length_expr(tok);
                    node->add_constraint(mk_constraint(a.mk_ge(len_var, a.mk_int(0)), eq.m_dep));
                }
            }
        }

        // Parikh interval bounds for regex memberships at this node
        for (str_mem const& mem : node->str_mems()) {
            expr* re_expr = mem.m_regex->get_expr();
            SASSERT(re_expr && m_seq.is_re(re_expr));

            unsigned min_len = 0, max_len = UINT_MAX;
            compute_regex_length_interval(mem.m_regex, min_len, max_len);

            expr_ref len_str = compute_length_expr(mem.m_str);

            if (min_len > 0)
                node->add_constraint(mk_constraint(a.mk_ge(len_str, a.mk_int(min_len)), mem.m_dep));
            if (max_len < UINT_MAX)
                node->add_constraint(mk_constraint(a.mk_le(len_str, a.mk_int(max_len)), mem.m_dep));
        }
    }

    bool nielsen_graph::check_int_feasibility() {
        // In incremental mode the solver already holds all path constraints
        // (root length constraints at the base level, edge side_constraints and node
        // constraints pushed/popped as the DFS descends and backtracks).
        // A plain check() is therefore sufficient.
        return m_solver.check() != l_false;
    }

    dep_tracker nielsen_graph::get_subsolver_dependency(nielsen_node* n) {
        u_map<dep_tracker> expr_to_dep;
        expr_ref_vector assumptions(m);
        assumptions.resize(n->constraints().size());
        for (unsigned i = 0; i < assumptions.size(); i++) {
            auto& c = n->constraints()[i];
            expr_to_dep.insert_if_not_there(c.fml->get_id(), c.dep);
            assumptions[i] = c.fml;
        }
        expr_ref_vector core(m);
        lbool res = m_core_solver.check_with_assumptions(assumptions, core);
        VERIFY(res == l_false);

        dep_tracker dep = dep_mgr().mk_empty();
        for (expr* e : core) {
             dep = dep_mgr().mk_join(dep, expr_to_dep[e->get_id()]);
        }
        return dep;
    }

    bool nielsen_graph::check_lp_le(expr* lhs, expr* rhs) {
        rational lhs_lo, rhs_up;
        if (m_solver.lower_bound(lhs, lhs_lo) &&
            m_solver.upper_bound(rhs, rhs_up)) {

            if (lhs_lo > rhs_up)
                return false; // definitely infeasible
        }
        rational rhs_lo, lhs_up;
        if (m_solver.lower_bound(lhs, lhs_lo) &&
            m_solver.upper_bound(rhs, rhs_up)) {

            if (lhs_up <= rhs_lo)
                return true; // definitely feasible
        }
        // fall through - ask the solver [expensive]

        // TODO: Maybe cache the result?

        // The solver already holds all path constraints incrementally.
        // Temporarily add NOT(lhs <= rhs), i.e. lhs >= rhs + 1.
        // If that is unsat, then lhs <= rhs is entailed.
        expr_ref one(a.mk_int(1), m);
        expr_ref rhs_plus_one(a.mk_add(rhs, one), m);

        m_solver.push();
        m_solver.assert_expr(a.mk_ge(lhs, rhs_plus_one));
        lbool result = m_solver.check();
        m_solver.pop(1);
        return result == l_false;
    }

    constraint nielsen_graph::mk_constraint(expr* fml, dep_tracker const& dep) {
        return constraint(fml, dep, m);
    }

    expr* nielsen_graph::get_power_exponent(euf::snode* power) {
        SASSERT(power);
        if (!power->is_power())
            return nullptr;
        SASSERT(power->num_args() == 2);
        euf::snode* exp_snode = power->arg(1);
        return exp_snode ? exp_snode->get_expr() : nullptr;
    }

    expr_ref nielsen_graph::mk_fresh_int_var() {
        std::string name = "n!" + std::to_string(m_fresh_cnt++);
        return expr_ref(m.mk_fresh_const(name.c_str(), a.mk_int()), m);
    }

    bool nielsen_graph::solve_sat_path_raw(model_ref& mdl) {
        mdl = nullptr;
        if (m_sat_path.empty() && (!m_sat_node ||
            (m_sat_node->constraints().empty() && m_sat_node->char_diseqs().empty() && m_sat_node->char_ranges().empty())))
            return false;

        // Re-assert the sat-path constraints into m_solver (which holds only root-level
        // constraints at this point) and extract a model via the injected simple_solver.
        // The sat path was found by DFS which verified feasibility at every step via
        // check_int_feasibility, so all constraints along this path are jointly satisfiable
        // and do not require incremental skipping.
        IF_VERBOSE(1, verbose_stream() << "solve_sat_path_ints: sat_path length=" << m_sat_path.size() << "\n";);
        m_solver.push();
        for (nielsen_edge* e : m_sat_path) {
            for (auto const& ic : e->side_constraints()) {
                m_solver.assert_expr(ic.fml);
            }
        }
        if (m_sat_node) {
            for (auto const& ic : m_sat_node->constraints())
                m_solver.assert_expr(ic.fml);
            for (auto const& dis : m_sat_node->char_diseqs()) {
                ptr_vector<expr> dist;
                dist.reserve((unsigned)dis.m_value.size());
                for (unsigned i = 0; i < dis.m_value.size(); ++i) {
                    dist.push_back(dis.m_value[i].first->get_expr());
                }
                m_solver.assert_expr(m.mk_distinct(dist.size(), dist.data()));
            }
            // NSB code review: there is a seprate sort for characters
            bv_util arith(m);
            for (auto const& kvp : m_sat_node->char_ranges()) {
                expr_ref_vector cases(m);
                const auto& var = m_sg.nodes()[kvp.m_key]->get_expr();
                const auto& ranges = kvp.m_value.first.ranges();
                cases.reserve(ranges.size());
                SASSERT(var->get_sort()->get_family_id() == arith.get_family_id());
                unsigned bitCnt = arith.get_bv_size(var);

                for (unsigned i = 0; i < ranges.size(); ++i) {
                    cases.push_back(m.mk_and(
                        arith.mk_ule(arith.mk_numeral(ranges[i].m_lo, bitCnt), var),
                        arith.mk_ule(var, arith.mk_numeral(ranges[i].m_hi - 1, bitCnt))
                        ));
                }
                m_solver.assert_expr(m.mk_or(cases));
            }
        }
        lbool result = m_solver.check();
        IF_VERBOSE(1, verbose_stream() << "solve_sat_path_ints result: " << result << "\n";);
        if (result == l_true) {
            m_solver.get_model(mdl);
            IF_VERBOSE(1, if (mdl) {
                verbose_stream() << "  raw_model:\n";
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
                                             euf::snode* str, euf::snode* regex, dep_tracker& dep) {
        SASSERT(str && regex && m_seq_regex);
        // Only apply to ground regexes with non-trivial strings
        if (!regex->is_ground())
            return false;


        // Build the overapproximation regex for the string.
        // Variables → intersection of their primitive regex constraints (or Σ*)
        // Symbolic chars → re.range from char_ranges (or full_char)
        // Concrete chars → to_re(unit(c))
        euf::snode_vector tokens;
        str->collect_tokens(tokens);
        if (tokens.empty())
            return false;

        SASSERT(dep);

        euf::snode* approx = nullptr;
        for (euf::snode* tok : tokens) {
            euf::snode* tok_re = nullptr;

            if (tok->is_char()) {
                // Concrete character → to_re(unit(c))
                expr* te = tok->get_expr();
                SASSERT(te);
                expr_ref tre(m_seq.re.mk_to_re(te), m);
                tok_re = m_sg.mk(tre);
            }
            else if (tok->is_var()) {
                // Variable → intersection of primitive regex constraints, or Σ*
                euf::snode* x_range = m_seq_regex->collect_primitive_regex_intersection(tok, node, m_dep_mgr, dep);
                if (x_range)
                    tok_re = x_range;
                else {
                    // Unconstrained variable: approximate as Σ*
                    sort* str_sort = m_seq.str.mk_string_sort();
                    expr_ref all_re(m_seq.re.mk_full_seq(m_seq.re.mk_re(str_sort)), m);
                    tok_re = m_sg.mk(all_re);
                }
            }
            else if (tok->is_unit()) {
                // Symbolic char — try to get char_range
                if (node.char_ranges().contains(tok->id())) {
                    auto& cs = node.char_ranges()[tok->id()];
                    if (!cs.first.is_empty()) {
                        // Build union of re.range for each interval
                        euf::snode* range_re = nullptr;
                        for (auto const& r : cs.first.ranges()) {
                            expr_ref lo(m_seq.mk_char(r.m_lo), m);
                            expr_ref hi(m_seq.mk_char(r.m_hi - 1), m);
                            expr_ref rng(m_seq.re.mk_range(
                                m_seq.str.mk_string(zstring(r.m_lo)),
                                m_seq.str.mk_string(zstring(r.m_hi - 1))), m);
                            euf::snode* rng_sn = m_sg.mk(rng);
                            if (!range_re)
                                range_re = rng_sn;
                            else {
                                expr_ref u(m_seq.re.mk_union(range_re->get_expr(), rng_sn->get_expr()), m);
                                range_re = m_sg.mk(u);
                            }
                        }
                        dep = dep_mgr().mk_join(dep, cs.second);
                        tok_re = range_re;
                    }
                }
                if (!tok_re) {
                    // Unconstrained symbolic char: approximate as full_char (single char, any value)
                    sort* str_sort = m_seq.str.mk_string_sort();
                    expr_ref fc(m_seq.re.mk_full_char(m_seq.re.mk_re(str_sort)), m);
                    tok_re = m_sg.mk(fc);
                }
            }
            else {
                // Unknown token type — approximate as Σ*
                sort* str_sort = m_seq.str.mk_string_sort();
                expr_ref all_re(m_seq.re.mk_full_seq(m_seq.re.mk_re(str_sort)), m);
                tok_re = m_sg.mk(all_re);
            }

            SASSERT(tok_re);

            if (!approx)
                approx = tok_re;
            else {
                expr* ae = approx->get_expr();
                expr* te = tok_re->get_expr();
                SASSERT(ae && te);
                expr_ref cat(m_seq.re.mk_concat(ae, te), m);
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
        expr_ref inter(m_seq.re.mk_inter(ae, re), m);
        euf::snode* inter_sn = m_sg.mk(inter);
        SASSERT(inter_sn);
        // TODO: Minimize the conflict here
        lbool result = m_seq_regex->is_empty_bfs(inter_sn, 5000);
        return result == l_true;
    }

    // -----------------------------------------------------------------------
    // Leaf-node regex intersection emptiness check
    // Mirrors ZIPT NielsenNode.CheckRegex (NielsenNode.cs:1311-1329)
    // -----------------------------------------------------------------------

    bool nielsen_graph::check_leaf_regex(nielsen_node const& node, dep_tracker& dep) {
        if (!m_seq_regex)
            return true;

        // Group str_mem constraints by variable (primitive constraints only)
        u_map<std::pair<ptr_vector<euf::snode>, dep_tracker>> var_regexes;

        for (auto const& mem : node.str_mems()) {
            if (!mem.m_str || !mem.m_regex)
                continue;
            if (!mem.is_primitive())
                continue;
            euf::snode* const first = mem.m_str->first();
            SASSERT(first && first->is_var());
            auto& list = var_regexes.insert_if_not_there(first->id(), std::pair<ptr_vector<euf::snode>, dep_tracker>());
            list.first.push_back(mem.m_regex);
            list.second = dep_mgr().mk_join(list.second, mem.m_dep);
        }

        // For each variable with 2+ regex constraints, check intersection non-emptiness
        for (auto& [var_id, regexes] : var_regexes) {
            if (regexes.first.size() < 2)
                continue;
            lbool result = m_seq_regex->check_intersection_emptiness(regexes.first, 5000);
            if (result == l_true) {
                // Intersection is empty — infeasible
                dep = regexes.second;
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
        st.update("nseq mod regex fact",       m_stats.m_mod_regex_factorization);
        st.update("nseq mod const nielsen",    m_stats.m_mod_const_nielsen);
        st.update("nseq mod signature split",  m_stats.m_mod_signature_split);
        st.update("nseq mod regex var",        m_stats.m_mod_regex_var_split);
        st.update("nseq mod regex if",         m_stats.m_mod_regex_if_split);
        st.update("nseq mod power split",      m_stats.m_mod_power_split);
        st.update("nseq mod var nielsen",      m_stats.m_mod_var_nielsen);
        st.update("nseq mod var num unwind (eq)",   m_stats.m_mod_var_num_unwinding_eq);
        st.update("nseq mod var num unwind (mem)",   m_stats.m_mod_var_num_unwinding_mem);
    }

}

