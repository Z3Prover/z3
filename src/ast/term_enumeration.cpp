/**
 * term_enumeration.cpp - Bottom-up term enumeration module for Z3
 *
 * Inspired by the Probe synthesizer (Barke et al., "Just-in-Time Learning
 * for Bottom-Up Enumerative Synthesis"). Adapted to use Z3's internal APIs.
 *
 * Key ideas:
 *   - Terms are enumerated bottom-up by "height" (max nesting depth).
 *   - Observational equivalence (OE): two terms that produce the same outputs
 *     on all sample inputs are considered equivalent; only one representative
 *     per equivalence class is kept.
 *   - A Grammar describes which function symbols (operators) and leaves
 *     (constants, variables) are available for enumeration.
 */

#include "ast/term_enumeration.h"
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <functional>
#include <string>
#include <memory>
#include <queue>
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "model/model.h"
#include "model/model_evaluator.h"
#include "solver/solver.h"
#include "smt/smt_solver.h"
#include "util/vector.h"
#include "util/ref.h"
#include "util/obj_hashtable.h"

namespace term_enum {

// ============================================================================
// Grammar production rule
// ============================================================================

/**
 * A Production describes how to construct a term from child terms.
 * - domain: the sort required for each child
 * - range: the sort of the produced term
 * - builder: given a vector of child exprs, produce the result expr
 */
struct Production {
    std::string name;
    sort_ref range;
    sort_ref_vector domain;
    std::function<expr_ref(expr_ref_vector const&)> builder;

    bool is_leaf() const { return domain.empty(); }
};

// ============================================================================
// Grammar
// ============================================================================

/**
 * A Grammar groups productions into leaves (arity 0) and operators (arity > 0).
 */
class Grammar {
public:
    Grammar(ast_manager& m) : m(m) {}

    void add_production(Production p) {
        if (p.is_leaf())
            m_leaves.push_back(std::move(p));
        else
            m_operators.push_back(std::move(p));
    }

    vector<Production> const& leaves() const { return m_leaves; }
    vector<Production> const& operators() const { return m_operators; }
    ast_manager& mgr() const { return m; }

    void add_variable(char const* name, sort* s) {
        expr_ref var(m.mk_const(name, s), m);
        sort_ref sr(s, m);
        sort_ref_vector dom(m);
        add_production({name, sr, dom, [var](expr_ref_vector const&) { return var; }});
    }

    void add_int_const(int val) {
        arith_util a(m);
        expr_ref e(a.mk_int(val), m);
        sort_ref sr(a.mk_int(), m);
        sort_ref_vector dom(m);
        add_production({std::to_string(val), sr, dom, [e](expr_ref_vector const&) { return e; }});
    }

    void add_bv_const(int val, unsigned bits) {
        bv_util bv(m);
        expr_ref e(bv.mk_numeral(rational(val), bits), m);
        sort_ref sr(bv.mk_sort(bits), m);
        sort_ref_vector dom(m);
        add_production({std::to_string(val), sr, dom, [e](expr_ref_vector const&) { return e; }});
    }

    void add_string_const(std::string const& val) {
        seq_util seq(m);
        expr_ref e(seq.str.mk_string(zstring(val.c_str())), m);
        sort_ref sr(seq.str.mk_string_sort(), m);
        sort_ref_vector dom(m);
        add_production({"\"" + val + "\"", sr, dom, [e](expr_ref_vector const&) { return e; }});
    }

    void add_bool_const(bool val) {
        expr_ref e(val ? m.mk_true() : m.mk_false(), m);
        sort_ref sr(m.mk_bool_sort(), m);
        sort_ref_vector dom(m);
        std::string n = val ? "true" : "false";
        add_production({n, sr, dom, [e](expr_ref_vector const&) { return e; }});
    }

    void add_func_decl(func_decl *f) {
        sort_ref range(f->get_range(), m);
        sort_ref_vector dom(m);
        for (unsigned i = 0; i < f->get_arity(); ++i)
            dom.push_back(sort_ref(f->get_domain(i), m));
        add_production({f->get_name().str(), range, dom, [this, f](expr_ref_vector const &args) {
                            return expr_ref(m.mk_app(f, args), m);
                        }});
    }

    void add_expr(expr *e) {
        sort_ref range(e->get_sort(), m);
        sort_ref_vector dom(m);
        std::stringstream ss;
        ss << mk_bounded_pp(e, m);
        std::string name = ss.str();
        add_production({name, range, dom, [this, e](expr_ref_vector const&) { return expr_ref(e, m); }});
    }

private:
    ast_manager& m;
    vector<Production> m_leaves;
    vector<Production> m_operators;
};

// ============================================================================
// Standard grammar factories - build common operator sets
// ============================================================================

namespace grammars {

/**
 * Build a grammar over linear integer arithmetic.
 * Operators: +, -, *, ite (with bool condition)
 */
inline void add_lia_operators(Grammar& g) {
    ast_manager& m = g.mgr();
    arith_util a(m);
    sort_ref isort(a.mk_int(), m);
    sort_ref bsort(m.mk_bool_sort(), m);

    sort_ref_vector ii(m); ii.push_back(isort); ii.push_back(isort);
    sort_ref_vector i1(m); i1.push_back(isort);
    sort_ref_vector bb(m); bb.push_back(bsort); bb.push_back(bsort);
    sort_ref_vector b1(m); b1.push_back(bsort);
    sort_ref_vector bii(m); bii.push_back(bsort); bii.push_back(isort); bii.push_back(isort);

    g.add_production({"add", isort, ii,
        [&m](expr_ref_vector const& ch) { arith_util a(m); return expr_ref(a.mk_add(ch[0], ch[1]), m); }});
    g.add_production({"sub", isort, ii,
        [&m](expr_ref_vector const& ch) { arith_util a(m); return expr_ref(a.mk_sub(ch[0], ch[1]), m); }});
    g.add_production({"mul", isort, ii,
        [&m](expr_ref_vector const& ch) { arith_util a(m); return expr_ref(a.mk_mul(ch[0], ch[1]), m); }});
    g.add_production({"neg", isort, i1,
        [&m](expr_ref_vector const& ch) { arith_util a(m); return expr_ref(a.mk_uminus(ch[0]), m); }});

    g.add_production({"le", bsort, ii,
        [&m](expr_ref_vector const& ch) { arith_util a(m); return expr_ref(a.mk_le(ch[0], ch[1]), m); }});
    g.add_production({"lt", bsort, ii,
        [&m](expr_ref_vector const& ch) { arith_util a(m); return expr_ref(a.mk_lt(ch[0], ch[1]), m); }});
    g.add_production({"eq_int", bsort, ii,
        [&m](expr_ref_vector const& ch) { return expr_ref(m.mk_eq(ch[0], ch[1]), m); }});

    g.add_production({"and", bsort, bb,
        [&m](expr_ref_vector const& ch) { return expr_ref(m.mk_and(ch[0], ch[1]), m); }});
    g.add_production({"or", bsort, bb,
        [&m](expr_ref_vector const& ch) { return expr_ref(m.mk_or(ch[0], ch[1]), m); }});
    g.add_production({"not", bsort, b1,
        [&m](expr_ref_vector const& ch) { return expr_ref(m.mk_not(ch[0]), m); }});

    g.add_production({"ite_int", isort, bii,
        [&m](expr_ref_vector const& ch) { return expr_ref(m.mk_ite(ch[0], ch[1], ch[2]), m); }});
}

/**
 * Build a grammar over bitvectors.
 */
inline void add_bv_operators(Grammar& g, unsigned bits) {
    ast_manager& m = g.mgr();
    bv_util bv(m);
    sort_ref bvsort(bv.mk_sort(bits), m);
    sort_ref bsort(m.mk_bool_sort(), m);

    sort_ref_vector vv(m); vv.push_back(bvsort); vv.push_back(bvsort);
    sort_ref_vector v1(m); v1.push_back(bvsort);
    sort_ref_vector bvv(m); bvv.push_back(bsort); bvv.push_back(bvsort); bvv.push_back(bvsort);

    g.add_production({"bvadd", bvsort, vv,
        [&m](expr_ref_vector const& ch) { bv_util bv(m); return expr_ref(bv.mk_bv_add(ch[0], ch[1]), m); }});
    g.add_production({"bvsub", bvsort, vv,
        [&m](expr_ref_vector const& ch) { bv_util bv(m); return expr_ref(bv.mk_bv_sub(ch[0], ch[1]), m); }});
    g.add_production({"bvmul", bvsort, vv,
        [&m](expr_ref_vector const& ch) { bv_util bv(m); return expr_ref(bv.mk_bv_mul(ch[0], ch[1]), m); }});
    g.add_production({"bvand", bvsort, vv,
        [&m](expr_ref_vector const& ch) { bv_util bv(m); return expr_ref(bv.mk_bv_and(ch[0], ch[1]), m); }});
    g.add_production({"bvor", bvsort, vv,
        [&m](expr_ref_vector const& ch) { bv_util bv(m); return expr_ref(bv.mk_bv_or(ch[0], ch[1]), m); }});
    g.add_production({"bvxor", bvsort, vv,
        [&m](expr_ref_vector const& ch) { bv_util bv(m); return expr_ref(bv.mk_bv_xor(ch[0], ch[1]), m); }});
    g.add_production({"bvnot", bvsort, v1,
        [&m](expr_ref_vector const& ch) { bv_util bv(m); return expr_ref(bv.mk_bv_not(ch[0]), m); }});
    g.add_production({"bvneg", bvsort, v1,
        [&m](expr_ref_vector const& ch) { bv_util bv(m); return expr_ref(bv.mk_bv_neg(ch[0]), m); }});
    g.add_production({"bvshl", bvsort, vv,
        [&m](expr_ref_vector const& ch) { bv_util bv(m); return expr_ref(bv.mk_bv_shl(ch[0], ch[1]), m); }});
    g.add_production({"bvlshr", bvsort, vv,
        [&m](expr_ref_vector const& ch) { bv_util bv(m); return expr_ref(bv.mk_bv_lshr(ch[0], ch[1]), m); }});
    g.add_production({"bvashr", bvsort, vv,
        [&m](expr_ref_vector const& ch) { bv_util bv(m); return expr_ref(bv.mk_bv_ashr(ch[0], ch[1]), m); }});

    g.add_production({"bvult", bsort, vv,
        [&m](expr_ref_vector const& ch) { bv_util bv(m); return expr_ref(m.mk_app(bv.get_fid(), OP_ULT, ch[0], ch[1]), m); }});
    g.add_production({"bvslt", bsort, vv,
        [&m](expr_ref_vector const& ch) { bv_util bv(m); return expr_ref(bv.mk_slt(ch[0], ch[1]), m); }});
    g.add_production({"bveq", bsort, vv,
        [&m](expr_ref_vector const& ch) { return expr_ref(m.mk_eq(ch[0], ch[1]), m); }});

    g.add_production({"ite_bv", bvsort, bvv,
        [&m](expr_ref_vector const& ch) { return expr_ref(m.mk_ite(ch[0], ch[1], ch[2]), m); }});
}

/**
 * Build a grammar over strings.
 */
inline void add_string_operators(Grammar& g) {
    ast_manager& m = g.mgr();
    seq_util seq(m);
    arith_util a(m);
    sort_ref ssort(seq.str.mk_string_sort(), m);
    sort_ref isort(a.mk_int(), m);
    sort_ref bsort(m.mk_bool_sort(), m);

    sort_ref_vector ss(m); ss.push_back(ssort); ss.push_back(ssort);
    sort_ref_vector s1(m); s1.push_back(ssort);
    sort_ref_vector si(m); si.push_back(ssort); si.push_back(isort);
    sort_ref_vector sii(m); sii.push_back(ssort); sii.push_back(isort); sii.push_back(isort);
    sort_ref_vector ssi(m); ssi.push_back(ssort); ssi.push_back(ssort); ssi.push_back(isort);
    sort_ref_vector sss(m); sss.push_back(ssort); sss.push_back(ssort); sss.push_back(ssort);
    sort_ref_vector i1(m); i1.push_back(isort);
    sort_ref_vector bss(m); bss.push_back(bsort); bss.push_back(ssort); bss.push_back(ssort);

    g.add_production({"str.++", ssort, ss,
        [&m](expr_ref_vector const& ch) { seq_util seq(m); return expr_ref(seq.str.mk_concat(ch[0], ch[1]), m); }});
    g.add_production({"str.len", isort, s1,
        [&m](expr_ref_vector const& ch) { seq_util seq(m); return expr_ref(seq.str.mk_length(ch[0]), m); }});
    g.add_production({"str.at", ssort, si,
        [&m](expr_ref_vector const& ch) {
            seq_util seq(m); arith_util a(m);
            return expr_ref(seq.str.mk_substr(ch[0], ch[1], a.mk_int(1)), m);
        }});
    g.add_production({"str.substr", ssort, sii,
        [&m](expr_ref_vector const& ch) { seq_util seq(m); return expr_ref(seq.str.mk_substr(ch[0], ch[1], ch[2]), m); }});
    g.add_production({"str.indexof", isort, ssi,
        [&m](expr_ref_vector const& ch) { seq_util seq(m); return expr_ref(seq.str.mk_index(ch[0], ch[1], ch[2]), m); }});
    g.add_production({"str.replace", ssort, sss,
        [&m](expr_ref_vector const& ch) { seq_util seq(m); return expr_ref(seq.str.mk_replace(ch[0], ch[1], ch[2]), m); }});
    g.add_production({"str.contains", bsort, ss,
        [&m](expr_ref_vector const& ch) { seq_util seq(m); return expr_ref(seq.str.mk_contains(ch[0], ch[1]), m); }});
    g.add_production({"str.prefixof", bsort, ss,
        [&m](expr_ref_vector const& ch) { seq_util seq(m); return expr_ref(seq.str.mk_prefix(ch[0], ch[1]), m); }});
    g.add_production({"str.suffixof", bsort, ss,
        [&m](expr_ref_vector const& ch) { seq_util seq(m); return expr_ref(seq.str.mk_suffix(ch[0], ch[1]), m); }});
    g.add_production({"int.to.str", ssort, i1,
        [&m](expr_ref_vector const& ch) { seq_util seq(m); return expr_ref(seq.str.mk_itos(ch[0]), m); }});
    g.add_production({"str.to.int", isort, s1,
        [&m](expr_ref_vector const& ch) { seq_util seq(m); return expr_ref(seq.str.mk_stoi(ch[0]), m); }});

    g.add_production({"ite_str", ssort, bss,
        [&m](expr_ref_vector const& ch) { return expr_ref(m.mk_ite(ch[0], ch[1], ch[2]), m); }});
}

} // namespace grammars

// ============================================================================
// Observational Equivalence Manager
// ============================================================================

/**
 * Evaluates candidate terms on a set of sample inputs and keeps only one
 * representative per equivalence class (the one encountered first).
 *
 * Uses Z3's model evaluation to reduce terms to concrete values.
 */
class OEManager {
public:
    OEManager(ast_manager& m) : m(m) {}

    void set_samples(vector<model_ref> samples) {
        m_samples = std::move(samples);
        m_seen.clear();
    }

    void add_sample(model_ref mdl) {
        m_samples.push_back(std::move(mdl));
        m_seen.clear();
    }

    /**
     * Returns true if `term` is a new representative (its fingerprint has
     * not been seen before).
     */
    bool is_representative(expr* term) {
        if (m_samples.empty()) return true;
        std::string fingerprint = compute_fingerprint(term);
        if (fingerprint.empty()) return false;
        return m_seen.insert(fingerprint).second;
    }

    void clear() { m_seen.clear(); }

    size_t num_classes() const { return m_seen.size(); }
    size_t num_samples() const { return m_samples.size(); }

private:
    ast_manager& m;
    vector<model_ref> m_samples;
    std::unordered_set<std::string> m_seen;

    std::string compute_fingerprint(expr* term) {
        std::string fp;
        for (auto& mdl : m_samples) {
            expr_ref val(m);
            model_evaluator eval(*mdl);
            eval.set_model_completion(true);
            if (!eval.eval(term, val, true))
                return "";
            std::ostringstream os;
            os << mk_pp(val, m);
            fp += os.str();
            fp += '\x1f';
        }
        return fp;
    }
};

// ============================================================================
// Term Bank - stores enumerated terms by height and sort
// ============================================================================

class TermBank {
public:
    TermBank(ast_manager& m) : m(m), m_pinned(m) {}

    void reset() {
        m_pinned.reset();
        m_terms.clear();
    }

    void add(expr* term, unsigned height) {
        sort* s = term->get_sort();
        unsigned sid = s->get_id();
        m_pinned.push_back(term);
        if (height >= m_terms.size()) 
            m_terms.resize(height + 1);
        m_terms[height].insert_if_not_there(s, ptr_vector<expr>()).push_back(term);
    }

    /** Get all terms of a given sort up to (and including) max_height */
    expr_ref_vector get_by_sort(sort* s, unsigned max_height) const {
        expr_ref_vector result(m);
        for (unsigned h = 0; h <= max_height; ++h) {
            if (h >= m_terms.size()) 
                break;
            if (!m_terms[h].contains(s))
                continue;
            for (auto t : m_terms[h].find(s))
                result.push_back(t);
        }
        return result;
    }

    size_t total_terms() const {
        size_t n = 0;
        for (auto& sm : m_terms)
            for (auto& [s, v] : sm)
                n += v.size();
        return n;
    }

private:
    ast_manager& m;
    expr_ref_vector m_pinned;
    // height -> sort -> terms
    vector<obj_map<sort, ptr_vector<expr>>> m_terms;
};

// ============================================================================
// Children Iterator - generates all combinations of child terms
// ============================================================================

/**
 * Iterates over all tuples (c1, c2, ..., cn) where each ci has the required
 * sort, drawn from the term bank, with at least one child at the current
 * height - 1 (to avoid regenerating previously seen terms).
 */
class ChildrenIterator {
public:
    ChildrenIterator(ast_manager& m, Production const& prod, TermBank const& bank, unsigned current_height)
        : m(m), m_prod(prod), m_current_height(current_height), m_done(false)
    {
        m_arity = prod.domain.size();
        if (m_arity == 0) {
            m_done = true;
            return;
        }
        for (unsigned i = 0; i < m_arity; ++i) {
            m_candidates.push_back(bank.get_by_sort(prod.domain[i], current_height - 1));
            if (m_candidates.back().empty()) {
                m_done = true;
                return;
            }
        }
        m_indices.resize(m_arity, 0);
    }

    bool has_next() {
        while (!m_done) {
            if (has_child_at_max_height()) 
                return true;
            advance();
        }
        return false;
    }

    expr_ref_vector next() {
        expr_ref_vector result(m);
        for (unsigned i = 0; i < m_arity; ++i)
            result.push_back(m_candidates[i].get(m_indices[i]));
        advance();
        return result;
    }

private:
    ast_manager& m;
    Production const& m_prod;
    unsigned m_current_height;
    unsigned m_arity;
    bool m_done;
    vector<expr_ref_vector> m_candidates;
    svector<unsigned> m_indices;

    bool has_child_at_max_height() const {
        return true;
    }

    void advance() {
        for (auto i = m_arity; i-- > 0;) {
            m_indices[i]++;
            if (m_indices[i] < m_candidates[i].size()) return;
            m_indices[i] = 0;
        }
        m_done = true;
    }
};

// ============================================================================
// Enumerator - the main bottom-up term enumeration engine
// ============================================================================

/**
 * Enumerates terms bottom-up by height, applying observational equivalence
 * pruning. Users iterate via has_next() / next(), or call enumerate_up_to().
 *
 * Usage:
 *   ast_manager m;
 *   Grammar g(m);
 *   // ... add productions ...
 *   OEManager oe(m);
 *   // ... set samples ...
 *   Enumerator en(g, oe);
 *   arith_util a(m);
 *   en.set_target_sort(a.mk_int());
 *   while (en.has_next()) {
 *       expr_ref term = en.next();
 *       // ... check if term satisfies specification ...
 *   }
 */
class Enumerator {
public:
    Enumerator(Grammar& grammar, OEManager& oe)
        : m_grammar(grammar), m(grammar.mgr()), m_oe(oe),
          m_bank(grammar.mgr()), m_height(0),
          m_leaf_idx(0), m_op_idx(0), m_state(State::Leaves),
          m_target_sort(nullptr), m_pending(grammar.mgr())
    {}

    void set_target_sort(sort* s) { m_target_sort = s; }
    void set_max_height(unsigned h) { m_max_height = h; }

    bool has_next() {
        if (m_pending) return true;
        m_pending = find_next();
        return m_pending != nullptr;
    }

    expr_ref next() {
        if (!m_pending)
            m_pending = find_next();
        expr_ref result(m_pending, m);
        m_pending = nullptr;
        return result;
    }

    expr_ref_vector enumerate_up_to(unsigned max_height) {
        m_max_height = max_height;
        expr_ref_vector results(m);
        while (has_next()) {
            results.push_back(next());
        }
        return results;
    }

    TermBank const& bank() const { return m_bank; }
    unsigned current_height() const { return m_height; }

    void reset() {
        m_height = 0;
        m_leaf_idx = 0;
        m_op_idx = 0;
        m_state = State::Leaves;
        m_bank.reset();
        m_oe.clear();
        m_pending = nullptr;
        m_children_iter.reset();
    }

private:
    enum class State { Leaves, Operators, Done };

    Grammar& m_grammar;
    ast_manager& m;
    OEManager& m_oe;
    TermBank m_bank;
    unsigned m_height;
    unsigned m_leaf_idx;
    unsigned m_op_idx;
    State m_state;
    sort* m_target_sort;
    expr_ref m_pending;
    std::unique_ptr<ChildrenIterator> m_children_iter;
    unsigned m_max_height = 100;

    bool sort_matches(expr* e) const {
        if (!m_target_sort) return true;
        return e->get_sort() == m_target_sort;
    }

    expr* find_next() {
        while (true) {
            switch (m_state) {
            case State::Leaves:
                while (m_leaf_idx < m_grammar.leaves().size()) {
                    Production const& prod = m_grammar.leaves()[m_leaf_idx];
                    m_leaf_idx++;
                    expr_ref_vector empty_args(m);
                    expr_ref term = prod.builder(empty_args);
                    if (m_oe.is_representative(term)) {
                        m_bank.add(term, 0);
                        if (sort_matches(term))
                            return term;
                    }
                }
                m_state = State::Operators;
                m_height = 1;
                m_op_idx = 0;
                m_children_iter.reset();
                break;

            case State::Operators: {
                expr* result = enumerate_operators();
                if (result) return result;
                m_height++;
                if (m_height > m_max_height) {
                    m_state = State::Done;
                    break;
                }
                m_op_idx = 0;
                m_children_iter.reset();
                break;
            }
            case State::Done:
                return nullptr;
            }
        }
    }

    expr* enumerate_operators() {
        auto const& ops = m_grammar.operators();
        while (true) {
            if (m_children_iter && m_children_iter->has_next()) {
                expr_ref_vector children = m_children_iter->next();
                Production const& prod = ops[m_op_idx - 1];
                expr_ref term = prod.builder(children);
                if (m_oe.is_representative(term)) {
                    m_bank.add(term, m_height);
                    if (sort_matches(term))
                        return term;
                }
                continue;
            }
            if (m_op_idx >= ops.size()) return nullptr;
            Production const& prod = ops[m_op_idx];
            m_op_idx++;
            m_children_iter = std::make_unique<ChildrenIterator>(m, prod, m_bank, m_height);
        }
    }
};

// ============================================================================
// CEGIS integration helper
// ============================================================================

/**
 * Counter-Example Guided Inductive Synthesis loop.
 * Combines the enumerator with a solver to verify candidates against a
 * specification.
 *
 * spec: a function (expr* candidate) -> expr_ref that returns the specification
 *       constraint (should be valid for a correct program).
 * variables: the free variables of the specification.
 */
class CEGISLoop {
public:
    CEGISLoop(Grammar& grammar, sort* target_sort,
              std::function<expr_ref(expr*)> spec,
              expr_ref_vector variables)
        : m(grammar.mgr()), m_grammar(grammar), m_oe(grammar.mgr()),
          m_enumerator(grammar, m_oe),
          m_spec(std::move(spec)), m_variables(std::move(variables))
    {
        m_enumerator.set_target_sort(target_sort);
        params_ref p;
        m_solver = mk_smt_solver(m, p, symbol::null);
    }

    /**
     * Run the CEGIS loop. Returns the synthesized term, or null expr_ref if
     * max_height is exceeded.
     */
    expr_ref synthesize(unsigned max_height = 10, unsigned max_restarts = 20) {
        m_enumerator.set_max_height(max_height);
        unsigned restarts = 0;
        
        while (m_enumerator.has_next()) {
            expr_ref candidate = m_enumerator.next();

            if (!satisfies_samples(candidate)) continue;

            expr_ref spec_expr = m_spec(candidate);
            m_solver->push();
            m_solver->assert_expr(m.mk_not(spec_expr));
            lbool result = m_solver->check_sat(0, nullptr);

            if (result == l_false) {
                m_solver->pop(1);
                return candidate;
            } else if (result == l_true) {
                model_ref cex;
                m_solver->get_model(cex);
                m_oe.add_sample(cex);
                m_samples.push_back(cex);
                m_solver->pop(1);
                restarts++;
                if (restarts > max_restarts) return expr_ref(m);
                m_enumerator.reset();
            } else {
                m_solver->pop(1);
            }
        }
        return expr_ref(m);
    }

    size_t num_samples() const { return m_oe.num_samples(); }
    size_t num_equivalence_classes() const { return m_oe.num_classes(); }

private:
    ast_manager& m;
    Grammar& m_grammar;
    OEManager m_oe;
    Enumerator m_enumerator;
    std::function<expr_ref(expr*)> m_spec;
    expr_ref_vector m_variables;
    ref<solver> m_solver;
    vector<model_ref> m_samples;

    bool satisfies_samples(expr* candidate) {
        expr_ref spec_expr = m_spec(candidate);
        for (auto& mdl : m_samples) {
            model_evaluator eval(*mdl);
            eval.set_model_completion(true);
            if (eval.is_false(spec_expr))
                return false;
        }
        return true;
    }
};

} // namespace term_enum

// ============================================================================
// term_enumeration public interface implementation
// ============================================================================

struct term_enumeration::imp {
    ast_manager&                  m;
    term_enum::Grammar            m_grammar;
    term_enum::OEManager          m_oe;
    term_enum::Enumerator         m_enumerator;
    std::function<unsigned(expr*)> m_cost;

    imp(ast_manager& m) :
        m(m), m_grammar(m), m_oe(m), m_enumerator(m_grammar, m_oe) {}

    void add_production(func_decl* f) {
        m_grammar.add_func_decl(f);
    }

    void add_production(expr* e) {
        m_grammar.add_expr(e);
    }

    void set_cost(std::function<unsigned(expr*)> const& cost) {
        m_cost = cost;
    }

    // Enumerate terms of given sort up to a height, ordered by cost.
    // Returns the next term in cost order, or nullptr if exhausted at current height.
    expr* next_term(sort* s, unsigned& height_state, unsigned& idx_state,
                    vector<expr_ref_vector>& levels) {
        // Expand levels as needed
        while (idx_state >= level_size(levels, height_state)) {
            height_state++;
            if (height_state > 100)
                return nullptr;
            expand_level(s, height_state, levels);
            idx_state = 0;
            if (level_size(levels, height_state) > 0)
                break;
        }
        if (height_state >= levels.size() || idx_state >= levels[height_state].size())
            return nullptr;
        return levels[height_state][idx_state++];
    }

private:
    unsigned level_size(vector<expr_ref_vector> const& levels, unsigned h) const {
        if (h >= levels.size()) return 0;
        return levels[h].size();
    }

    void expand_level(sort* s, unsigned height, vector<expr_ref_vector>& levels) {
        if (height >= levels.size())
            levels.resize(height + 1, expr_ref_vector(m));

        // Collect terms at this height
        if (height == 0) {
            // Leaves
            for (auto const& prod : m_grammar.leaves()) {
                if (prod.range.get() != s) continue;
                expr_ref_vector empty_args(m);
                expr_ref term = prod.builder(empty_args);
                if (m_oe.is_representative(term)) {
                    m_enumerator.bank();  // just to ensure bank is populated
                    levels[0].push_back(term);
                }
            }
        }
        else {
            // Operators
            for (auto const& prod : m_grammar.operators()) {
                if (prod.range.get() != s) continue;
                term_enum::ChildrenIterator iter(m, prod, m_enumerator.bank(), height);
                while (iter.has_next()) {
                    expr_ref_vector children = iter.next();
                    expr_ref term = prod.builder(children);
                    if (m_oe.is_representative(term))
                        levels[height].push_back(term);
                }
            }
        }

        // Sort by cost if cost function is set
        if (m_cost && !levels[height].empty()) {
            expr_ref_vector& lv = levels[height];
            std::sort(lv.data(), lv.data() + lv.size(),
                      [&](expr* a, expr* b) { return m_cost(a) < m_cost(b); });
        }
    }
};

// -- iterator implementation --

struct term_enumeration::iterator::iter_imp {
    imp&                    m_imp;
    sort*                   m_sort;
    unsigned                m_height;
    unsigned                m_idx;
    vector<expr_ref_vector> m_levels;
    expr*                   m_current;
    bool                    m_end;

    iter_imp(imp& i, sort* s) :
        m_imp(i), m_sort(s), m_height(0), m_idx(0), m_current(nullptr), m_end(false) {
        expand_current_level();
        advance_to_valid();
    }

    // Sentinel constructor
    iter_imp(imp& i) :
        m_imp(i), m_sort(nullptr), m_height(0), m_idx(0), m_current(nullptr), m_end(true) {}

    void expand_current_level() {
        if (m_height >= m_levels.size())
            m_levels.resize(m_height + 1, expr_ref_vector(m_imp.m));

        if (!m_levels[m_height].empty())
            return;

        if (m_height == 0) {
            for (auto const& prod : m_imp.m_grammar.leaves()) {
                if (prod.range.get() != m_sort) continue;
                expr_ref_vector empty_args(m_imp.m);
                expr_ref term = prod.builder(empty_args);
                if (m_imp.m_oe.is_representative(term))
                    m_levels[0].push_back(term);
            }
        }
        else {
            for (auto const& prod : m_imp.m_grammar.operators()) {
                if (prod.range.get() != m_sort) continue;
                term_enum::ChildrenIterator iter(m_imp.m, prod, m_imp.m_enumerator.bank(), m_height);
                while (iter.has_next()) {
                    expr_ref_vector children = iter.next();
                    expr_ref term = prod.builder(children);
                    if (m_imp.m_oe.is_representative(term))
                        m_levels[m_height].push_back(term);
                }
            }
        }

        // Sort by cost if cost function is set
        if (m_imp.m_cost && !m_levels[m_height].empty()) {
            expr_ref_vector& lv = m_levels[m_height];
            std::sort(lv.data(), lv.data() + lv.size(),
                      [&](expr* a, expr* b) { return m_imp.m_cost(a) < m_imp.m_cost(b); });
        }
    }

    void advance_to_valid() {
        while (true) {
            if (m_height >= m_levels.size())
                expand_current_level();
            if (m_idx < m_levels[m_height].size()) {
                m_current = m_levels[m_height][m_idx];
                return;
            }
            m_height++;
            m_idx = 0;
            if (m_height > 100) {
                m_end = true;
                m_current = nullptr;
                return;
            }
            expand_current_level();
        }
    }

    void advance() {
        if (m_end) return;
        m_idx++;
        advance_to_valid();
    }
};

term_enumeration::iterator::iterator(imp& i, sort* s) {
    m_imp = alloc(iter_imp, i, s);
}

term_enumeration::iterator::iterator(std::nullptr_t) {
    m_imp = nullptr;
}

term_enumeration::iterator::iterator(iterator const& other) {
    m_imp = nullptr;
    if (other.m_imp)
        m_imp = alloc(iter_imp, *other.m_imp);
}

term_enumeration::iterator& term_enumeration::iterator::operator=(iterator const& other) {
    if (this != &other) {
        dealloc(m_imp);
        m_imp = nullptr;
        if (other.m_imp)
            m_imp = alloc(iter_imp, *other.m_imp);
    }
    return *this;
}

term_enumeration::iterator::~iterator() {
    dealloc(m_imp);
}

expr* term_enumeration::iterator::operator*() {
    return m_imp ? m_imp->m_current : nullptr;
}

term_enumeration::iterator& term_enumeration::iterator::operator++() {
    if (m_imp) m_imp->advance();
    return *this;
}

term_enumeration::iterator term_enumeration::iterator::operator++(int) {
    iterator tmp(*this);
    ++(*this);
    return tmp;
}

bool term_enumeration::iterator::operator!=(iterator const& other) const {
    if (!m_imp && !other.m_imp) return false;
    if (!m_imp) return !other.m_imp->m_end;
    if (!other.m_imp) return !m_imp->m_end;
    return m_imp->m_end != other.m_imp->m_end ||
           m_imp->m_current != other.m_imp->m_current;
}

// -- terms implementation --

term_enumeration::terms::terms(imp* i, sort* s) : m_imp(i), m_sort(s) {}

term_enumeration::iterator term_enumeration::terms::begin() {
    return iterator(*m_imp, m_sort);
}

term_enumeration::iterator term_enumeration::terms::end() {
    return iterator(nullptr);
}

// -- term_enumeration implementation --

term_enumeration::term_enumeration(ast_manager& m) {
    m_imp = alloc(imp, m);
}

term_enumeration::~term_enumeration() {
    dealloc(m_imp);
}

void term_enumeration::add_production(func_decl* f) {
    m_imp->add_production(f);
}

void term_enumeration::add_production(expr* e) {
    m_imp->add_production(e);
}

void term_enumeration::set_cost(std::function<unsigned(expr*)> const& cost) {
    m_imp->set_cost(cost);
}

term_enumeration::terms term_enumeration::enum_terms(sort* s) {
    return terms(m_imp, s);
}
