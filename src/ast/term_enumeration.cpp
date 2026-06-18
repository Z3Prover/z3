/**
 * term_enumeration.cpp - Bottom-up term enumeration module for Z3
 *
 * Inspired by the Probe synthesizer (Barke et al., "Just-in-Time Learning
 * for Bottom-Up Enumerative Synthesis"). Adapted to use Z3's internal APIs.
 *
 * Key ideas:
 *   - Terms are enumerated bottom-up by "cost" (calculated by tree size).
 *   - Observational equivalence (OE): two terms that produce the same outputs
 *     on all sample inputs are considered equivalent; only one representative
 *     per equivalence class is kept.
 *   - A grammar describes which function symbols (operators) and leaves
 *     (constants, variables) are available for enumeration.
 */

#include <sstream>
#include <unordered_set>
#include <functional>
#include <string>
#include "util/vector.h"
#include "util/ref.h"
#include "util/obj_hashtable.h"
#include "ast/ast.h"
#include "ast/ast_ll_pp.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "ast/term_enumeration.h"
#include "model/model.h"
#include "model/model_evaluator.h"


namespace term_enum {

// ============================================================================
// grammar production rule
// ============================================================================

/**
 * A production describes how to construct a term from child terms.
 * - domain: the sort required for each child
 * - range: the sort of the produced term
 * - builder: given a vector of child exprs, produce the result expr
 */
struct production {
    std::string name;
    sort_ref range;
    sort_ref_vector domain;
    std::function<expr_ref(expr_ref_vector const&)> builder;

    bool is_leaf() const { return domain.empty(); }
};

// ============================================================================
// grammar
// ============================================================================

/**
 * A grammar groups productions into leaves (arity 0) and operators (arity > 0).
 */
class grammar {
public:
    grammar(ast_manager& m) : m(m) {}

    void add_production(production p) {
        if (p.is_leaf())
            m_leaves.push_back(std::move(p));
        else
            m_operators.push_back(std::move(p));
    }

    vector<production> const& leaves() const { return m_leaves; }
    vector<production> const& operators() const { return m_operators; }
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
    vector<production> m_leaves;
    vector<production> m_operators;
};

// ============================================================================
// Observational Equivalence Manager
// ============================================================================

/**
 * Evaluates candidate terms on a set of sample inputs and keeps only one
 * representative per equivalence class (the one encountered first).
 *
 * Uses Z3's model evaluation to reduce terms to concrete values.
 */
class oe_manager {
public:
    oe_manager(ast_manager& m) : m(m) {}

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
        auto fingerprint = compute_fingerprint(term);
        if (fingerprint == 0) 
            return false;
        return m_seen.insert(fingerprint).second;
    }

    void clear() { m_seen.clear(); }

    size_t num_classes() const { return m_seen.size(); }
    unsigned num_samples() const { return m_samples.size(); }

private:
    ast_manager& m;
    vector<model_ref> m_samples;
    std::unordered_set<uint64_t> m_seen;

    uint64_t compute_fingerprint(expr* term) {
        uint64_t a = 1, b = 2, c = 0;
        for (auto& mdl : m_samples) {
            expr_ref val(m);
            model_evaluator eval(*mdl);
            eval.set_model_completion(true);
            if (!eval.eval(term, val, true))
                continue;
            a *= val->hash();
            mix(a, b, c);
        }
        return c;
    }
};

// ============================================================================
// Term Bank - stores enumerated terms by cost and sort
// ============================================================================

using cost_terms = vector<std::pair<expr*, unsigned>>;

class term_bank {
    using sort_term_map = obj_map<sort, ptr_vector<expr>>;
public:
    term_bank(ast_manager& m) : m(m), m_pinned(m) {}

    ~term_bank() {
        for (auto s : m_terms)
            dealloc(s);
    }

    void reset() {
        m_pinned.reset();
        m_terms.clear();
    }

    void add(expr* term, unsigned cost) {
        sort* s = term->get_sort();
        m_pinned.push_back(term);
        if (cost >= m_terms.size()) 
            m_terms.resize(cost + 1);
        if (!m_terms[cost])
            m_terms[cost] = alloc(sort_term_map);
        m_terms[cost]->insert_if_not_there(s, ptr_vector<expr>()).push_back(term);
    }

    /** Get all terms of a given sort up to (and including) max_cost */
    cost_terms get_by_sort(sort* s, unsigned max_cost) const {
        cost_terms result;
        for (unsigned c = 0; c <= max_cost; ++c) {
            if (c >= m_terms.size()) 
                break;
            if (!m_terms[c]->contains(s))
                continue;
            for (auto t : m_terms[c]->find(s))
                result.push_back({t, c});
        }
        return result;
    }

    ptr_vector<expr> null_ptr_vector;
    ptr_vector<expr> const &get_by_cost_and_sort(unsigned cost, sort *s) const {
        if (cost >= m_terms.size() || !m_terms[cost] || !m_terms[cost]->contains(s))
            return null_ptr_vector;
        return m_terms[cost]->find(s);
    } 

private:
    ast_manager& m;
    expr_ref_vector m_pinned;
    // cost -> sort -> terms
    ptr_vector<sort_term_map> m_terms;
};

// ============================================================================
// Children Iterator - generates all combinations of child terms
// ============================================================================

/**
 * Iterates over all tuples (c1, c2, ..., cn) where each ci has the required
 * sort, drawn from the term bank, with at least one child at the current
 * cost - 1 (to avoid regenerating previously seen terms).
 */
class children_iterator {
public:
    children_iterator(ast_manager& m, production const& prod, term_bank const& bank, unsigned current_cost)
        : m(m), m_prod(prod), m_current_cost(current_cost), m_done(false)
    {
        m_arity = prod.domain.size();
        if (m_arity == 0) {
            m_done = true;
            return;
        }
        for (unsigned i = 0; i < m_arity; ++i) {
            m_candidates.push_back(bank.get_by_sort(prod.domain[i], current_cost - 1));
            if (m_candidates.back().empty()) {
                m_done = true;
                return;
            }
        }
        m_indices.resize(m_arity, 0);
    }

    bool has_next(unsigned cost) {
        while (!m_done) {
            if (has_child_at_cost(cost)) 
                return true;
            advance();
        }
        return false;
    }

    expr_ref_vector next(unsigned& cost) {
        expr_ref_vector result(m);
        cost = 1;
        for (unsigned i = 0; i < m_arity; ++i) {
            auto [e, c] = m_candidates[i].get(m_indices[i]);
            cost += c;
            result.push_back(e);
        }
        advance();
        return result;
    }

private:
    ast_manager& m;
    production const& m_prod;
    unsigned m_current_cost;
    unsigned m_arity;
    bool m_done;
    vector<cost_terms> m_candidates;
    svector<unsigned> m_indices;

    bool has_child_at_cost(unsigned cost) const {
        for (unsigned i = 0; i < m_arity; ++i) {
            auto [e, c] = m_candidates[i].get(m_indices[i]);
            if (c + 1 == cost)
                return true;
        }
        return false;
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
// bottom_up_enumerator - the main bottom-up term enumeration engine
// ============================================================================

/**
 * Enumerates terms bottom-up by cost, applying observational equivalence
 * pruning. Users iterate via has_next() / next().
 *
 * Usage:
 *   ast_manager m;
 *   grammar g(m);
 *   // ... add productions ...
 *   oe_manager oe(m);
 *   // ... set samples ...
 *   bottom_up_enumerator en(g, oe);
 *   arith_util a(m);
 *   en.set_target_sort(a.mk_int());
 *   while (en.has_next()) {
 *       expr_ref term = en.next();
 *       // ... check if term satisfies specification ...
 *   }
 */
class bottom_up_enumerator {
public:
    bottom_up_enumerator(grammar& grammar, oe_manager& oe)
        : m_grammar(grammar), m(grammar.mgr()), m_oe(oe),
          m_bank(grammar.mgr()), m_pending(grammar.mgr())
    {}

    void set_target_sort(sort* s) { m_target_sort = s; }

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

    term_bank const& bank() const { return m_bank; }

    void reset() {
        m_cost = 0;
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

    grammar& m_grammar;
    ast_manager& m;
    oe_manager& m_oe;
    term_bank m_bank;
    unsigned m_cost = 0;
    unsigned m_leaf_idx = 0;
    unsigned m_op_idx = 0;
    unsigned m_bank_idx = 0;
    unsigned m_bank_size = 0;
    State m_state = State::Leaves;
    sort* m_target_sort = nullptr;
    expr_ref m_pending;
    std::unique_ptr<children_iterator> m_children_iter;

    bool sort_matches(expr* e) const {
        return !m_target_sort || e->get_sort() == m_target_sort;
    }

    expr* find_next() {
        while (true) {
            switch (m_state) {
            case State::Leaves:
                while (m_leaf_idx < m_grammar.leaves().size()) {
                    production const& prod = m_grammar.leaves()[m_leaf_idx];
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
                m_cost = 1;
                m_op_idx = 0;
                m_bank_idx = 0;
                m_bank_size = get_bank_size();                
                m_children_iter.reset();
                break;

            case State::Operators: {
                expr* result = enumerate_operators();
                if (result) 
                    return result;
                m_cost++;
                m_op_idx = 0;
                m_bank_idx = 0;
                m_bank_size = get_bank_size();
                m_children_iter.reset();
                break;
            }
            case State::Done:
                return nullptr;
            }
        }
    }

    unsigned get_bank_size() const {
        auto const &terms = m_bank.get_by_cost_and_sort(m_cost, m_target_sort);
        return terms.size();
    }

    expr *enumerate_operators() {
        auto const &ops = m_grammar.operators();
        while (true) {

            // first find terms at m_cost that were already created
            if (m_bank_idx < m_bank_size) {
                auto const &terms = m_bank.get_by_cost_and_sort(m_cost, m_target_sort);
                auto t = terms.get(m_bank_idx);
                m_bank_idx++;
                SASSERT(sort_matches(t));
                return t;                
            }

            // then create new terms using children at cost below current m_cost.
            if (m_children_iter && m_children_iter->has_next(m_cost)) {
                unsigned new_cost = 0;
                expr_ref_vector children = m_children_iter->next(new_cost);
                production const &prod = ops[m_op_idx - 1];
                expr_ref term = prod.builder(children);
                SASSERT(new_cost >= m_cost);
                if (m_oe.is_representative(term)) {
                    m_bank.add(term, new_cost);
                    if (sort_matches(term) && new_cost == m_cost)
                        return term;
                }
                continue;
            }
            if (m_op_idx >= ops.size())
                return nullptr;
            production const &prod = ops[m_op_idx];
            m_op_idx++;
            m_children_iter = std::make_unique<children_iterator>(m, prod, m_bank, m_cost);
        }
    }
};

} // namespace term_enum

// ============================================================================
// term_enumeration public interface implementation
// ============================================================================

struct term_enumeration::imp {
    ast_manager&                  m;
    term_enum::grammar            m_grammar;
    term_enum::oe_manager          m_oe;
    term_enum::bottom_up_enumerator         m_bottom_up_enumerator;
    std::function<unsigned(expr*)> m_cost;

    imp(ast_manager& m) :
        m(m), m_grammar(m), m_oe(m), m_bottom_up_enumerator(m_grammar, m_oe) {}

    void add_production(func_decl* f) {
        m_grammar.add_func_decl(f);
    }

    void add_production(expr* e) {
        m_grammar.add_expr(e);
    }

    void set_cost(std::function<unsigned(expr*)> const& cost) {
        m_cost = cost;
    }

    // Enumerate terms of given sort up to a cost, ordered by cost.
    // Returns the next term in cost order, or nullptr if exhausted at current cost.
    expr* next_term(sort* s, unsigned& cost_state, unsigned& idx_state,
                    vector<expr_ref_vector>& levels) {
        // Expand levels as needed
        while (idx_state >= level_size(levels, cost_state)) {
            cost_state++;
            expand_level(s, cost_state, levels);
            idx_state = 0;
            if (level_size(levels, cost_state) > 0)
                break;
        }
        if (cost_state >= levels.size() || idx_state >= levels[cost_state].size())
            return nullptr;
        return levels[cost_state].get(idx_state++);
    }

private:
    unsigned level_size(vector<expr_ref_vector> const& levels, unsigned cost) const {
        if (cost >= levels.size()) return 0;
        return levels[cost].size();
    }

    void expand_level(sort* s, unsigned cost, vector<expr_ref_vector>& levels) {
        if (cost >= levels.size())
            levels.resize(cost + 1, expr_ref_vector(m));

        // Collect terms at this cost
        if (cost == 0) {
            // Leaves
            for (auto const& prod : m_grammar.leaves()) {
                if (prod.range.get() != s) continue;
                expr_ref_vector empty_args(m);
                expr_ref term = prod.builder(empty_args);
                if (m_oe.is_representative(term)) {
                    m_bottom_up_enumerator.bank();  // just to ensure bank is populated
                    levels[0].push_back(term);
                }
            }
        }
        else {
            // operators
            for (auto const& prod : m_grammar.operators()) {
                if (prod.range.get() != s) continue;
                term_enum::children_iterator iter(m, prod, m_bottom_up_enumerator.bank(), cost);
                while (iter.has_next(cost)) {
                    unsigned new_cost = 0;
                    expr_ref_vector children = iter.next(new_cost);
                    expr_ref term = prod.builder(children);
                    levels.reserve(new_cost + 1, expr_ref_vector(m));
                    if (m_oe.is_representative(term))
                        levels[new_cost].push_back(term);
                }
            }
        }

        // Sort by cost if cost function is set
        if (m_cost && !levels[cost].empty()) {
            expr_ref_vector& lv = levels[cost];
            std::sort(lv.data(), lv.data() + lv.size(),
                      [&](expr* a, expr* b) { return m_cost(a) < m_cost(b); });
        }
    }
};

// -- iterator implementation --

struct term_enumeration::iterator::iter_imp {
    imp&                    m_imp;
    sort*                   m_sort;
    unsigned                m_cost = 0;
    unsigned                m_idx = 0;
    vector<expr_ref_vector> m_levels;
    expr*                   m_current = nullptr;
    bool                    m_end;

    iter_imp(imp& i, sort* s) : m_imp(i), m_sort(s), m_end(false) {
        expand_current_level();
        advance_to_valid();
    }

    // Sentinel constructor
    iter_imp(imp& i) :
        m_imp(i), m_sort(nullptr), m_end(true) {}

    void expand_current_level() {
        if (m_cost >= m_levels.size())
            m_levels.resize(m_cost + 1, expr_ref_vector(m_imp.m));

        if (!m_levels[m_cost].empty())
            return;

        if (m_cost == 0) {
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
                term_enum::children_iterator iter(m_imp.m, prod, m_imp.m_bottom_up_enumerator.bank(), m_cost);
                while (iter.has_next(m_cost)) {
                    unsigned new_cost = 0;
                    expr_ref_vector children = iter.next(new_cost);
                    expr_ref term = prod.builder(children);
                    m_levels.reserve(new_cost + 1, expr_ref_vector(m_imp.m));
                    if (m_imp.m_oe.is_representative(term))
                        m_levels[new_cost].push_back(term);
                }
            }
        }

        // Sort by cost if cost function is set
        if (m_imp.m_cost && !m_levels[m_cost].empty()) {
            expr_ref_vector& lv = m_levels[m_cost];
            std::sort(lv.data(), lv.data() + lv.size(),
                      [&](expr* a, expr* b) { return m_imp.m_cost(a) < m_imp.m_cost(b); });
        }
    }

    void advance_to_valid() {
        while (true) {
            if (m_cost >= m_levels.size())
                expand_current_level();
            if (m_idx < m_levels[m_cost].size()) {
                m_current = m_levels[m_cost].get(m_idx);
                return;
            }
            m_cost++;
            m_idx = 0;
            if (m_cost > 100) {
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
