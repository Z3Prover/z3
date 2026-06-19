/**
 * term_enumeration.cpp - Bottom-up term enumeration module for Z3
 *
 * Inspired by the Probe synthesizer (Barke et al., "Just-in-Time Learning
 * for Bottom-Up Enumerative Synthesis"). Adapted to use Z3's internal APIs.
 *
 * Key ideas:
 *   - Terms are enumerated bottom-up by "cost" (calculated by tree size).
 *   - A grammar describes which function symbols (operators) and leaves
 *     (constants, variables) are available for enumeration.
 */

#include <sstream>
#include <functional>
#include <string>
#include "util/vector.h"
#include "util/scoped_ptr_vector.h"
#include "util/obj_hashtable.h"
#include "util/uint_set.h"
#include "ast/ast.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/term_enumeration.h"


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
    grammar(ast_manager& m) : m(m), m_pinned(m) {}

    void add_production(production* p) {
        if (p->is_leaf())
            m_leaves.push_back(p);
        else
            m_operators.push_back(p);
    }

    scoped_ptr_vector<production> const& leaves() const { return m_leaves; }
    scoped_ptr_vector<production> const& operators() const { return m_operators; }
    ast_manager& mgr() const { return m; }

    void add_func_decl(func_decl *f) {
        if (m_seen.contains(f))
            return;
        m_pinned.push_back(f);
        m_seen.insert(f);
        sort_ref range(f->get_range(), m);
        sort_ref_vector dom(m);
        for (unsigned i = 0; i < f->get_arity(); ++i)
            dom.push_back(sort_ref(f->get_domain(i), m));
        add_production(alloc(production, {f->get_name().str(), range, dom, [this, f](expr_ref_vector const &args) {
                            return expr_ref(m.mk_app(f, args), m);
                        }}));
    }

    void add_expr(expr *e) {
        if (m_seen.contains(e))
            return;
        m_pinned.push_back(e);
        m_seen.insert(e);
        sort_ref range(e->get_sort(), m);
        sort_ref_vector dom(m);
        std::stringstream ss;
        ss << mk_bounded_pp(e, m);
        std::string name = ss.str();
        add_production(alloc(production, {name, range, dom, [this, e](expr_ref_vector const&) { return expr_ref(e, m); }}));
    }

    std::ostream& display(std::ostream& out) const {
        out << "Leaves:\n";
        for (auto const *p : m_leaves) {
            out << "  " << p->name << " : " << mk_pp(p->range, m) << "\n";
        }
        out << "Operators:\n";
        for (auto const *p : m_operators) {
            out << "  " << p->name << " : (";
            for (unsigned i = 0; i < p->domain.size(); ++i) {
                if (i > 0)
                    out << ", ";
                out << mk_pp(p->domain[i], m);
            }
            out << ") -> " << mk_pp(p->range, m) << "\n";
        }
        return out;
    }

private:
    ast_manager& m;
    ast_ref_vector m_pinned;
    scoped_ptr_vector<production> m_leaves;
    scoped_ptr_vector<production> m_operators;
    obj_hashtable<ast> m_seen;
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

    // Return true if there is at least one term at/above `cost` whose sort is
    // not in `sorts` (i.e., enumeration can still produce a new requested sort).
    bool is_productive(unsigned cost, uint_set const& sorts) {
        for (unsigned i = cost; i < m_terms.size(); ++i) {
            if (!m_terms[i])
                continue;
            for (auto const& entry : *m_terms[i]) {
                sort* term_sort = entry.m_key;
                if (!sorts.contains(term_sort->get_small_id()))
                    return true;
            }
        }
        return false;
    }

    ptr_vector<expr> null_ptr_vector;
    ptr_vector<expr> const &get_by_cost_and_sort(unsigned cost, sort *s) const {
        if (cost >= m_terms.size() || !m_terms[cost] || !m_terms[cost]->contains(s))
            return null_ptr_vector;
        return m_terms[cost]->find(s);
    } 

    std::ostream& display(std::ostream& out) const {
        for (unsigned cost = 0; cost < m_terms.size(); ++cost) {
            if (!m_terms[cost])
                continue;
            out << "cost " << cost << ":\n";
            for (auto& [s, terms] : *m_terms[cost]) {
                out << " sort " << mk_pp(s, m) << ":\n";
                for (expr* e : terms) {
                    out << "  #" << e->get_id() << " ";
                    if (cost == 0) {
                        out << mk_bounded_pp(e, m);
                    }
                    else if (is_app(e)) {
                        app* a = to_app(e);
                        out << a->get_decl()->get_name() << "(";
                        bool first = true;
                        for (expr* arg : *a) {
                            if (!first) out << ", ";
                            first = false;
                            out << "#" << arg->get_id();
                        }
                        out << ")";
                    }
                    out << "\n";
                }
            }
        }
        return out;
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


class bottom_up_enumerator {
public:
    bottom_up_enumerator(grammar& grammar)
        : m_grammar(grammar), m(grammar.mgr()), 
          m_bank(grammar.mgr()), m_pending(grammar.mgr()), m_rewriter(grammar.mgr())
    {}

    void set_target_sort(sort *s) {
        m_target_sort = s;
    }
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

    std::ostream& display(std::ostream& out) const {
        m_grammar.display(out);
        return m_bank.display(out);
    }

    void reset() {
        m_cost = 0;
        m_leaf_idx = 0;
        m_op_idx = 0;
        m_state = State::Leaves;
        m_bank.reset();
        m_pending = nullptr;
        m_rewriter.reset();
        m_seen_terms.reset();
        m_children_iter.reset();
    }

    expr* add_term(expr_ref const& term, unsigned cost) {
        expr_ref simplified(m);
        m_rewriter(term, simplified);
        if (m_seen_terms.contains(simplified))
            return nullptr;
        m_seen_terms.insert(simplified);
        m_bank.add(simplified, cost);
        return simplified;
    }

private:
    enum class State { Leaves, Operators, Done };

    grammar& m_grammar;
    ast_manager& m;
    term_bank m_bank;
    unsigned m_cost = 0;
    unsigned m_leaf_idx = 0;
    unsigned m_op_idx = 0;
    unsigned m_bank_idx = 0;
    unsigned m_bank_size = 0;
    bool m_made_progress = false;   
    uint_set m_sorts_produced;
    State m_state = State::Leaves;
    expr_ref m_pending;
    th_rewriter m_rewriter;
    obj_hashtable<expr> m_seen_terms;
    std::unique_ptr<children_iterator> m_children_iter;
    sort *m_target_sort = nullptr;

    bool sort_matches(expr* e) const {
        return !m_target_sort || e->get_sort() == m_target_sort;
    }

    expr* find_next() {
        while (true) {
            switch (m_state) {
            case State::Leaves:
                while (m_leaf_idx < m_grammar.leaves().size()) {
                    production const &prod = *m_grammar.leaves()[m_leaf_idx];
                    m_leaf_idx++;
                    expr_ref_vector empty_args(m);
                    expr_ref term = prod.builder(empty_args);
                    expr* r = add_term(term, 0);
                    if (r && sort_matches(r)) 
                        return r;                    
                }
                m_state = State::Operators;
                m_cost = 1;
                m_op_idx = 0;
                m_bank_idx = 0;
                m_bank_size = get_bank_size();      
                m_made_progress = false;
                m_sorts_produced.reset();
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
                if (!m_made_progress && !m_bank.is_productive(m_cost, m_sorts_produced)) {
                    m_state = State::Done;
                    return nullptr;
                }
                if (m_sorts_produced.contains(m_target_sort->get_small_id())) 
                    m_sorts_produced.reset();                
                m_made_progress = false;
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
                production const &prod = *ops[m_op_idx - 1];
                expr_ref term = prod.builder(children);
                // IF_VERBOSE(0, verbose_stream() << term << "\n");
                SASSERT(new_cost >= m_cost);
                expr* r = add_term(term, new_cost);
                if (!r)
                    continue;
                unsigned sort_id = r->get_sort()->get_small_id();
                if (!m_sorts_produced.contains(sort_id))
                    m_made_progress = true;
                m_sorts_produced.insert(sort_id);
                if (sort_matches(r) && new_cost == m_cost) {
                    return r;
                }                
                continue;
            }

            if (m_op_idx >= ops.size())                 
                return nullptr;
            
            production const &prod = *ops[m_op_idx];
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
    term_enum::bottom_up_enumerator         m_bottom_up_enumerator;
    std::function<unsigned(expr*)> m_cost;

    imp(ast_manager& m) :
        m(m), m_grammar(m), m_bottom_up_enumerator(m_grammar) {}

    void add_production(func_decl* f) {
        m_grammar.add_func_decl(f);
    }

    void add_production(expr* e) {
        m_grammar.add_expr(e);
    }

    void set_cost(std::function<unsigned(expr*)> const& cost) {
        // TODO
    }

    std::ostream& display(std::ostream& out) const {
        return m_bottom_up_enumerator.display(out);
    }
};

// -- iterator implementation --

struct term_enumeration::iterator::iter_imp {
    imp&                    m_imp;
    ast_manager &           m;
    sort*                   m_sort;
    unsigned                m_cost = 0;
    unsigned                m_idx = 0;
    vector<expr_ref_vector> m_levels;
    expr_ref                m_current;
    bool                    m_end;
    vector<expr_ref_vector> m_vars;
    vector<ptr_vector<sort>> m_decls;
    vector<vector<symbol>> m_names;

    iter_imp(imp& i, sort* s) : m_imp(i), m(i.m), m_sort(s), m_current(i.m), m_end(false) {  
        m_imp.m_bottom_up_enumerator.reset();
        init_sort();
        advance();
    }
    
    // Sentinel constructor
    iter_imp(imp& i) :
        m_imp(i), m(i.m), m_sort(nullptr), m_current(i.m), m_end(true) {
        UNREACHABLE();
    }


    void init_sort() {
        array_util autil(m);
        sort *range = m_sort;

        while (autil.is_array(range)) {
            m_vars.push_back(expr_ref_vector(m));
            m_decls.push_back(ptr_vector<sort>());
            m_names.push_back(vector<symbol>());
            for (unsigned i = 0; i < get_array_arity(range); ++i) {
                m_decls.back().push_back(get_array_domain(range, i));
                m_vars.back().push_back(nullptr);
                m_names.back().push_back(symbol());
            }

            expr_ref_vector args(m);
            args.push_back(m.mk_const("a", range));
            for (unsigned i = 0; i < m_decls.back().size(); ++i) {
                args.push_back(m.mk_var(i, m_decls.back().get(i)));
            }
            app_ref sel(autil.mk_select(args), m);
            m_imp.m_grammar.add_func_decl(sel->get_decl());
            
            range = get_array_range(range);
        }
        unsigned n = 0;
        for (unsigned i = m_decls.size(); i-- > 0;) {
            for (unsigned j = m_decls[i].size(); j-- > 0;) {
                m_vars[i][j] = m.mk_var(n, m_decls[i][j]);
                m_names[i][j] = symbol(n);
                m_imp.add_production(m_vars[i].get(j));
                n++;
            }
        }
        m_sort = range;
        m_imp.m_bottom_up_enumerator.set_target_sort(range);
    }
    
    void mk_lambda() {
        if (!m_current)
            return;
        for (unsigned i = m_decls.size(); i-- > 0;)
            m_current = m.mk_lambda(m_decls[i].size(), m_decls[i].data(), m_names[i].data(), m_current);
    }

    void advance() {
        if (m_end) 
            return;
        m_current = m_imp.m_bottom_up_enumerator.next();
        SASSERT(!m_current || m_current->get_sort() == m_sort);
        mk_lambda();
        if (!m_current)
            m_end = true;
    }
};

term_enumeration::iterator::iterator(imp& i, sort* s) {
    m_imp = alloc(iter_imp, i, s);
}

term_enumeration::iterator::iterator(std::nullptr_t) {
    m_imp = nullptr;
}

term_enumeration::iterator::~iterator() {
    dealloc(m_imp);
}

expr* term_enumeration::iterator::operator*() {
    return m_imp ? m_imp->m_current.get() : nullptr;
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

bool term_enumeration::iterator::operator==(iterator const& other) const {
    if (!m_imp && !other.m_imp) return true;
    if (!m_imp) return other.m_imp->m_end;
    if (!other.m_imp) return m_imp->m_end;
    return m_imp->m_end == other.m_imp->m_end &&
           m_imp->m_current == other.m_imp->m_current;
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

std::ostream& term_enumeration::display(std::ostream& out) const {
    return m_imp->display(out);
}
