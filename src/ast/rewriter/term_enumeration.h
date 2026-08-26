#pragma once

#include "ast/ast.h"
#include <functional>

class term_enumeration {
    struct imp;
    imp* m_imp;
public:
    term_enumeration(ast_manager& m);
    ~term_enumeration();

    void add_production(func_decl* f);
    void add_production(expr* e);
    // void add_production(sort *s, std::function<expr *()> g);

    // cost function associated with expressions.
    // terms are enumerated with increasing cost.

    void set_cost(std::function<unsigned(expr*)> const& cost);

    // An external enumerator is consulted (at most once per sort) to
    // produce a base value for sorts that are not covered by the grammar
    // (e.g., non-datatype sorts referenced as fields of an algebraic
    // datatype). This allows clients such as the model's datatype value
    // factory to combine bottom-up enumeration of constructor applications
    // with model-provided values for the non-datatype argument sorts.
    using external_enumerator_t = std::function<expr*(sort*)>;
    void set_external_enumerator(external_enumerator_t fn);

    class iterator {
        struct iter_imp;
        iter_imp* m_imp;
    public:
        iterator(imp& i, sort* s);
        iterator(std::nullptr_t);
        iterator(iterator&& other) noexcept;
        iterator& operator=(iterator&& other) noexcept;
        iterator(iterator const&) = delete;
        iterator& operator=(iterator const&) = delete;
        ~iterator();
        expr* operator*();
        iterator& operator++();
        bool operator!=(iterator const& other) const {
            return !(*this == other);
        }
        bool operator==(iterator const &other) const;
    };

    class terms {
        imp* m_imp;
        sort* m_sort;
    public:
        terms(imp* i, sort* s);
        iterator begin();
        iterator end();
    };

    terms enum_terms(sort* s);

    // -- tuple enumeration --
    // Iterate over vectors of terms, one term per input sort. Produces all
    // combinations (dovetailed, since individual streams may be infinite).

    class tuple_iterator {
        struct timp;
        timp* m_imp;
    public:
        tuple_iterator(imp& i, unsigned n, sort* const* sorts);
        tuple_iterator(std::nullptr_t);
        ~tuple_iterator();
        expr_ref_vector operator*();
        tuple_iterator& operator++();
        bool operator!=(tuple_iterator const& other) const {
            return !(*this == other);
        }
        bool operator==(tuple_iterator const& other) const;
    };

    class tuples {
        imp*             m_imp;
        ptr_vector<sort> m_sorts;
    public:
        tuples(imp* i, unsigned n, sort* const* sorts);
        tuple_iterator begin();
        tuple_iterator end();
    };

    tuples enum_tuples(unsigned n, sort* const* sorts);
    tuples enum_tuples(sort_ref_vector const& sorts);

    std::ostream& display(std::ostream& out) const;
};