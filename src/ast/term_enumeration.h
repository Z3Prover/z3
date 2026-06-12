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

    // cost function associated with expressions.
    // terms are enumerated with increasing cost.

    void set_cost(std::function<unsigned(expr*)> const& cost);

    class iterator {
        struct iter_imp;
        iter_imp* m_imp;
    public:
        iterator(imp& i, sort* s);
        iterator(std::nullptr_t);
        iterator(iterator const& other);
        iterator& operator=(iterator const& other);
        ~iterator();
        expr* operator*();
        iterator operator++(int);
        iterator& operator++();
        bool operator!=(iterator const& other) const;
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
};