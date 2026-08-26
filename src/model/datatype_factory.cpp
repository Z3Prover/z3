/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    datatype_factory.cpp

Abstract:

    Value factory for algebraic datatypes, implemented on top of the
    generic bottom-up term_enumeration module. Constructors of the
    datatype sort (and of every datatype sort reachable through
    constructor argument sorts) are registered as grammar productions.
    Values for non-datatype argument sorts (e.g., Int, arrays,
    uninterpreted sorts) are supplied through term_enumeration's external
    enumerator hook, which defers to the underlying model.

Author:

    Leonardo de Moura (leonardo) 2008-11-06.

Revision History:

--*/
#include "model/datatype_factory.h"
#include "model/model_core.h"
#include "ast/ast_pp.h"

datatype_factory::datatype_factory(ast_manager & m, model_core & md):
    struct_factory(m, m.mk_family_id("datatype"), md),
    m_util(m) {
}

datatype_factory::~datatype_factory() {
    for (auto & kv : m_some_enum)
        dealloc(kv.m_value);
    for (auto & kv : m_fresh_iter)
        dealloc(kv.m_value);
    for (auto & kv : m_fresh_enum)
        dealloc(kv.m_value);
}

/**
   \brief Build (or retrieve from \c cache) a term_enumeration that can
   enumerate values of sort \c s. The enumerator's grammar is seeded with
   the constructors of \c s and of every datatype sort transitively
   reachable through constructor argument sorts -- including datatype
   sorts nested under parametric sort constructors such as Array, Seq
   and FiniteSet (e.g. (Array Int MyList), (Seq MyList)). Values for
   argument sorts that are not datatypes are produced on demand by the
   external enumerator, which asks the model for a value.
*/
term_enumeration & datatype_factory::get_enumerator(sort * s, obj_map<sort, term_enumeration *> & cache) {
    term_enumeration * te = nullptr;
    if (cache.find(s, te))
        return *te;

    te = alloc(term_enumeration, m_manager);
    cache.insert(s, te);

    ptr_vector<sort> todo;
    obj_hashtable<sort> visited;
    todo.push_back(s);
    visited.insert(s);
    while (!todo.empty()) {
        sort * cur = todo.back();
        todo.pop_back();
        if (m_util.is_datatype(cur)) {
            for (func_decl * c : *m_util.get_datatype_constructors(cur)) {
                te->add_production(c);
                unsigned num = c->get_arity();
                for (unsigned i = 0; i < num; ++i) {
                    sort * s_arg = c->get_domain(i);
                    if (!visited.contains(s_arg)) {
                        visited.insert(s_arg);
                        todo.push_back(s_arg);
                    }
                }
            }
        }
        // Sorts such as Array, Seq and FiniteSet may nest a datatype sort
        // as one of their sort parameters (e.g., the range of an Array,
        // the element sort of a Seq or FiniteSet). Follow those nested
        // sorts uniformly, via sort::get_sort_parameters(), so that any
        // datatype constructors they contain are also registered.
        for (sort * nested : cur->get_sort_parameters()) {
            if (!visited.contains(nested)) {
                visited.insert(nested);
                todo.push_back(nested);
            }
        }
    }

    te->set_external_enumerator([this](sort * s_arg) -> expr* {
        return m_model.get_some_value(s_arg);
    });

    return *te;
}

expr * datatype_factory::get_some_value(sort * s) {
    if (!m_util.is_datatype(s))
        return m_model.get_some_value(s);
    auto& [set, values] = get_value_set(s);
    if (!set.empty())
        return *(set.begin());
    term_enumeration & te = get_enumerator(s, m_some_enum);
    for (expr * e : te.enum_terms(s)) {
        register_value(e);
        TRACE(datatype, tout << mk_pp(e, m_util.get_manager()) << "\n";);
        return e;
    }
    UNREACHABLE();
    return nullptr;
}

expr * datatype_factory::get_fresh_value(sort * s) {
    if (!m_util.is_datatype(s))
        return m_model.get_fresh_value(s);
    TRACE(datatype, tout << "generating fresh value for: " << s->get_name() << "\n";);

    auto& [set, values] = get_value_set(s);

    if (!m_util.is_recursive(s)) {
        // No structural growth is possible for a non-recursive datatype, so
        // bottom-up term enumeration alone cannot produce arbitrarily many
        // distinct values (e.g., a plain record with an Int field, or an
        // enumeration sort). Instead, try to vary one constructor argument
        // using the model's own fresh values, falling back to constructors
        // that have not been used yet (this covers enumeration sorts, whose
        // nullary constructors have no arguments to vary).
        for (func_decl * c : *m_util.get_datatype_constructors(s)) {
            expr_ref_vector args(m_manager);
            bool found_fresh_arg = false;
            unsigned num = c->get_arity();
            for (unsigned i = 0; i < num; ++i) {
                sort * s_arg = c->get_domain(i);
                if (!found_fresh_arg) {
                    expr * fresh_arg = m_util.is_datatype(s_arg) ? get_fresh_value(s_arg) : m_model.get_fresh_value(s_arg);
                    if (fresh_arg) {
                        found_fresh_arg = true;
                        args.push_back(fresh_arg);
                        continue;
                    }
                }
                args.push_back(m_util.is_datatype(s_arg) ? get_some_value(s_arg) : m_model.get_some_value(s_arg));
            }
            expr * new_value = m_manager.mk_app(c, args);
            if (!set.contains(new_value)) {
                register_value(new_value);
                TRACE(datatype, tout << "result: " << mk_pp(new_value, m_manager) << "\n";);
                return new_value;
            }
        }
        return set.empty() ? get_some_value(s) : nullptr;
    }

    term_enumeration::iterator * it = nullptr;
    if (!m_fresh_iter.find(s, it)) {
        term_enumeration & te = get_enumerator(s, m_fresh_enum);
        it = alloc(term_enumeration::iterator, te.enum_terms(s).begin());
        m_fresh_iter.insert(s, it);
    }

    expr * e = nullptr;
    while ((e = **it) != nullptr) {
        ++(*it);
        if (!set.contains(e)) {
            register_value(e);
            TRACE(datatype, tout << "result: " << mk_pp(e, m_manager) << "\n";);
            return e;
        }
    }
    return nullptr;
}

