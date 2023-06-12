/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat definitions (define variables as names for terms)

Author:

    Jakob Rath 2023-06-01

--*/
#pragma once
#include "math/polysat/types.h"
#include <optional>

namespace polysat {

    class solver;

    class name_manager final {

        struct name_key {
            // NOTE: this is only optional because table2map requires a default constructor
            std::optional<pdd> term;

            name_key() = default;
            name_key(pdd term): term(std::move(term)) {}

            bool operator==(name_key const& other) const {
                return term == other.term;
            }

            unsigned hash() const {
                return term ? term->hash() : 0;
            }
        };
        using name_hash = obj_hash<name_key>;
        using name_eq = default_eq<name_key>;
        using name_map = map<name_key, pvar, name_hash, name_eq>;

        solver&     s;
        name_map    m_names;    // term -> name
        vector<pdd> m_terms;    // name -> term

        void set_name(pvar v, pdd const& term);

    public:
        name_manager(solver& s): s(s) {}

        void push_var(pdd v);
        void pop_var();

        /** Whether v is a definition for a term */
        bool is_name(pvar v) const { return !m_terms[v].is_var() || m_terms[v].var() != v; }

        /** Return name for term, or null_var if none has been created yet */
        pvar get_name(pdd const& term) const;
        bool has_name(pdd const& term) const { return get_name(term) != null_var; }

        /** Return name for term, creating one if necessary */
        pvar mk_name(pdd const& term);
    };

}
