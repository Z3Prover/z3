/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_npn3_finder.h

  Abstract:

    extracts clauses for 3-input Boolean functions

  Author:

    Mathias Soeken 2020-02-20

  Notes:

    NPN3 finder
  --*/

#pragma once

#include "util/params.h"
#include "util/scoped_ptr_vector.h"
#include "util/statistics.h"
#include "sat/sat_clause.h"
#include "sat/sat_types.h"
#include "sat/sat_big.h"

namespace sat {

    class solver;

    class npn3_finder {
        solver& s;
        big                     m_big;

        typedef std::function<void(literal, literal, literal, literal)> on_function_t;
        on_function_t m_on_mux;
        on_function_t m_on_maj;
        on_function_t m_on_orand;
        on_function_t m_on_and;
        on_function_t m_on_xor;
        on_function_t m_on_andxor;
        on_function_t m_on_xorand;
        on_function_t m_on_gamble;
        on_function_t m_on_onehot;
        on_function_t m_on_dot;

        typedef svector<std::pair<literal, clause*>> use_list_t;
        scoped_ptr_vector<use_list_t> m_use_lists;

        struct binary {
            literal x, y;
            use_list_t* use_list;
            binary(literal _x, literal _y, use_list_t* u);
            binary();
            struct hash {
                unsigned operator()(binary const& t) const;
            };
            struct eq {
                bool operator()(binary const& a, binary const& b) const;
            };
        };

        struct ternary {
            literal x, y, z;
            clause* orig;
            ternary(literal _x, literal _y, literal _z, clause* c);
            ternary();
            struct hash {
                unsigned operator()(ternary const& t) const;
            };
            struct eq {
                bool operator()(ternary const& a, ternary const& b) const;
            };
        };

        struct quaternary {
            literal w, x, y, z;
            clause* orig;
            quaternary(literal _w, literal _x, literal _y, literal _z, clause* c);
            quaternary();
            struct hash {
                unsigned operator()(quaternary const& q) const;
            };
            struct eq {
                bool operator()(quaternary const& a, quaternary const& b) const;
            };
        };

        typedef hashtable<binary, binary::hash, binary::eq> binary_hash_table_t;
        typedef hashtable<ternary, ternary::hash, ternary::eq> ternary_hash_table_t;
        typedef hashtable<quaternary, quaternary::hash, quaternary::eq> quaternary_hash_table_t;

        void process_clauses(clause_vector& clauses, binary_hash_table_t& binaries, ternary_hash_table_t& ternaries);
        void process_more_clauses(clause_vector& clauses, binary_hash_table_t& binaries, ternary_hash_table_t& ternaries, quaternary_hash_table_t& quaternaries);
        bool has_ternary(ternary_hash_table_t const& ternaries, literal x, literal y, literal z, clause*& c) const;
        bool has_quaternary(quaternary_hash_table_t const& quaternaries, ternary_hash_table_t const& ternaries, literal w, literal x, literal y, literal z, clause*& c) const;

        bool implies(literal a, literal b) const;
        void filter(clause_vector& clauses) const;
        void find_npn3(clause_vector& clauses, on_function_t const& on_function, std::function<bool(binary_hash_table_t const&, ternary_hash_table_t const&, literal, literal, literal, clause&)> const& checker);
        void find_mux(clause_vector& clauses);
        void find_maj(clause_vector& clauses);
        void find_orand(clause_vector& clauses);
        void find_and(clause_vector& clauses);
        void find_xor(clause_vector& clauses);
        void find_andxor(clause_vector& clauses);
        void find_xorand(clause_vector& clauses);
        void find_gamble(clause_vector& clauses);
        void find_onehot(clause_vector& clauses);
        void find_dot(clause_vector& clauses);


    public:
        npn3_finder(solver& s);
        ~npn3_finder() {}
        void set_on_mux(std::function<void(literal head, literal cond, literal th, literal el)> const& f) { m_on_mux = f; }
        void set_on_maj(std::function<void(literal head, literal a, literal b, literal c)> const& f) { m_on_maj = f; }
        void set_on_orand(std::function<void(literal head, literal a, literal b, literal c)> const& f) { m_on_orand = f; }
        void set_on_and(std::function<void(literal head, literal a, literal b, literal c)> const& f) { m_on_and = f; }
        void set_on_xor(std::function<void(literal head, literal a, literal b, literal c)> const& f) { m_on_xor = f; }
        void set_on_andxor(std::function<void(literal head, literal a, literal b, literal c)> const& f) { m_on_andxor = f; }
        void set_on_xorand(std::function<void(literal head, literal a, literal b, literal c)> const& f) { m_on_xorand = f; }
        void set_on_gamble(std::function<void(literal head, literal a, literal b, literal c)> const& f) { m_on_gamble = f; }
        void set_on_onehot(std::function<void(literal head, literal a, literal b, literal c)> const& f) { m_on_onehot = f; }
        void set_on_dot(std::function<void(literal head, literal a, literal b, literal c)> const& f) { m_on_dot = f; }
        void operator()(clause_vector& clauses);
    };
}
