/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    polymorphism_util.h

Abstract:

    Utilities for supporting polymorphic type signatures.

Author:

    Nikolaj Bjorner (nbjorner) 2023-7-8

--*/
#pragma once

#include "ast/ast.h"
#include "util/hashtable.h"

namespace polymorphism {

    class substitution {
        ast_manager& m;
        obj_map<sort, sort*> m_sub;
        sort_ref_vector m_trail;
    public:
        substitution(ast_manager& m): m(m), m_trail(m) {}
    
        sort_ref_vector operator()(sort_ref_vector const& s);
        
        sort_ref operator()(sort* s);

        expr_ref operator()(expr* e);
        
        bool unify(sort* s1, sort* s2);       

        bool match(sort* s1, sort* s_ground);

        obj_map<sort, sort*>::iterator begin() const { return m_sub.begin(); }
        obj_map<sort, sort*>::iterator end() const { return m_sub.end(); }

        void insert(sort* v, sort* t) { m_trail.push_back(v).push_back(t); m_sub.insert(v, t); }

        bool find(sort* v, sort*& t) const { return m_sub.find(v, t); }

        unsigned size() const { return m_sub.size(); }

        /**
        * weak equality: strong equality considers applying substitutions recursively in range
        * because substitutions may be in triangular form.
        */
        struct eq {
            bool operator()(substitution const* s1, substitution const* s2) const {
                if (s1->size() != s2->size())
                    return false;
                sort* v2;
                for (auto const& [k, v] : *s1) {
                    if (!s2->find(k, v2))
                        return false;
                    if (v != v2)
                        return false;
                }
                return true;
            }
        };

        struct hash {
            unsigned operator()(substitution const* s) const {
                unsigned hash = 0xfabc1234 + s->size();
                for (auto const& [k, v] : *s) 
                    hash ^= k->hash() + 2 * v->hash();                
                return hash;
            }
        };
    };

    typedef hashtable<substitution*, substitution::hash, substitution::eq> substitutions;

    /**
     * Polymorphic signature for operators
     */
    struct psig {
        symbol          m_name;
        unsigned        m_num_params;
        sort_ref_vector m_dom;
        sort_ref        m_range;
        psig(ast_manager& m, char const* name, unsigned n, unsigned dsz, sort* const* dom, sort* rng):
            m_name(name),
            m_num_params(n),
            m_dom(m),
            m_range(rng, m)
        {
            m_dom.append(dsz, dom);
        }
    };
    
    class util {
        ast_manager&         m;
        sort_ref_vector      m_trail;
        obj_map<sort, sort*> m_fresh;
        unsigned             m_counter = 0;

        sort_ref fresh(sort* s);

        sort_ref_vector fresh(unsigned n, sort* const* s);
        
    public:
        util(ast_manager& m): m(m), m_trail(m) {}
        
        bool unify(sort* s1, sort* s2, substitution& sub);
        
        bool unify(func_decl* f1, func_decl* f2, substitution& sub);
        
        bool unify(substitution const& s1, substitution const& s2,
                   substitution& sub);

        bool match(substitution& sub, sort* s1, sort* s_ground);

        /**
         * Match a polymorphic signature against concrete argument sorts.
         * Raises exception if arity mismatch or type mismatch.
         * Returns the instantiated range sort via range_out.
         */
        void match(psig& sig, unsigned dsz, sort* const* dom, sort* range, sort_ref& range_out);
                        
        // collect instantiations of polymorphic functions
        void collect_poly_instances(expr* e, ptr_vector<func_decl>& instances);
        
        // test if expression contains polymorphic variable.
        bool has_type_vars(expr* e);

        void collect_type_vars(expr* e, ptr_vector<sort>& tvs);
        
    };
}
