/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_quantifier_stat.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-20.

Revision History:

--*/
#ifndef SMT_QUANTIFIER_STAT_H_
#define SMT_QUANTIFIER_STAT_H_

#include "ast/ast.h"
#include "util/obj_hashtable.h"
#include "util/approx_nat.h"
#include "util/region.h"

namespace smt {
    
    /**
       \brief Store statistics for quantifiers. This information is
       used to implement heuristics for quantifier instantiation.
    */
    class quantifier_stat {
        unsigned m_size;
        unsigned m_depth;
        unsigned m_generation;
        unsigned m_case_split_factor; //!< the product of the size of the clauses created by this quantifier.
        unsigned m_num_nested_quantifiers;
        unsigned m_num_instances;
        unsigned m_num_instances_curr_search;
        unsigned m_num_instances_curr_branch; //!< only updated if QI_TRACK_INSTANCES is true
        unsigned m_max_generation; //!< max. generation of an instance
        float    m_max_cost;

        friend class quantifier_stat_gen;

        quantifier_stat(unsigned generation);
    public:

        unsigned get_size() const { 
            return m_size; 
        }
        
        unsigned get_depth() const { 
            return m_depth; 
        }
        
        unsigned get_generation() const {
            return m_generation; 
        }
        
        unsigned get_case_split_factor() const {
            return m_case_split_factor;
        }

        unsigned get_num_nested_quantifiers() const {
            return m_num_nested_quantifiers;
        }

        unsigned get_num_instances() const {
            return m_num_instances;
        }

        unsigned get_num_instances_curr_search() const {
            return m_num_instances_curr_search;
        }

        unsigned & get_num_instances_curr_branch() {
            return m_num_instances_curr_branch;
        }
        
        void inc_num_instances() {
            m_num_instances++;
            m_num_instances_curr_search++;
        }

        void inc_num_instances_curr_branch() {
            m_num_instances_curr_branch++;
        }

        void reset_num_instances_curr_search() {
            m_num_instances_curr_search = 0;
        }

        void update_max_generation(unsigned g) {
            if (m_max_generation < g)
                m_max_generation = g;
        }

        unsigned get_max_generation() const {
            return m_max_generation;
        }

        void update_max_cost(float c) {
            if (m_max_cost < c)
                m_max_cost = c;
        }

        float get_max_cost() const {
            return m_max_cost;
        }
    };

    /**
       \brief Functor used to generate quantifier statistics.
    */
    class quantifier_stat_gen {
        struct entry {
            expr *    m_expr;
            unsigned  m_depth:31;
            bool      m_depth_only:1; //!< track only the depth of this entry.
            entry():m_expr(nullptr), m_depth(0), m_depth_only(false) {}
            entry(expr * n, unsigned depth = 0, bool depth_only = false):m_expr(n), m_depth(depth), m_depth_only(depth_only) {}
        };
        ast_manager &           m_manager;
        region &                m_region;
        obj_map<expr, unsigned> m_already_found; // expression to the max. depth it was reached.
        svector<entry>          m_todo;
        approx_nat              m_case_split_factor;
        void reset();
        
    public:
        quantifier_stat_gen(ast_manager & m, region & r);
        quantifier_stat * operator()(quantifier * q, unsigned generation);
    };

};

#endif /* SMT_QUANTIFIER_STAT_H_ */

