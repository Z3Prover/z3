/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    objective_ast.h

Abstract:
    Abstract data-type for compound objectives.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-21

Notes:

--*/
#ifndef __OBJECTIVE_AST_H_
#define __OBJECTIVE_AST_H_

#include"ast.h"

namespace opt {

    enum objective_t {
        MINIMIZE, 
        MAXIMIZE,
        MAXSAT,
        LEX,
        BOX,
        PARETO
    };

    class compound_objective;
    class min_max_objective;
    class maxsat_objective;

    class objective {
        objective_t m_type;
    public:
        objective(objective_t ty):
            m_type(ty)
        {}
        virtual ~objective() {}

        objective_t type() const { return m_type; }

        // constructors;
        static objective* mk_max(expr_ref& e);
        static objective* mk_min(expr_ref& e);
        static objective* mk_maxsat(symbol id);

        static objective* mk_lex(unsigned sz, objective * const* children);
        static objective* mk_box(unsigned sz, objective * const* children);
        static objective* mk_pareto(unsigned sz, objective * const* children);

        // accessors (implicit cast operations)
        compound_objective& get_compound();
        min_max_objective& get_min_max();
        maxsat_objective& get_maxsat();
    };

    class compound_objective : public objective {
        ptr_vector<objective> m_children;
    public:
        compound_objective(objective_t t, unsigned sz, objective * const* children): 
            objective(t), 
            m_children(sz, children) {}

        virtual ~compound_objective() { 
            ptr_vector<objective>::iterator it = m_children.begin(), end = m_children.end();
            for (; it != end; ++it) {
                dealloc(*it);
            }
        }

        objective *const* children() const { return m_children.c_ptr(); }

        unsigned num_children() const { return m_children.size(); }
    };

    class min_max_objective : public objective {
        bool     m_is_max;
        expr_ref m_expr;
    public:
        min_max_objective(bool is_max, expr_ref& e): 
            objective(is_max ? MAXIMIZE : MINIMIZE), 
            m_is_max(is_max), 
            m_expr(e) {}

        virtual ~min_max_objective() {}

        expr* term() { return m_expr; }
        bool  is_max() const { return m_is_max; }
    };

    class maxsat_objective : public objective {
        symbol m_id;
    public:
        maxsat_objective(symbol const& id): objective(MAXSAT), m_id(id) {}
        virtual ~maxsat_objective() {}
        
        symbol const& get_id() const { return m_id; }
    };
    
};

#endif
