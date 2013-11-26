/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    objective_ast.h

Abstract:
    Abstract data-type for compound objectives.

Author:

    Anh-Dung Phan (t-anphan) 2013-11-26

Notes:

--*/

#include"objective_ast.h"

namespace opt {

    objective* objective::mk_max(expr_ref& e) { return alloc(min_max_objective, MAXIMIZE, e); };
    objective* objective::mk_min(expr_ref& e) { return alloc(min_max_objective, MINIMIZE, e); };
    objective* objective::mk_maxsat(symbol id) { return alloc(maxsat_objective, id); };

    objective* objective::mk_lex(unsigned sz, objective * const* children) { 
        return alloc(compound_objective, LEX, sz, children); 
    };

    objective* objective::mk_box(unsigned sz, objective * const* children) {
        return alloc(compound_objective, BOX, sz, children);  
    };

    objective* objective::mk_pareto(unsigned sz, objective * const* children) {
        return alloc(compound_objective, PARETO, sz, children); 
    };

    compound_objective& objective::get_compound() { 
        SASSERT(m_type == LEX || m_type == BOX || m_type == PARETO); 
        return dynamic_cast<compound_objective&>(*this);
    }

    min_max_objective& objective::get_min_max() {
        SASSERT(m_type == MAXIMIZE || m_type == MINIMIZE); 
        return dynamic_cast<min_max_objective&>(*this);
    }

    maxsat_objective& objective::get_maxsat() {
        SASSERT(m_type == MAXSAT); 
        return dynamic_cast<maxsat_objective&>(*this);
    }

};
