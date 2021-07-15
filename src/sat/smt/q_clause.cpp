/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_clause.cpp

Abstract:

    Clause and literals

Author:

    Nikolaj Bjorner (nbjorner) 2021-01-24

--*/

#include "sat/smt/q_clause.h"


namespace q {

    std::ostream& lit::display(std::ostream& out) const {
        ast_manager& m = lhs.m();
        if (m.is_true(rhs) && !sign) 
            return out << mk_bounded_pp(lhs, m, 2);
        if (m.is_false(rhs) && !sign) 
            return out << "(not " << mk_bounded_pp(lhs, m, 2) << ")";
        return 
            out << mk_bounded_pp(lhs, m, 2) 
                << (sign ? " != " : " == ") 
                << mk_bounded_pp(rhs, m, 2);
    }

    std::ostream& binding::display(euf::solver& ctx, unsigned num_nodes, std::ostream& out) const {
        for (unsigned i = 0; i < num_nodes; ++i) 
            out << ctx.bpp((*this)[i]) << " ";
        return out;
    }

    std::ostream& clause::display(euf::solver& ctx, std::ostream& out) const {
        out << "clause:\n";
        for (auto const& lit : m_lits)
            lit.display(out) << "\n";
        binding* b = m_bindings;
        if (b) {
            do {
                b->display(ctx, num_decls(), out) << "\n";
                b = b->next();
            }
            while (b != m_bindings);
        }
        return out;
    }


}
