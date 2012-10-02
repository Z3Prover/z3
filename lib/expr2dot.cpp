/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    expr2dot.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-03-07.

Revision History:

--*/
#include"expr2dot.h"
#include"for_each_expr.h"

class dot_printer {
    std::ostream & m_out;
    ast_manager &  m_manager;
    bool           m_proofs_only;
public:
    dot_printer(std::ostream & out, ast_manager & m, bool proofs):
        m_out(out),
        m_manager(m),
        m_proofs_only(proofs) {
    }

    char const * get_color(app * n) {
        if (m_manager.is_unit_resolution(n)) 
            return "blue";
        else if (m_manager.is_lemma(n))
            return "gold";
        else if (m_manager.is_transitivity(n))
            return "red";
        else if (m_manager.is_monotonicity(n))
            return "green";
        else 
            return "black";
    }

    void operator()(var * n) {
        if (!m_proofs_only) {
            m_out << n->get_id() << "[label=\"\",shape=circle];\n";
        }
    }
    
    void operator()(quantifier * n) {
        if (!m_proofs_only) {
            m_out << n->get_id() << "[label=\"\",shape=circle,color=gray];\n";
            m_out << n->get_expr()->get_id() << " -> " << n->get_id() << ";\n";
        }
    }

    void operator()(app * n) {
        if (!m_proofs_only || m_manager.is_proof(n)) {
            char const * c = get_color(n);
            m_out << n->get_id() << "[label=\"\",shape=circle,color=" << c << "];\n";
            if (m_proofs_only) {
                unsigned num = m_manager.get_num_parents(n);
                for (unsigned i = 0; i < num; i++)
                    m_out << m_manager.get_parent(n, i)->get_id() << " -> " << n->get_id() << " [color=" << c << "];\n";
            }
            else {
                unsigned num = n->get_num_args();
                for (unsigned i = 0; i < num; i++)
                    m_out << n->get_arg(i)->get_id() << " -> " << n->get_id() << " [color=" << c << "];\n";
            }
        }
    }
};

void expr2dot(std::ostream & out, expr * n, ast_manager & m, bool proofs) {
    out << "digraph \"ast\" {\n";
    dot_printer p(out, m, proofs);
    for_each_expr(p, n);
    out << "}\n";
}


