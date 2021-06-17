/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_clause.h

Abstract:

    Literals, clauses, justifications for quantifier instantiation

Author:

    Nikolaj Bjorner (nbjorner) 2021-01-24

--*/
#pragma once

#include "util/dlist.h"
#include "ast/ast.h"
#include "ast/quantifier_stat.h"
#include "ast/euf/euf_enode.h"
#include "sat/smt/euf_solver.h"

namespace q {

    struct lit {
        expr_ref lhs;
        expr_ref rhs;
        bool     sign;
        lit(expr_ref const& lhs, expr_ref const& rhs, bool sign):
            lhs(lhs), rhs(rhs), sign(sign) {}
        std::ostream& display(std::ostream& out) const;
    };

    struct binding : public dll_base<binding> {
        app*               m_pattern;
        unsigned           m_max_generation;
        unsigned           m_min_top_generation;
        unsigned           m_max_top_generation;
        euf::enode*        m_nodes[0];

        binding(app* pat, unsigned max_generation, unsigned min_top, unsigned max_top):
            m_pattern(pat),
            m_max_generation(max_generation),
            m_min_top_generation(min_top),
            m_max_top_generation(max_top) {}

        euf::enode* const* nodes() { return m_nodes; }

        euf::enode* operator[](unsigned i) const { return m_nodes[i]; }

        std::ostream& display(euf::solver& ctx, unsigned num_nodes, std::ostream& out) const;
    };

    struct clause {
        unsigned            m_index;
        vector<lit>         m_lits;
        quantifier_ref      m_q;
        sat::literal        m_literal;
        q::quantifier_stat* m_stat = nullptr;
        binding*            m_bindings = nullptr;

        clause(ast_manager& m, unsigned idx): m_index(idx), m_q(m) {}

        std::ostream& display(euf::solver& ctx, std::ostream& out) const;
        lit const& operator[](unsigned i) const { return m_lits[i]; }
        lit& operator[](unsigned i) { return m_lits[i]; }
        unsigned size() const { return m_lits.size(); }
        unsigned num_decls() const { return m_q->get_num_decls(); }
        unsigned index() const { return m_index; }
        quantifier* q() const { return m_q; }
    };

    struct justification {
        expr*     m_lhs, *m_rhs;
        bool      m_sign;
        clause&   m_clause;
        euf::enode* const* m_binding;
        justification(lit const& l, clause& c, euf::enode* const* b):
            m_lhs(l.lhs), m_rhs(l.rhs), m_sign(l.sign), m_clause(c), m_binding(b) {}
        sat::ext_constraint_idx to_index() const { 
            return sat::constraint_base::mem2base(this); 
        }
        static justification& from_index(size_t idx) {
            return *reinterpret_cast<justification*>(sat::constraint_base::from_index(idx)->mem());
        }
        static size_t get_obj_size() { return sat::constraint_base::obj_size(sizeof(justification)); }
    };

}
