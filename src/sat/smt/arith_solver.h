/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    arith_solver.h

Abstract:

    Theory plugin for arithmetic

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/
#pragma once

#include "ast/ast_trail.h"
#include "sat/smt/sat_th.h"
#include "ast/arith_decl_plugin.h"

namespace euf {
    class solver;
}

namespace arith {

    class solver : public euf::th_euf_solver {
        typedef euf::theory_var theory_var;
        typedef euf::theory_id theory_id;
        typedef sat::literal literal;
        typedef sat::bool_var bool_var;
        typedef sat::literal_vector literal_vector;
        typedef union_find<solver, euf::solver>  array_union_find;


        struct stats {
            void reset() { memset(this, 0, sizeof(*this)); }
            stats() { reset(); }
        };


        arith_util        a;
        stats             m_stats;

        // internalize
        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;
        void ensure_var(euf::enode* n);

        // axioms
        void mk_div_axiom(expr* p, expr* q);
        void solver::mk_to_int_axiom(app* n);
        void mk_is_int_axiom(app* n);

        void pop_core(unsigned n) override;
        
    public:
        solver(euf::solver& ctx, theory_id id);
        ~solver() override;
        bool is_external(bool_var v) override { return false; }
        bool propagate(literal l, sat::ext_constraint_idx idx) override { UNREACHABLE(); return false; }
        void get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector& r, bool probing) override {}
        void asserted(literal l) override;
        sat::check_result check() override;

        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override;
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override;
        void collect_statistics(statistics& st) const override;
        euf::th_solver* clone(sat::solver* s, euf::solver& ctx) override;
        void new_eq_eh(euf::th_eq const& eq) override;
        bool unit_propagate() override;
        void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) override;
        void add_dep(euf::enode* n, top_sort<euf::enode>& dep) override;
        sat::literal internalize(expr* e, bool sign, bool root, bool learned) override;
        void internalize(expr* e, bool redundant) override;
        euf::theory_var mk_var(euf::enode* n) override;
        void apply_sort_cnstr(euf::enode* n, sort* s) override {}
        bool is_shared(theory_var v) const override;
    };
}
