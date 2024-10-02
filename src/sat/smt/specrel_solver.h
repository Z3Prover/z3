/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    specrel_solver.h

Abstract:

    Theory plugin for special relations

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/
#pragma once

#include "sat/smt/sat_th.h"
#include "ast/special_relations_decl_plugin.h"

namespace euf {
    class solver;
}

namespace specrel {

    class solver : public euf::th_euf_solver {
        typedef euf::theory_var theory_var;
        typedef euf::theory_id theory_id;
        typedef euf::enode enode;
        typedef euf::enode_pair enode_pair;
        typedef euf::enode_pair_vector enode_pair_vector;
        typedef sat::bool_var bool_var;
        typedef sat::literal literal;
        typedef sat::literal_vector literal_vector;

        special_relations_util sp;
        
    public:
        solver(euf::solver& ctx, theory_id id);

        bool is_external(bool_var v) override { return false; }
        void get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector& r, bool probing) override {}
        void asserted(literal l) override;
        sat::check_result check() override;

        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override { return euf::th_explain::from_index(idx).display(out); }
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override { return display_justification(out, idx); }
        void collect_statistics(statistics& st) const override;
        euf::th_solver* clone(euf::solver& ctx) override;
        void new_eq_eh(euf::th_eq const& eq) override;
        bool unit_propagate() override { return false; }
        void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) override;
        bool add_dep(euf::enode* n, top_sort<euf::enode>& dep) override;
        bool include_func_interp(func_decl* f) const override;
        sat::literal internalize(expr* e, bool sign, bool root) override;
        void internalize(expr* e) override;
        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;
        
        euf::theory_var mk_var(euf::enode* n) override;
        void apply_sort_cnstr(euf::enode* n, sort* s) override {}
        bool is_shared(theory_var v) const override { return false; }
        lbool get_phase(bool_var v) override { return l_true; }
        bool enable_self_propagate() const override { return true; }

        void merge_eh(theory_var, theory_var, theory_var v1, theory_var v2);
        void after_merge_eh(theory_var r1, theory_var r2, theory_var v1, theory_var v2) {}
        void unmerge_eh(theory_var v1, theory_var v2) {}
    };
}
