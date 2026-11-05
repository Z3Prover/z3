/*++
Copyright (c) 2026 Romain Soulat

    Finite-field adapter for the SAT/EUF frontend. Algebra and evidence belong
    to ast/ff; congruence, assignments and model arrangements belong here.
--*/
#pragma once
#include "sat/smt/sat_th.h"
#include "ast/ff/ff_solver.h"

namespace ff_sat {
    class solver : public euf::th_euf_solver {
        ff_util ff;
        expr_ref_vector proofs, domains;
        bool split_domain(euf::enode *n);
        ff::basis_cache basis;
        obj_map<sort, std::unique_ptr<ff::ff_encoding_cache>> caches;
        obj_map<expr, rational> values;
        unsigned checks = 0, conflicts = 0, arrangements = 0;
        bool visit(expr *e) override;
        bool visited(expr *e) override;
        bool post_visit(expr *e, bool sign, bool root) override;

    public:
        explicit solver(euf::solver &ctx);
        euf::th_solver *clone(euf::solver &ctx) override {
            return alloc(solver, ctx);
        }
        void asserted(sat::literal) override {}
        bool unit_propagate() override {
            return false;
        }
        bool is_external(sat::bool_var) override {
            return false;
        }
        sat::check_result check() override;
        void get_antecedents(sat::literal, sat::ext_justification_idx, sat::literal_vector &, bool) override {}
        std::ostream &display(std::ostream &out) const override {
            return out;
        }
        std::ostream &display_justification(std::ostream &out, sat::ext_justification_idx) const override {
            return out;
        }
        std::ostream &display_constraint(std::ostream &out, sat::ext_constraint_idx) const override {
            return out;
        }
        void collect_statistics(statistics &st) const override;
        sat::literal internalize(expr *e, bool sign, bool root) override;
        void internalize(expr *e) override;
        void apply_sort_cnstr(euf::enode *n, sort *) override;
        void add_value(euf::enode *n, model &, expr_ref_vector &result) override;
    };
}  // namespace ff_sat
