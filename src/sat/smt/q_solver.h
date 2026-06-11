/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_solver.h

Abstract:

    Quantifier solver plugin

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-29

--*/
#pragma once

#include "util/obj_hashtable.h"
#include "ast/ast_trail.h"
#include "ast/rewriter/der.h"
#include "sat/smt/sat_th.h"
#include "sat/smt/q_mbi.h"
#include "sat/smt/q_ematch.h"

namespace euf {
    class solver;
}

namespace q {

    struct q_proof_hint : public euf::th_proof_hint {
        symbol        m_method;
        unsigned      m_generation;
        unsigned      m_num_bindings;
        unsigned      m_num_literals;
        sat::literal* m_literals;
        expr*         m_bindings[0];
        
        q_proof_hint(symbol const& method, unsigned g, unsigned b, unsigned l) {
            m_method = method;
            m_generation = g;
            m_num_bindings = b;
            m_num_literals = l;
            m_literals = reinterpret_cast<sat::literal*>(m_bindings + m_num_bindings);
        }
        static size_t get_obj_size(unsigned num_bindings, unsigned num_lits) { return sizeof(q_proof_hint) + num_bindings*sizeof(expr*) + num_lits*sizeof(sat::literal); }
        static q_proof_hint* mk(euf::solver& s, symbol const& method, unsigned generation, sat::literal_vector const& lits, unsigned n, euf::enode* const* bindings);
        static q_proof_hint* mk(euf::solver& s, symbol const& method, unsigned generation, sat::literal l1, sat::literal l2, unsigned n, expr* const* bindings);
        expr* get_hint(euf::solver& s) const override;
    };

    class solver : public euf::th_euf_solver {

        typedef obj_map<quantifier, quantifier*> flat_table;
        friend class mbqi;

        struct stats {
            unsigned m_num_quantifier_asserts;
            void reset() { memset(this, 0, sizeof(*this)); }
            stats() { reset(); }
        };

        stats                  m_stats;
        mbqi                   m_mbqi;
        ematch                 m_ematch;

        flat_table             m_flat;
        sat::literal_vector    m_universal;
        obj_map<sort, expr*>   m_unit_table;
        expr_ref_vector        m_expanded;
        der_rewriter           m_der;

        sat::literal instantiate(quantifier* q, bool negate, std::function<expr* (quantifier*, unsigned)>& mk_var);
        sat::literal skolemize(quantifier* q);
        sat::literal specialize(quantifier* q);
        void init_units();
        expr* get_unit(sort* s);
        
        bool expand(quantifier* q);
        bool split(expr* arg, expr_ref& e1, expr_ref& e2);
        bool is_literal(expr* arg);

        friend class ematch;

    public:

        solver(euf::solver& ctx, family_id fid);
        bool is_external(sat::bool_var v) override { return false; }
        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing) override;
        void asserted(sat::literal l) override;
        sat::check_result check() override;

        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override { return display_constraint(out, idx); }
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override;
        void collect_statistics(statistics& st) const override;
        euf::th_solver* clone(euf::solver& ctx) override;
        bool unit_propagate() override;
        sat::literal internalize(expr* e, bool sign, bool root) override;
        void internalize(expr* e) override { internalize(e, false, false); }
        euf::theory_var mk_var(euf::enode* n) override;
        void init_search() override;
        void finalize_model(model& mdl) override;
        bool is_shared(euf::theory_var v) const override { return true; }
        void relevant_eh(euf::enode* n) override { m_ematch.relevant_eh(n); }

        ast_manager& get_manager() { return m; }
        sat::literal_vector const& universal() const { return m_universal; }
        quantifier* flatten(quantifier* q);

        void log_instantiation(sat::literal q, sat::literal i, justification* j = nullptr) { sat::literal lits[2] = { q, i }; log_instantiation(2, lits, j); }
        void log_instantiation(sat::literal_vector const& lits, justification* j) { log_instantiation(lits.size(), lits.data(), j); }
        void log_instantiation(unsigned n, sat::literal const* lits, justification* j);

    };
}
