/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    euf_completion.h

Abstract:

    Completion for (conditional) equalities.
    This transforms expressions into a normal form by perorming equality saturation modulo 
    ground equations and E-matching on quantified axioms.
    It supports conditional equations in terms of implications.

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-30

--*/

#pragma once

#include "util/scoped_vector.h"
#include "util/dlist.h"
#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_mam.h"
#include "ast/rewriter/th_rewriter.h"
// include "ast/pattern/pattern_inference.h"
#include "params/smt_params.h"

namespace euf {

    class side_condition_solver {
    public:
        struct solution {
            expr* var;
            expr_ref term;
            expr_ref guard;
        };
        virtual ~side_condition_solver() = default;
        virtual void add_constraint(expr* f, proof*, expr_dependency* d) = 0;
        virtual bool is_true(expr* f, proof_ref& pr, expr_dependency*& d) = 0;
        virtual void push() = 0;
        virtual void pop(unsigned n) = 0;
        virtual void solve_for(vector<solution>& sol) = 0;
    };

    struct binding : public dll_base<binding> {
        quantifier*        m_q;
        app*               m_pattern;
        unsigned           m_max_generation;
        unsigned           m_min_top_generation;
        unsigned           m_max_top_generation;
        euf::enode*        m_nodes[0];

        binding(quantifier* q, app* pat, unsigned max_generation, unsigned min_top, unsigned max_top) :
            m_q(q),
            m_pattern(pat),
            m_max_generation(max_generation),
            m_min_top_generation(min_top),
            m_max_top_generation(max_top) {
        }

        euf::enode* const* nodes() { return m_nodes; }

        euf::enode* operator[](unsigned i) const { return m_nodes[i]; }

        unsigned size() const { return m_q->get_num_decls(); }

        quantifier* q() const { return m_q; }

        bool eq(binding const& other) const {
            if (q() != other.q())
                return false;
            for (unsigned i = size(); i-- > 0; )
                if ((*this)[i] != other[i])
                    return false;
            return true;
        }
    };

    struct binding_khasher {
        unsigned operator()(binding const* f) const { return f->q()->get_id(); }
    };

    struct binding_chasher {
        unsigned operator()(binding const* f, unsigned idx) const { return f->m_nodes[idx]->hash(); }
    };

    struct binding_hash_proc {
        unsigned operator()(binding const* f) const {
            return get_composite_hash<binding*, binding_khasher, binding_chasher>(const_cast<binding*>(f), f->size());
        }
    };

    struct binding_eq_proc {
        bool operator()(binding const* a, binding const* b) const { return a->eq(*b); }
    };

    typedef ptr_hashtable<binding, binding_hash_proc, binding_eq_proc> bindings;

    class completion : public dependent_expr_simplifier, public on_binding_callback, public mam_solver {

        struct stats {
            unsigned m_num_rewrites = 0;
            unsigned m_num_instances = 0;
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        struct conditional_rule {
            euf::enode_vector m_body;
            expr_ref m_head;
            expr_ref_vector m_proofs;
            expr_dependency* m_dep;
            unsigned m_watch_index = 0;
            bool m_active = true;
            bool m_in_queue = false;
            conditional_rule(euf::enode_vector& b, expr_ref& h, expr_ref_vector& prs, expr_dependency* d) :
                m_body(b), m_head(h), m_proofs(prs), m_dep(d) {}
        };

        smt_params             m_smt_params;
        egraph                 m_egraph;
        unsigned               m_th_var = 0;
        scoped_ptr<mam>        m_mam;
        enode*                 m_tt, *m_ff;
        ptr_vector<expr>       m_todo;
        enode_vector           m_args, m_reps, m_nodes_to_canonize;
        expr_ref_vector        m_canonical, m_eargs;
        proof_ref_vector       m_canonical_proofs;
        //        pattern_inference_rw   m_infer_patterns;
        bindings               m_bindings;
        scoped_ptr<binding>    m_tmp_binding;
        unsigned               m_tmp_binding_capacity = 0;
        expr_dependency_ref_vector m_deps;
        obj_map<quantifier, std::pair<proof*, expr_dependency*>> m_q2dep;
        vector<std::pair<proof_ref, expr_dependency*>> m_pr_dep;
        unsigned               m_epoch = 0;
        unsigned_vector        m_epochs;
        th_rewriter            m_rewriter;
        stats                  m_stats;
        scoped_ptr<side_condition_solver> m_side_condition_solver;
        ptr_vector<conditional_rule>    m_rules;
        bool                   m_has_new_eq = false;
        bool                   m_should_propagate = false;
        unsigned               m_max_instantiations = std::numeric_limits<unsigned>::max();
        unsigned               m_generation = 0;
        vector<ptr_vector<conditional_rule>> m_rule_watch;

        size_t* to_ptr(size_t i) const { return reinterpret_cast<size_t*>(i); }
        unsigned from_ptr(size_t* s) const { return (unsigned)reinterpret_cast<size_t>(s); }
        unsigned push_pr_dep(proof* pr, expr_dependency* d);
            
        enode* mk_enode(expr* e);
        bool is_new_eq(expr* a, expr* b);
        void update_has_new_eq(expr* g);
        expr_ref mk_and(expr* a, expr* b);
        void add_egraph();
        void map_canonical();
        void read_egraph();
        expr_ref canonize(expr* f, proof_ref& pr, expr_dependency_ref& dep);
        expr_ref canonize_fml(expr* f, proof_ref& pr, expr_dependency_ref& dep);
        expr* get_canonical(expr* f, proof_ref& pr, expr_dependency_ref& d);
        expr* get_canonical(enode* n);
        proof* get_canonical_proof(enode* n);
        void set_canonical(enode* n, expr* e, proof* pr);
        void add_constraint(expr*f, proof* pr, expr_dependency* d);
        expr_dependency* explain_eq(enode* a, enode* b);
        proof_ref prove_eq(enode* a, enode* b);
        proof_ref prove_conflict();
        expr_dependency* explain_conflict();
        std::pair<proof*, expr_dependency*> get_dependency(quantifier* q) { return m_q2dep.contains(q) ? m_q2dep[q] : std::pair(nullptr, nullptr); }

        binding* tmp_binding(quantifier* q, app* pat, euf::enode* const* _binding);
        binding* alloc_binding(quantifier* q, app* pat, euf::enode* const* _binding, unsigned max_generation, unsigned min_top, unsigned max_top);
        void insert_binding(binding* b);
        void apply_binding(binding& b);
        void flush_binding_queue();
        vector<ptr_vector<binding>> m_queue;

        lbool eval_cond(expr* f, proof_ref& pr, expr_dependency*& d);
        
        bool should_stop();

        void add_rule(expr* f, proof* pr, expr_dependency* d);
        void watch_rule(enode* root, enode* other);
        void insert_watch(enode* n, conditional_rule* r);
        void propagate_rule(conditional_rule& r);
        void propagate_rules();
        void propagate_all_rules();
        void clear_propagation_queue();
        ptr_vector<conditional_rule> m_propagation_queue;
        struct push_watch_rule;

        struct scoped_generation;

        bool is_gt(expr* a, expr* b) const;
    public:
        completion(ast_manager& m, dependent_expr_state& fmls);
        ~completion() override;
        char const* name() const override { return "euf-completion"; }
        void push() override;
        void pop(unsigned n) override;
        void reduce() override;
        void collect_statistics(statistics& st) const override;
        void reset_statistics() override { m_stats.reset(); }
        void updt_params(params_ref const& p) override;
        bool supports_proofs() const override { return true; }

        trail_stack& get_trail() override { return m_trail;}
        region& get_region() override { return m_trail.get_region(); }
        egraph& get_egraph() override { return m_egraph; }
        bool is_relevant(enode* n) const override { return true; }
        bool resource_limits_exceeded() const override { return m_stats.m_num_instances > m_max_instantiations; }
        ast_manager& get_manager() override { return m; }

        void on_binding(quantifier* q, app* pat, enode* const* binding, unsigned mg, unsigned ming, unsigned mx) override;
        void set_solver(side_condition_solver* s) { m_side_condition_solver = s; }
    };
}
