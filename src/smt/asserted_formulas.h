/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    asserted_formulas.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-11.

Revision History:

--*/
#ifndef ASSERTED_FORMULAS_H_
#define ASSERTED_FORMULAS_H_

#include "util/statistics.h"
#include "ast/static_features.h"
#include "ast/expr_substitution.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/bit2int.h"
#include "ast/rewriter/maximize_ac_sharing.h"
#include "ast/rewriter/distribute_forall.h"
#include "ast/rewriter/push_app_ite.h"
#include "ast/rewriter/inj_axiom.h"
#include "ast/rewriter/bv_elim.h"
#include "ast/rewriter/der.h"
#include "ast/rewriter/elim_bounds.h"
#include "ast/macros/macro_manager.h"
#include "ast/macros/macro_finder.h"
#include "ast/normal_forms/defined_names.h"
#include "ast/normal_forms/pull_quant.h"
#include "ast/pattern/pattern_inference.h"
#include "smt/params/smt_params.h"
#include "smt/elim_term_ite.h"


class asserted_formulas {
    
    ast_manager &               m;
    smt_params &                m_smt_params;
    params_ref                  m_params;
    th_rewriter                 m_rewriter;
    expr_substitution           m_substitution;
    scoped_expr_substitution    m_scoped_substitution;
    defined_names               m_defined_names;
    static_features             m_static_features;
    vector<justified_expr>      m_formulas;
    unsigned                    m_qhead;
    bool                        m_elim_and;
    macro_manager               m_macro_manager;
    scoped_ptr<macro_finder>    m_macro_finder;  
    maximize_bv_sharing_rw      m_bv_sharing;
    bool                        m_inconsistent;
    bool                        m_has_quantifiers;
    struct scope {
        unsigned                m_formulas_lim;
        bool                    m_inconsistent_old;
    };
    svector<scope>              m_scopes;
    obj_map<expr, unsigned>     m_expr2depth;

    class simplify_fmls {
    protected:
        asserted_formulas& af;
        ast_manager&           m;
        char const*            m_id;
    public:
        simplify_fmls(asserted_formulas& af, char const* id): af(af), m(af.m), m_id(id) {}
        char const* id() const { return m_id; }
        virtual void simplify(justified_expr const& j, expr_ref& n, proof_ref& p) = 0;
        virtual bool should_apply() const { return true;}
        virtual void post_op() {}
        virtual void operator()();
    };

    class reduce_asserted_formulas_fn : public simplify_fmls {
    public:
        reduce_asserted_formulas_fn(asserted_formulas& af): simplify_fmls(af, "reduce-asserted") {}
        void simplify(justified_expr const& j, expr_ref& n, proof_ref& p) override { af.m_rewriter(j.get_fml(), n, p); }
    };

    class find_macros_fn : public simplify_fmls {
    public:
        find_macros_fn(asserted_formulas& af): simplify_fmls(af, "find-macros") {}
        void operator()() override { af.find_macros_core(); }
        bool should_apply() const override { return af.m_smt_params.m_macro_finder && af.has_quantifiers(); }
        void simplify(justified_expr const& j, expr_ref& n, proof_ref& p) override { UNREACHABLE(); }
    };

    class apply_quasi_macros_fn : public simplify_fmls {
    public:
        apply_quasi_macros_fn(asserted_formulas& af): simplify_fmls(af, "find-quasi-macros") {}
        void operator()() override { af.apply_quasi_macros(); }
        bool should_apply() const override { return af.m_smt_params.m_quasi_macros && af.has_quantifiers(); }
        void simplify(justified_expr const& j, expr_ref& n, proof_ref& p) override { UNREACHABLE(); }
    };

    class nnf_cnf_fn : public simplify_fmls {
    public:
        nnf_cnf_fn(asserted_formulas& af): simplify_fmls(af, "nnf-cnf") {}
        void operator()() override { af.nnf_cnf(); }
        bool should_apply() const override { return af.m_smt_params.m_nnf_cnf || (af.m_smt_params.m_mbqi && af.has_quantifiers()); }
        void simplify(justified_expr const& j, expr_ref& n, proof_ref& p) override { UNREACHABLE(); }
    };

    class propagate_values_fn : public simplify_fmls {
    public:
        propagate_values_fn(asserted_formulas& af): simplify_fmls(af, "propagate-values") {}
        void operator()() override { af.propagate_values(); }
        bool should_apply() const override { return af.m_smt_params.m_propagate_values; }
        void simplify(justified_expr const& j, expr_ref& n, proof_ref& p) override { UNREACHABLE(); }
    };

    class distribute_forall_fn : public simplify_fmls {
        distribute_forall m_functor;
    public:
        distribute_forall_fn(asserted_formulas& af): simplify_fmls(af, "distribute-forall"), m_functor(af.m) {}
        void simplify(justified_expr const& j, expr_ref& n, proof_ref& p) override { m_functor(j.get_fml(), n); }
        bool should_apply() const override { return af.m_smt_params.m_distribute_forall && af.has_quantifiers(); }
        void post_op() override { af.reduce_and_solve();  TRACE("asserted_formulas", af.display(tout);); }
    };

    class pattern_inference_fn : public simplify_fmls {
        pattern_inference_rw m_infer;
    public:
        pattern_inference_fn(asserted_formulas& af): simplify_fmls(af, "pattern-inference"), m_infer(af.m, af.m_smt_params) {}
        void simplify(justified_expr const& j, expr_ref& n, proof_ref& p) override { m_infer(j.get_fml(), n, p); }
        bool should_apply() const override { return af.m_smt_params.m_ematching && af.has_quantifiers(); }
    };

    class refine_inj_axiom_fn : public simplify_fmls {
    public:
        refine_inj_axiom_fn(asserted_formulas& af): simplify_fmls(af, "refine-injectivity") {}
        void simplify(justified_expr const& j, expr_ref& n, proof_ref& p) override;
        bool should_apply() const override { return af.m_smt_params.m_refine_inj_axiom && af.has_quantifiers(); }
    };

    class max_bv_sharing_fn : public simplify_fmls {
    public:
        max_bv_sharing_fn(asserted_formulas& af): simplify_fmls(af, "maximizing-bv-sharing") {}
        void simplify(justified_expr const& j, expr_ref& n, proof_ref& p) override { af.m_bv_sharing(j.get_fml(), n, p); }
        bool should_apply() const override { return af.m_smt_params.m_max_bv_sharing; }
        void post_op() override { af.m_reduce_asserted_formulas(); }
    };

    class elim_term_ite_fn : public simplify_fmls {
        elim_term_ite_rw m_elim;
    public:
        elim_term_ite_fn(asserted_formulas& af): simplify_fmls(af, "elim-term-ite"), m_elim(af.m, af.m_defined_names) {}
        void simplify(justified_expr const& j, expr_ref& n, proof_ref& p) override { m_elim(j.get_fml(), n, p); }
        bool should_apply() const override { return af.m_smt_params.m_eliminate_term_ite && af.m_smt_params.m_lift_ite != LI_FULL; }
        void post_op() override { af.m_formulas.append(m_elim.new_defs()); af.reduce_and_solve(); m_elim.reset(); }
    };

#define MK_SIMPLIFIERA(NAME, FUNCTOR, MSG, APP, ARG, REDUCE)            \
    class NAME : public simplify_fmls {                                 \
        FUNCTOR m_functor;                                              \
    public:                                                             \
        NAME(asserted_formulas& af):simplify_fmls(af, MSG), m_functor ARG {} \
        virtual void simplify(justified_expr const& j, expr_ref& n, proof_ref& p) { \
            m_functor(j.get_fml(), n, p);                               \
        }                                                               \
        virtual void post_op() { if (REDUCE) af.reduce_and_solve(); }   \
        virtual bool should_apply() const { return APP; }               \
    };                                                                  \

#define MK_SIMPLIFIERF(NAME, FUNCTOR, MSG, APP, REDUCE) MK_SIMPLIFIERA(NAME, FUNCTOR, MSG, APP, (af.m), REDUCE)

    MK_SIMPLIFIERF(pull_nested_quantifiers, pull_nested_quant, "pull-nested-quantifiers", af.m_smt_params.m_pull_nested_quantifiers && af.has_quantifiers(), false);
    MK_SIMPLIFIERF(cheap_quant_fourier_motzkin, elim_bounds_rw, "cheap-fourier-motzkin", af.m_smt_params.m_eliminate_bounds && af.has_quantifiers(), true);
    MK_SIMPLIFIERF(elim_bvs_from_quantifiers, bv_elim_rw, "eliminate-bit-vectors-from-quantifiers", af.m_smt_params.m_bb_quantifiers, true);
    MK_SIMPLIFIERF(apply_bit2int, bit2int, "propagate-bit-vector-over-integers", af.m_smt_params.m_simplify_bit2int, true);
    MK_SIMPLIFIERA(lift_ite, push_app_ite_rw, "lift-ite", af.m_smt_params.m_lift_ite != LI_NONE, (af.m, af.m_smt_params.m_lift_ite == LI_CONSERVATIVE), true);
    MK_SIMPLIFIERA(ng_lift_ite, ng_push_app_ite_rw, "lift-ite", af.m_smt_params.m_ng_lift_ite != LI_NONE, (af.m, af.m_smt_params.m_ng_lift_ite == LI_CONSERVATIVE), true);


    reduce_asserted_formulas_fn m_reduce_asserted_formulas;
    distribute_forall_fn        m_distribute_forall;
    pattern_inference_fn        m_pattern_inference;
    refine_inj_axiom_fn         m_refine_inj_axiom;
    max_bv_sharing_fn           m_max_bv_sharing_fn;
    elim_term_ite_fn            m_elim_term_ite;
    pull_nested_quantifiers     m_pull_nested_quantifiers;
    elim_bvs_from_quantifiers   m_elim_bvs_from_quantifiers;
    cheap_quant_fourier_motzkin m_cheap_quant_fourier_motzkin;
    apply_bit2int               m_apply_bit2int;
    lift_ite                    m_lift_ite;
    ng_lift_ite                 m_ng_lift_ite;
    find_macros_fn              m_find_macros;
    propagate_values_fn         m_propagate_values;
    nnf_cnf_fn                  m_nnf_cnf;
    apply_quasi_macros_fn       m_apply_quasi_macros;

    bool invoke(simplify_fmls& s);
    void swap_asserted_formulas(vector<justified_expr>& new_fmls);
    void push_assertion(expr * e, proof * pr, vector<justified_expr>& result);
    bool canceled() { return m.canceled(); }
    bool check_well_sorted() const;
    unsigned get_total_size() const;

    void find_macros_core();
    void expand_macros();
    void apply_quasi_macros();
    void nnf_cnf();
    void reduce_and_solve();
    void flush_cache() { m_rewriter.reset(); m_rewriter.set_substitution(&m_substitution); }
    void set_eliminate_and(bool flag);
    void propagate_values();
    unsigned propagate_values(unsigned i);
    bool update_substitution(expr* n, proof* p);
    bool is_gt(expr* lhs, expr* rhs);
    void compute_depth(expr* e);
    unsigned depth(expr* e) { return m_expr2depth[e]; }

    void init(unsigned num_formulas, expr * const * formulas, proof * const * prs);

public:
    asserted_formulas(ast_manager & m, smt_params & smtp, params_ref const& p);
    ~asserted_formulas();

    void updt_params(params_ref const& p);
    bool has_quantifiers() const { return m_has_quantifiers; }
    void setup();
    void assert_expr(expr * e, proof * in_pr);
    void assert_expr(expr * e);
    void reset();
    void push_scope();
    void pop_scope(unsigned num_scopes);
    bool inconsistent() const { return m_inconsistent; }
    proof * get_inconsistency_proof() const;
    void reduce();
    unsigned get_num_formulas() const { return m_formulas.size(); }
    unsigned get_formulas_last_level() const;
    unsigned get_qhead() const { return m_qhead; }
    void commit(); 
    void commit(unsigned new_qhead); 
    expr *  get_formula(unsigned idx) const { return m_formulas[idx].get_fml(); }
    proof * get_formula_proof(unsigned idx) const { return m_formulas[idx].get_proof(); }
    
    th_rewriter & get_rewriter() { return m_rewriter; }
    void get_assertions(ptr_vector<expr> & result) const;
    bool empty() const { return m_formulas.empty(); }
    void display(std::ostream & out) const;
    void display_ll(std::ostream & out, ast_mark & pp_visited) const;
    void collect_statistics(statistics & st) const;
    
    // -----------------------------------
    //
    // Macros
    //
    // -----------------------------------
    unsigned get_num_macros() const { return m_macro_manager.get_num_macros(); }
    unsigned get_first_macro_last_level() const { return m_macro_manager.get_first_macro_last_level(); }
    func_decl * get_macro_func_decl(unsigned i) const { return m_macro_manager.get_macro_func_decl(i); }
    func_decl * get_macro_interpretation(unsigned i, expr_ref & interp) const { return m_macro_manager.get_macro_interpretation(i, interp); }
    quantifier * get_macro_quantifier(func_decl * f) const { return m_macro_manager.get_macro_quantifier(f); }
    // auxiliary function used to create a logic context based on a model.
    void insert_macro(func_decl * f, quantifier * m, proof * pr) { m_macro_manager.insert(f, m, pr); }
    void insert_macro(func_decl * f, quantifier * m, proof * pr, expr_dependency* dep) { m_macro_manager.insert(f, m, pr, dep); }

};

#endif /* ASSERTED_FORMULAS_H_ */

