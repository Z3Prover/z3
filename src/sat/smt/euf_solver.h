/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_solver.h

Abstract:

    Solver plugin for EUF

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/
#pragma once

#include "util/scoped_ptr_vector.h"
#include "util/trail.h"
#include "ast/ast_translation.h"
#include "ast/euf/euf_egraph.h"
#include "ast/rewriter/th_rewriter.h"
#include "tactic/model_converter.h"
#include "sat/sat_extension.h"
#include "sat/smt/atom2bool_var.h"
#include "sat/smt/sat_th.h"
#include "sat/smt/sat_dual_solver.h"
#include "sat/smt/euf_ackerman.h"
#include "sat/smt/user_solver.h"
#include "smt/params/smt_params.h"

namespace euf {
    typedef sat::literal literal;
    typedef sat::ext_constraint_idx ext_constraint_idx;
    typedef sat::ext_justification_idx ext_justification_idx;
    typedef sat::literal_vector literal_vector;
    typedef sat::bool_var bool_var;

    class constraint {
    public:
        enum class kind_t { conflict, eq, lit };
    private:
        kind_t m_kind;
    public:
        constraint(kind_t k) : m_kind(k) {}
        kind_t kind() const { return m_kind; }
        static constraint& from_idx(size_t z) {
            return *reinterpret_cast<constraint*>(sat::constraint_base::idx2mem(z));
        }
        size_t to_index() const { return sat::constraint_base::mem2base(this); }
    };

    class solver : public sat::extension, public th_internalizer, public th_decompile {
        typedef top_sort<euf::enode> deps_t;
        friend class ackerman;
        class user_sort;
        // friend class sat::ba_solver;
        struct stats {
            unsigned m_ackerman;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };
        struct scope {
            unsigned m_var_lim;
        };
        typedef trail_stack<solver> euf_trail_stack;


        size_t* to_ptr(sat::literal l) { return TAG(size_t*, reinterpret_cast<size_t*>((size_t)(l.index() << 4)), 1); }
        size_t* to_ptr(size_t jst) { return TAG(size_t*, reinterpret_cast<size_t*>(jst), 2); }
        bool is_literal(size_t* p) const { return GET_TAG(p) == 1; }
        bool is_justification(size_t* p) const { return GET_TAG(p) == 2; }
        sat::literal get_literal(size_t* p) const {
            unsigned idx = static_cast<unsigned>(reinterpret_cast<size_t>(UNTAG(size_t*, p)));
            return sat::to_literal(idx >> 4);
        }
        size_t get_justification(size_t* p) const {
            return reinterpret_cast<size_t>(UNTAG(size_t*, p));
        }

        ast_manager& m;
        sat::sat_internalizer& si;
        smt_params            m_config;
        euf::egraph           m_egraph;
        euf_trail_stack       m_trail;
        stats                 m_stats;
        th_rewriter           m_rewriter;
        func_decl_ref_vector  m_unhandled_functions;
        sat::lookahead*       m_lookahead{ nullptr };
        ast_manager*           m_to_m;
        sat::sat_internalizer* m_to_si;
        scoped_ptr<euf::ackerman>   m_ackerman;
        scoped_ptr<sat::dual_solver> m_dual_solver;
        user::solver*          m_user_propagator{ nullptr };
        th_solver*             m_qsolver { nullptr };

        ptr_vector<expr>                                m_bool_var2expr;
        ptr_vector<size_t>                              m_explain;
        unsigned                                        m_num_scopes{ 0 };
        unsigned_vector                                 m_var_trail;
        svector<scope>                                  m_scopes;
        scoped_ptr_vector<th_solver>                    m_solvers;
        ptr_vector<th_solver>                           m_id2solver;
        std::function<::solver*(void)>                  m_mk_solver;

        constraint* m_conflict{ nullptr };
        constraint* m_eq{ nullptr };
        constraint* m_lit{ nullptr };

        // internalization
        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;

        void add_distinct_axiom(app* e, euf::enode* const* args);
        void add_not_distinct_axiom(app* e, euf::enode* const* args);
        void axiomatize_basic(enode* n);
        bool internalize_root(app* e, bool sign, ptr_vector<enode> const& args);
        euf::enode* mk_true();
        euf::enode* mk_false();

        // replay
        expr_ref_vector      m_reinit_exprs;

        void start_reinit(unsigned num_scopes);
        void finish_reinit();

        // extensions
        th_solver* get_solver(family_id fid, func_decl* f);
        th_solver* sort2solver(sort* s) { return get_solver(s->get_family_id(), nullptr); }
        th_solver* func_decl2solver(func_decl* f) { return get_solver(f->get_family_id(), f); }
        th_solver* quantifier2solver();
        th_solver* expr2solver(expr* e);
        th_solver* bool_var2solver(sat::bool_var v);
        void add_solver(th_solver* th);
        void init_ackerman();

        // model building
        expr_ref_vector m_values;
        obj_map<expr, enode*> m_values2root;
        bool include_func_interp(func_decl* f);
        void register_macros(model& mdl);
        void dependencies2values(deps_t& deps, model_ref& mdl);
        void collect_dependencies(deps_t& deps);
        void values2model(deps_t const& deps, model_ref& mdl);

        // solving
        void propagate_literals();
        void propagate_th_eqs();
        bool is_self_propagated(th_eq const& e);
        void get_antecedents(literal l, constraint& j, literal_vector& r, bool probing);
        void new_diseq(enode* a, enode* b, literal lit);

        // proofs
        void log_antecedents(std::ostream& out, literal l, literal_vector const& r);
        void log_antecedents(literal l, literal_vector const& r);
        void drat_log_decl(func_decl* f);
        obj_hashtable<ast> m_drat_asts;
        bool m_drat_initialized{ false };
        void init_drat();

        // relevancy
        bool_vector m_relevant_expr_ids;
        void ensure_dual_solver();
        bool init_relevancy();


        // invariant
        void check_eqc_bool_assignment() const;
        void check_missing_bool_enode_propagation() const;
        void check_missing_eq_propagation() const;

        // diagnosis
        std::ostream& display_justification_ptr(std::ostream& out, size_t* j) const;

        // constraints
        constraint& mk_constraint(constraint*& c, constraint::kind_t k);
        constraint& conflict_constraint() { return mk_constraint(m_conflict, constraint::kind_t::conflict); }
        constraint& eq_constraint() { return mk_constraint(m_eq, constraint::kind_t::eq); }
        constraint& lit_constraint() { return mk_constraint(m_lit, constraint::kind_t::lit); }

        // user propagator
        void check_for_user_propagator() {
            if (!m_user_propagator)
                throw default_exception("user propagator must be initialized");
        }

    public:
        solver(ast_manager& m, sat::sat_internalizer& si, params_ref const& p = params_ref());

        ~solver() override {
            if (m_conflict) dealloc(sat::constraint_base::mem2base_ptr(m_conflict));
            if (m_eq) dealloc(sat::constraint_base::mem2base_ptr(m_eq));
            if (m_lit) dealloc(sat::constraint_base::mem2base_ptr(m_lit));
            m_trail.reset();
        }

        struct scoped_set_translate {
            solver& s;
            scoped_set_translate(solver& s, ast_manager& m, sat::sat_internalizer& si) :
                s(s) {
                s.m_to_m = &m;
                s.m_to_si = &si;
            }
            ~scoped_set_translate() {
                s.m_to_m = &s.m;
                s.m_to_si = &s.si;
            }
        };

        // accessors
        
        sat::sat_internalizer& get_si() { return si; }
        ast_manager& get_manager() { return m; }
        enode* get_enode(expr* e) const { return m_egraph.find(e); }
        sat::literal expr2literal(expr* e) const { return enode2literal(get_enode(e)); }
        sat::literal enode2literal(enode* n) const { return sat::literal(n->bool_var(), false); }
        lbool value(enode* n) const { return s().value(enode2literal(n)); }
        smt_params const& get_config() const { return m_config; }
        region& get_region() { return m_trail.get_region(); }
        egraph& get_egraph() { return m_egraph; }
        th_solver* fid2solver(family_id fid) const { return m_id2solver.get(fid, nullptr); }

        template <typename C>
        void push(C const& c) { m_trail.push(c); }
        template <typename V>
        void push_vec(ptr_vector<V>& vec, V* val) {
            vec.push_back(val);
            push(push_back_trail<solver, V*, false>(vec));
        }
        template <typename V>
        void push_vec(svector<V>& vec, V val) {
            vec.push_back(val);
            push(push_back_trail<solver, V, false>(vec));
        }
        euf_trail_stack& get_trail_stack() { return m_trail; }

        void updt_params(params_ref const& p);
        void set_lookahead(sat::lookahead* s) override { m_lookahead = s; }
        void init_search() override;
        double get_reward(literal l, ext_constraint_idx idx, sat::literal_occs_fun& occs) const override;
        bool is_extended_binary(ext_justification_idx idx, literal_vector& r) override;
        bool is_external(bool_var v) override;
        bool propagated(literal l, ext_constraint_idx idx) override;
        bool unit_propagate() override;

        void propagate(literal lit, ext_justification_idx idx);
        bool propagate(enode* a, enode* b, ext_justification_idx idx);
        void set_conflict(ext_justification_idx idx);

        void propagate(literal lit, th_propagation* p) { propagate(lit, p->to_index()); }
        bool propagate(enode* a, enode* b, th_propagation* p) { return propagate(a, b, p->to_index()); }
        void set_conflict(th_propagation* p) { set_conflict(p->to_index()); }

        bool set_root(literal l, literal r) override;
        void flush_roots() override;

        void get_antecedents(literal l, ext_justification_idx idx, literal_vector& r, bool probing) override;
        void get_antecedents(literal l, th_propagation& jst, literal_vector& r, bool probing);
        void add_antecedent(enode* a, enode* b);
        void asserted(literal l) override;
        sat::check_result check() override;
        void push() override;
        void pop(unsigned n) override;
        void user_push() override;
        void user_pop(unsigned n) override;
        void pre_simplify() override;
        void simplify() override;
        // have a way to replace l by r in all constraints
        void clauses_modifed() override;
        lbool get_phase(bool_var v) override;
        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, ext_justification_idx idx) const override;
        std::ostream& display_constraint(std::ostream& out, ext_constraint_idx idx) const override;
        euf::egraph::b_pp bpp(enode* n) { return m_egraph.bpp(n); }
        void collect_statistics(statistics& st) const override;
        extension* copy(sat::solver* s) override;
        enode* copy(solver& dst_ctx, enode* src_n);
        void find_mutexes(literal_vector& lits, vector<literal_vector>& mutexes) override;
        void gc() override;
        void pop_reinit() override;
        bool validate() override;
        void init_use_list(sat::ext_use_list& ul) override;
        bool is_blocked(literal l, ext_constraint_idx) override;
        bool check_model(sat::model const& m) const override;
        unsigned max_var(unsigned w) const override;

        bool use_drat() { return s().get_config().m_drat && (init_drat(), true); }
        sat::drat& get_drat() { return s().get_drat(); }

        // decompile
        bool extract_pb(std::function<void(unsigned sz, literal const* c, unsigned k)>& card,
            std::function<void(unsigned sz, literal const* c, unsigned const* coeffs, unsigned k)>& pb) override;

        bool to_formulas(std::function<expr_ref(sat::literal)>& l2e, expr_ref_vector& fmls) override;

        // internalize
        sat::literal internalize(expr* e, bool sign, bool root, bool learned) override;
        void internalize(expr* e, bool learned) override;
        sat::literal mk_literal(expr* e);
        void attach_th_var(enode* n, th_solver* th, theory_var v) { m_egraph.add_th_var(n, v, th->get_id()); }
        void attach_node(euf::enode* n);
        expr_ref mk_eq(expr* e1, expr* e2);
        expr_ref mk_eq(euf::enode* n1, euf::enode* n2) { return mk_eq(n1->get_expr(), n2->get_expr()); }
        euf::enode* mk_enode(expr* e, unsigned n, enode* const* args) { return m_egraph.mk(e, n, args); }
        expr* bool_var2expr(sat::bool_var v) { return m_bool_var2expr.get(v, nullptr); }
        sat::literal attach_lit(sat::literal lit, expr* e);
        void unhandled_function(func_decl* f);
        th_rewriter& get_rewriter() { return m_rewriter; }
        bool is_shared(euf::enode* n) const;
        void drat_log_node(expr* n);

        // relevancy
        bool relevancy_enabled() const { return get_config().m_relevancy_lvl > 0; }
        void add_root(unsigned n, sat::literal const* lits);
        void add_aux(unsigned n, sat::literal const* lits);
        void track_relevancy(sat::bool_var v);
        bool is_relevant(expr* e) const;
        bool is_relevant(enode* n) const;

        // model construction
        void update_model(model_ref& mdl);
        obj_map<expr, enode*> const& values2root();

        // diagnostics
        func_decl_ref_vector const& unhandled_functions() { return m_unhandled_functions; }

        // user propagator
        void user_propagate_init(
            void* ctx,
            ::solver::push_eh_t& push_eh,
            ::solver::pop_eh_t& pop_eh,
            ::solver::fresh_eh_t& fresh_eh);
        bool watches_fixed(enode* n) const;
        void assign_fixed(enode* n, expr* val, unsigned sz, literal const* explain);
        void assign_fixed(enode* n, expr* val, literal_vector const& explain) { assign_fixed(n, val, explain.size(), explain.c_ptr()); }
        void assign_fixed(enode* n, expr* val, literal explain) { assign_fixed(n, val, 1, &explain); }

        void user_propagate_register_final(::solver::final_eh_t& final_eh) {
            check_for_user_propagator();
            m_user_propagator->register_final(final_eh);
        }
        void user_propagate_register_fixed(::solver::fixed_eh_t& fixed_eh) {
            check_for_user_propagator();
            m_user_propagator->register_fixed(fixed_eh);
        }
        void user_propagate_register_eq(::solver::eq_eh_t& eq_eh) {
            check_for_user_propagator();
            m_user_propagator->register_eq(eq_eh);
        }
        void user_propagate_register_diseq(::solver::eq_eh_t& diseq_eh) {
            check_for_user_propagator();
            m_user_propagator->register_diseq(diseq_eh);
        }
        unsigned user_propagate_register(expr* e) {
            check_for_user_propagator();
            return m_user_propagator->add_expr(e);
        }

        // solver factory
        ::solver* mk_solver() { return m_mk_solver(); }
        void set_mk_solver(std::function<::solver*(void)>& mk) { m_mk_solver = mk; }


    };
};

inline std::ostream& operator<<(std::ostream& out, euf::solver const& s) {
    return s.display(out);
}
