/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_context.h

Abstract:

    Logical context

Author:

    Leonardo de Moura (leonardo) 2008-02-18.

Revision History:

--*/
#ifndef SMT_CONTEXT_H_
#define SMT_CONTEXT_H_

#include "smt/smt_clause.h"
#include "smt/smt_setup.h"
#include "smt/smt_enode.h"
#include "smt/smt_cg_table.h"
#include "smt/smt_b_justification.h"
#include "smt/smt_eq_justification.h"
#include "smt/smt_justification.h"
#include "smt/smt_bool_var_data.h"
#include "smt/smt_theory.h"
#include "smt/smt_quantifier.h"
#include "smt/smt_quantifier_stat.h"
#include "smt/smt_statistics.h"
#include "smt/smt_conflict_resolution.h"
#include "smt/smt_relevancy.h"
#include "smt/smt_case_split_queue.h"
#include "smt/smt_almost_cg_table.h"
#include "smt/smt_failure.h"
#include "smt/asserted_formulas.h"
#include "smt/smt_types.h"
#include "smt/dyn_ack.h"
#include "ast/ast_smt_pp.h"
#include "smt/watch_list.h"
#include "util/trail.h"
#include "smt/fingerprints.h"
#include "util/ref.h"
#include "smt/proto_model/proto_model.h"
#include "model/model.h"
#include "util/timer.h"
#include "util/statistics.h"
#include "solver/progress_callback.h"
#include <tuple>

// there is a significant space overhead with allocating 1000+ contexts in
// the case that each context only references a few expressions.
// Using a map instead of a vector for the literals can compress space
// consumption.
#ifdef SPARSE_MAP
#define USE_BOOL_VAR_VECTOR 0
#else
#define USE_BOOL_VAR_VECTOR 1
#endif

namespace smt {

    class model_generator;

    class context {
        friend class model_generator;
    public:
        statistics                  m_stats;

        std::ostream& display_last_failure(std::ostream& out) const;
        std::string last_failure_as_string() const;
        void set_reason_unknown(char const* msg) { m_unknown = msg; }
        void set_progress_callback(progress_callback *callback);


    protected:
        ast_manager &               m_manager;
        smt_params &                m_fparams;
        params_ref                  m_params;
        setup                       m_setup;
        timer                       m_timer;
        asserted_formulas           m_asserted_formulas;
        scoped_ptr<quantifier_manager>   m_qmanager;
        scoped_ptr<model_generator>      m_model_generator;
        scoped_ptr<relevancy_propagator> m_relevancy_propagator;
        random_gen                  m_random;
        bool                        m_flushing; // (debug support) true when flushing
        mutable unsigned            m_lemma_id;
        progress_callback *         m_progress_callback;
        unsigned                    m_next_progress_sample;

        region                      m_region;

        fingerprint_set             m_fingerprints;

        expr_ref_vector             m_b_internalized_stack; // stack of the boolean expressions already internalized.
        // Remark: boolean expressions can also be internalized as
        // enodes. Examples: boolean expression nested in an
        // uninterpreted function.
        expr_ref_vector             m_e_internalized_stack; // stack of the expressions already internalized as enodes.

        ptr_vector<justification>   m_justifications;

        unsigned                    m_final_check_idx; // circular counter used for implementing fairness

        // -----------------------------------
        //
        // Equality & Uninterpreted functions
        //
        // -----------------------------------
        enode *                     m_true_enode;
        enode *                     m_false_enode;
        app2enode_t                 m_app2enode;    // app -> enode
        ptr_vector<enode>           m_enodes;
        plugin_manager<theory>      m_theories;     // mapping from theory_id -> theory
        ptr_vector<theory>          m_theory_set;   // set of theories for fast traversal
        vector<enode_vector>        m_decl2enodes;  // decl -> enode (for decls with arity > 0)
        enode_vector                m_empty_vector;
        cg_table                    m_cg_table;
        dyn_ack_manager             m_dyn_ack_manager;
        struct new_eq {
            enode *                 m_lhs;
            enode *                 m_rhs;
            eq_justification        m_justification;
            new_eq() {}
            new_eq(enode * lhs, enode * rhs, eq_justification const & js):
                m_lhs(lhs), m_rhs(rhs), m_justification(js) {}
        };
        svector<new_eq>             m_eq_propagation_queue;
        struct new_th_eq {
            theory_id  m_th_id;
            theory_var m_lhs;
            theory_var m_rhs;
            new_th_eq():m_th_id(null_theory_id), m_lhs(null_theory_var), m_rhs(null_theory_var) {}
            new_th_eq(theory_id id, theory_var l, theory_var r):m_th_id(id), m_lhs(l), m_rhs(r) {}
        };
        svector<new_th_eq>          m_th_eq_propagation_queue;
        svector<new_th_eq>          m_th_diseq_propagation_queue;
#ifdef Z3DEBUG
        svector<new_th_eq>          m_propagated_th_eqs;
        svector<new_th_eq>          m_propagated_th_diseqs;
        svector<enode_pair>         m_diseq_vector;
#endif
        enode *                     m_is_diseq_tmp; // auxiliary enode used to find congruent equality atoms.

        tmp_enode                   m_tmp_enode;
        ptr_vector<almost_cg_table> m_almost_cg_tables; // temporary field for is_ext_diseq

        // -----------------------------------
        //
        // Boolean engine
        //
        // -----------------------------------
#if USE_BOOL_VAR_VECTOR
        svector<bool_var>           m_expr2bool_var;         // expr id -> bool_var
#else
        u_map<bool_var>             m_expr2bool_var;
#endif
        ptr_vector<expr>            m_bool_var2expr;         // bool_var -> expr
        signed_char_vector          m_assignment;  //!< mapping literal id -> assignment lbool
        vector<watch_list>          m_watches;     //!< per literal
        vector<clause_set>          m_lit_occs;    //!< index for backward subsumption
        svector<bool_var_data>      m_bdata;       //!< mapping bool_var -> data
        svector<double>             m_activity;
        clause_vector               m_aux_clauses;
        clause_vector               m_lemmas;
        vector<clause_vector>       m_clauses_to_reinit;
        expr_ref_vector             m_units_to_reassert;
        svector<char>               m_units_to_reassert_sign;
        literal_vector              m_assigned_literals;
        typedef std::pair<clause*, literal_vector> tmp_clause;
        vector<tmp_clause>          m_tmp_clauses;
        unsigned                    m_qhead;
        unsigned                    m_simp_qhead;
        int                         m_simp_counter; //!< can become negative
        scoped_ptr<case_split_queue> m_case_split_queue;
        double                      m_bvar_inc;
        bool                        m_phase_cache_on;
        unsigned                    m_phase_counter; //!< auxiliary variable used to decide when to turn on/off phase caching
        bool                        m_phase_default; //!< default phase when using phase caching

        // A conflict is usually a single justification. That is, a justification
        // for false. If m_not_l is not null_literal, then m_conflict is a
        // justification for l, and the conflict is union of m_no_l and m_conflict;
        b_justification             m_conflict;
        literal                     m_not_l;
        scoped_ptr<conflict_resolution> m_conflict_resolution;
        proof_ref                   m_unsat_proof;


        literal_vector              m_atom_propagation_queue;

        obj_map<expr, unsigned>      m_cached_generation;
        obj_hashtable<expr>          m_cache_generation_visited;

        // -----------------------------------
        //
        // Model generation
        //
        // -----------------------------------
        proto_model_ref            m_proto_model;
        model_ref                  m_model;
        std::string                m_unknown;
        void                       mk_proto_model(lbool r);
        struct scoped_mk_model {
            context & m_ctx;
            scoped_mk_model(context & ctx):m_ctx(ctx) {
                m_ctx.m_proto_model = nullptr;
                m_ctx.m_model       = nullptr;
            }
            ~scoped_mk_model() {
                if (m_ctx.m_proto_model.get() != nullptr) {
                    m_ctx.m_model = m_ctx.m_proto_model->mk_model();
                    try {
                        m_ctx.add_rec_funs_to_model();
                    }
                    catch (...) {
                        // no op
                    }
                    m_ctx.m_proto_model = nullptr; // proto_model is not needed anymore.
                }
            }
        };


        // -----------------------------------
        //
        // Unsat core extraction
        //
        // -----------------------------------
        typedef u_map<expr *>      literal2assumption;
        literal_vector             m_assumptions;
        literal2assumption         m_literal2assumption; // maps an expression associated with a literal to the original assumption
        expr_ref_vector            m_unsat_core;

        // -----------------------------------
        //
        // Theory case split
        //
        // -----------------------------------
        uint_set m_all_th_case_split_literals;
        vector<literal_vector> m_th_case_split_sets;
        u_map< vector<literal_vector> > m_literal2casesplitsets; // returns the case split literal sets that a literal participates in

        // -----------------------------------
        //
        // Accessors
        //
        // -----------------------------------
    public:
        ast_manager & get_manager() const {
            return m_manager;
        }

        th_rewriter & get_rewriter() {
            return m_asserted_formulas.get_rewriter();
        }

        smt_params & get_fparams() {
            return m_fparams;
        }

        params_ref const & get_params() {
            return m_params;
        }

        void updt_params(params_ref const& p);

        bool get_cancel_flag();

        region & get_region() {
            return m_region;
        }

        bool relevancy() const {
            return m_fparams.m_relevancy_lvl > 0;
        }

        enode * get_enode(expr const * n) const {
            SASSERT(e_internalized(n));
            return m_app2enode[n->get_id()];
        }

        /**
           \brief Similar to get_enode, but returns 0 if n is to e_internalized.
        */
        enode * find_enode(expr const * n) const {
            return m_app2enode.get(n->get_id(), 0);
        }

        void reset_bool_vars() {
            m_expr2bool_var.reset();
        }

        bool_var get_bool_var(expr const * n) const {
            return m_expr2bool_var[n->get_id()];
        }

        bool_var get_bool_var_of_id(unsigned id) const {
            return m_expr2bool_var[id];
        }

        bool_var get_bool_var_of_id_option(unsigned id) const {
            return m_expr2bool_var.get(id, null_bool_var);
        }

#if USE_BOOL_VAR_VECTOR

        void set_bool_var(unsigned id, bool_var v) {
            m_expr2bool_var.setx(id, v, null_bool_var);
        }
#else

        void set_bool_var(unsigned id, bool_var v) {
            if (v == null_bool_var) {
                m_expr2bool_var.erase(id);
            }
            else {
                m_expr2bool_var.insert(id, v);
            }
        }
#endif

        clause_vector const& get_lemmas() const { return m_lemmas; }

        literal get_literal(expr * n) const;

        bool has_enode(bool_var v) const {
            return m_bdata[v].is_enode();
        }

        enode * bool_var2enode(bool_var v) const {
            SASSERT(m_bdata[v].is_enode());
            return m_app2enode[m_bool_var2expr[v]->get_id()];
        }

        bool_var enode2bool_var(enode const * n) const {
            SASSERT(n->is_bool());
            SASSERT(n != m_false_enode);
            return get_bool_var_of_id(n->get_owner_id());
        }

        literal enode2literal(enode const * n) const {
            SASSERT(n->is_bool());
            return n == m_false_enode ? false_literal : literal(enode2bool_var(n));
        }

        unsigned get_num_bool_vars() const {
            return m_b_internalized_stack.size();
        }

        bool_var_data & get_bdata(bool_var v) {
            return m_bdata[v];
        }

        bool_var_data const & get_bdata(bool_var v) const {
            return m_bdata[v];
        }

        lbool get_lit_assignment(unsigned lit_idx) const {
            return static_cast<lbool>(m_assignment[lit_idx]);
        }

        lbool get_assignment(literal l) const {
            return get_lit_assignment(l.index());
        }

        lbool get_assignment(bool_var v) const {
            return get_assignment(literal(v));
        }

        literal_vector const & assigned_literals() const {
            return m_assigned_literals;
        }

        lbool get_assignment(expr * n) const;

        // Similar to get_assignment, but returns l_undef if n is not internalized.
        lbool find_assignment(expr * n) const;

        lbool get_assignment(enode * n) const;

        void get_assignments(expr_ref_vector& assignments);

        b_justification get_justification(bool_var v) const {
            return get_bdata(v).justification();
        }

        void set_justification(bool_var v, bool_var_data& d, b_justification const& j);

        bool has_th_justification(bool_var v, theory_id th_id) const {
            b_justification js = get_justification(v);
            return js.get_kind() == b_justification::JUSTIFICATION && js.get_justification()->get_from_theory() == th_id;
        }

        int get_random_value() {
            return m_random();
        }

        bool is_searching() const {
            return m_searching;
        }

        svector<double> const & get_activity_vector() const {
            return m_activity;
        }

        double get_activity(bool_var v) const {
            return m_activity[v];
        }

        void set_activity(bool_var v, double & act) {
            m_activity[v] = act;
        }

        bool is_assumption(bool_var v) const {
            return get_bdata(v).m_assumption;
        }

        bool is_assumption(literal l) const {
            return is_assumption(l.var());
        }

        bool is_marked(bool_var v) const {
            return get_bdata(v).m_mark;
        }

        void set_mark(bool_var v) {
            SASSERT(!is_marked(v));
            get_bdata(v).m_mark = true;
        }

        void unset_mark(bool_var v) {
            SASSERT(is_marked(v));
            get_bdata(v).m_mark = false;
        }

        /**
           \brief Return the scope level when v was assigned.
        */
        unsigned get_assign_level(bool_var v) const {
            return get_bdata(v).m_scope_lvl;
        }

        unsigned get_assign_level(literal l) const {
            return get_assign_level(l.var());
        }

        /**
           \brief Return the scope level when v was internalized.
        */
        unsigned get_intern_level(bool_var v) const {
            return get_bdata(v).get_intern_level();
        }

        theory * get_theory(theory_id th_id) const {
            return m_theories.get_plugin(th_id);
        }
        
        ptr_vector<theory> const& theories() const { return m_theories.plugins(); }

        ptr_vector<theory>::const_iterator begin_theories() const {
            return m_theories.begin();
        }

        ptr_vector<theory>::const_iterator end_theories() const {
            return m_theories.end();
        }

        unsigned get_scope_level() const {
            return m_scope_lvl;
        }

        unsigned get_base_level() const {
            return m_base_lvl;
        }

        bool at_base_level() const {
            return m_scope_lvl == m_base_lvl;
        }

        unsigned get_search_level() const {
            return m_search_lvl;
        }

        bool at_search_level() const {
            return m_scope_lvl == m_search_lvl;
        }

        bool tracking_assumptions() const {
            return !m_assumptions.empty() && m_search_lvl > m_base_lvl;
        }

        expr * bool_var2expr(bool_var v) const {
            return m_bool_var2expr[v];
        }

        void literal2expr(literal l, expr_ref & result) const {
            if (l == true_literal)
                result = m_manager.mk_true();
            else if (l == false_literal)
                result = m_manager.mk_false();
            else if (l.sign())
                result = m_manager.mk_not(bool_var2expr(l.var()));
            else
                result = bool_var2expr(l.var());
        }

        bool is_true(enode const * n) const {
            return n == m_true_enode;
        }

        bool is_false(enode const * n) const {
            return n == m_false_enode;
        }

        unsigned get_num_enodes_of(func_decl const * decl) const {
            unsigned id = decl->get_decl_id();
            return id < m_decl2enodes.size() ? m_decl2enodes[id].size() : 0;
        }

        enode_vector const& enodes_of(func_decl const * d) const {
            unsigned id = d->get_decl_id();
            return id < m_decl2enodes.size() ? m_decl2enodes[id] : m_empty_vector;
        }

        enode_vector::const_iterator begin_enodes_of(func_decl const * decl) const {
            unsigned id = decl->get_decl_id();
            return id < m_decl2enodes.size() ? m_decl2enodes[id].begin() : nullptr;
        }

        enode_vector::const_iterator end_enodes_of(func_decl const * decl) const {
            unsigned id = decl->get_decl_id();
            return id < m_decl2enodes.size() ? m_decl2enodes[id].end() : nullptr;
        }

        ptr_vector<enode> const& enodes() const { return m_enodes; }

        ptr_vector<enode>::const_iterator begin_enodes() const {
            return m_enodes.begin();
        }

        ptr_vector<enode>::const_iterator end_enodes() const {
            return m_enodes.end();
        }

        unsigned get_generation(quantifier * q) const {
            return m_qmanager->get_generation(q);
        }

        /**
           \brief Return true if the logical context internalized universal quantifiers.
        */
        bool internalized_quantifiers() const {
            return !m_qmanager->empty();
        }

        /**
           \brief Return true if the logical context internalized or will internalize universal quantifiers.
        */
        bool has_quantifiers() const {
            return m_asserted_formulas.has_quantifiers();
        }

        fingerprint * add_fingerprint(void * data, unsigned data_hash, unsigned num_args, enode * const * args, expr* def = 0) {
            return m_fingerprints.insert(data, data_hash, num_args, args, def);
        }

        theory_id get_var_theory(bool_var v) const {
            return get_bdata(v).get_theory();
        }

        friend class set_var_theory_trail;
        void set_var_theory(bool_var v, theory_id tid);

        // -----------------------------------
        //
        // Backtracking support
        //
        // -----------------------------------
    protected:
        typedef ptr_vector<trail<context> >   trail_stack;
        trail_stack                           m_trail_stack;
#ifdef Z3DEBUG
        bool                                  m_trail_enabled;
#endif

    public:
        template<typename TrailObject>
        void push_trail(const TrailObject & obj) {
            SASSERT(m_trail_enabled);
            m_trail_stack.push_back(new (m_region) TrailObject(obj));
        }

        void push_trail_ptr(trail<context> * ptr) {
            m_trail_stack.push_back(ptr);
        }

    protected:

        unsigned                    m_scope_lvl;
        unsigned                    m_base_lvl;
        unsigned                    m_search_lvl; // It is greater than m_base_lvl when assumptions are used.  Otherwise, it is equals to m_base_lvl
        struct scope {
            unsigned                m_assigned_literals_lim;
            unsigned                m_trail_stack_lim;
            unsigned                m_aux_clauses_lim;
            unsigned                m_justifications_lim;
            unsigned                m_units_to_reassert_lim;
        };
        struct base_scope {
            unsigned                m_lemmas_lim;
            unsigned                m_simp_qhead_lim;
            unsigned                m_inconsistent;
        };

        svector<scope>              m_scopes;
        svector<base_scope>         m_base_scopes;

        void push_scope();

        unsigned pop_scope_core(unsigned num_scopes);

        void pop_scope(unsigned num_scopes);

        void undo_trail_stack(unsigned old_size);

        void unassign_vars(unsigned old_lim);

        void remove_watch_literal(clause * cls, unsigned idx);

        void remove_lit_occs(clause * cls);

        void remove_cls_occs(clause * cls);

        void del_clause(clause * cls);

        void del_clauses(clause_vector & v, unsigned old_size);

        void del_justifications(ptr_vector<justification> & justifications, unsigned old_lim);

        bool is_unit_clause(clause const * c) const;

        bool is_empty_clause(clause const * c) const;

        void cache_generation(unsigned new_scope_lvl);

        void cache_generation(clause const * cls, unsigned new_scope_lvl);

        void cache_generation(unsigned num_lits, literal const * lits, unsigned new_scope_lvl);

        void cache_generation(expr * n, unsigned new_scope_lvl);

        void reset_cache_generation();

        void reinit_clauses(unsigned num_scopes, unsigned num_bool_vars);

        void reassert_units(unsigned units_to_reassert_lim);

    public:
        // \brief exposed for PB solver to participate in GC

        void remove_watch(bool_var v);

        void mark_as_deleted(clause * cls);


        // -----------------------------------
        //
        // Internalization
        //
        // -----------------------------------
    public:
        bool b_internalized(expr const * n) const {
            return get_bool_var_of_id_option(n->get_id()) != null_bool_var;
        }

        bool lit_internalized(expr const * n) const {
            return m_manager.is_false(n) || (m_manager.is_not(n) ? b_internalized(to_app(n)->get_arg(0)) : b_internalized(n));
        }

        bool e_internalized(expr const * n) const {
            return m_app2enode.get(n->get_id(), 0) != 0;
        }

        unsigned get_num_b_internalized() const {
            return m_b_internalized_stack.size();
        }

        expr * get_b_internalized(unsigned idx) const {
            return  m_b_internalized_stack.get(idx);
        }

        unsigned get_num_e_internalized() const {
            return m_e_internalized_stack.size();
        }

        expr * get_e_internalized(unsigned idx) const {
            return  m_e_internalized_stack.get(idx);
        }

        /**
           \brief Return the position (in the assignment stack) of the decision literal at the given scope level.
        */
        unsigned get_decision_literal_pos(unsigned scope_lvl) const {
            SASSERT(scope_lvl > m_base_lvl);
            return m_scopes[scope_lvl - 1].m_assigned_literals_lim;
        }

    protected:
        unsigned m_generation; //!< temporary variable used during internalization

    public:
        bool binary_clause_opt_enabled() const {
            return !m_manager.proofs_enabled() && m_fparams.m_binary_clause_opt;
        }
    protected:
        bool_var_data & get_bdata(expr const * n) {
            return get_bdata(get_bool_var(n));
        }

        bool_var_data const & get_bdata(expr const * n) const {
            return get_bdata(get_bool_var(n));
        }

        typedef std::pair<expr *, bool> expr_bool_pair;

        void ts_visit_child(expr * n, bool gate_ctx, svector<int> & tcolors, svector<int> & fcolors, svector<expr_bool_pair> & todo, bool & visited);

        bool ts_visit_children(expr * n, bool gate_ctx, svector<int> & tcolors, svector<int> & fcolors, svector<expr_bool_pair> & todo);

        void top_sort_expr(expr * n, svector<expr_bool_pair> & sorted_exprs);

        void assert_default(expr * n, proof * pr);

        void assert_distinct(app * n, proof * pr);

        void internalize_formula(expr * n, bool gate_ctx);

        void internalize_eq(app * n, bool gate_ctx);

        void internalize_distinct(app * n, bool gate_ctx);

        bool internalize_theory_atom(app * n, bool gate_ctx);

        void internalize_quantifier(quantifier * q, bool gate_ctx);

        void internalize_lambda(quantifier * q);

        void internalize_formula_core(app * n, bool gate_ctx);

        void set_merge_tf(enode * n, bool_var v, bool is_new_var);

        friend class set_enode_flag_trail;

    public:
        void set_enode_flag(bool_var v, bool is_new_var);

    protected:
        void internalize_term(app * n);

        void internalize_ite_term(app * n);

        bool internalize_theory_term(app * n);

        void internalize_uninterpreted(app * n);

        friend class mk_bool_var_trail;
        class mk_bool_var_trail : public trail<context> {
        public:
            void undo(context & ctx) override { ctx.undo_mk_bool_var(); }
        };
        mk_bool_var_trail   m_mk_bool_var_trail;

        void undo_mk_bool_var();

        friend class mk_enode_trail;
        class mk_enode_trail : public trail<context> {
        public:
            void undo(context & ctx) override { ctx.undo_mk_enode(); }
        };

        mk_enode_trail   m_mk_enode_trail;

        void undo_mk_enode();

        void apply_sort_cnstr(app * term, enode * e);

        bool simplify_aux_clause_literals(unsigned & num_lits, literal * lits, literal_buffer & simp_lits);

        bool simplify_aux_lemma_literals(unsigned & num_lits, literal * lits);

        void mark_for_reinit(clause * cls, unsigned scope_lvl, bool reinternalize_atoms);

        unsigned get_max_iscope_lvl(unsigned num_lits, literal const * lits) const;

        bool use_binary_clause_opt(literal l1, literal l2, bool lemma) const;

        int select_learned_watch_lit(clause const * cls) const;

        int select_watch_lit(clause const * cls, int starting_at) const;

        void add_watch_literal(clause * cls, unsigned idx);

        proof * mk_clause_def_axiom(unsigned num_lits, literal * lits, expr * root_gate);

    public:
        void mk_gate_clause(unsigned num_lits, literal * lits);

        void mk_gate_clause(literal l1, literal l2);

        void mk_gate_clause(literal l1, literal l2, literal l3);

        void mk_gate_clause(literal l1, literal l2, literal l3, literal l4);

    protected:
        void mk_root_clause(unsigned num_lits, literal * lits, proof * pr);

        void mk_root_clause(literal l1, literal l2, proof * pr);

        void mk_root_clause(literal l1, literal l2, literal l3, proof * pr);

        void add_and_rel_watches(app * n);

        void add_or_rel_watches(app * n);

        void add_ite_rel_watches(app * n);

        void mk_not_cnstr(app * n);

        void mk_and_cnstr(app * n);

        void mk_or_cnstr(app * n);

        void mk_iff_cnstr(app * n);

        void mk_ite_cnstr(app * n);

        bool lit_occs_enabled() const { return m_fparams.m_phase_selection==PS_OCCURRENCE; }

        void add_lit_occs(clause * cls);
    public:
        void internalize(expr * n, bool gate_ctx);

        void internalize(expr * n, bool gate_ctx, unsigned generation);

        clause * mk_clause(unsigned num_lits, literal * lits, justification * j, clause_kind k = CLS_AUX, clause_del_eh * del_eh = nullptr);

        void mk_clause(literal l1, literal l2, justification * j);

        void mk_clause(literal l1, literal l2, literal l3, justification * j);

        void mk_th_axiom(theory_id tid, unsigned num_lits, literal * lits, unsigned num_params = 0, parameter * params = nullptr);

        void mk_th_axiom(theory_id tid, literal l1, literal l2, unsigned num_params = 0, parameter * params = nullptr);

        void mk_th_axiom(theory_id tid, literal l1, literal l2, literal l3, unsigned num_params = 0, parameter * params = nullptr);

        /*
         * Provide a hint to the core solver that the specified literals form a "theory case split".
         * The core solver will enforce the condition that exactly one of these literals can be
         * assigned 'true' at any time.
         * We assume that the theory solver has already asserted the disjunction of these literals
         * or some other axiom that means at least one of them must be assigned 'true'.
         */
        void mk_th_case_split(unsigned num_lits, literal * lits);


        /*
         * Provide a hint to the branching heuristic about the priority of a "theory-aware literal".
         * Literals marked in this way will always be branched on before unmarked literals,
         * starting with the literal having the highest priority.
         */
        void add_theory_aware_branching_info(bool_var v, double priority, lbool phase);

    public:

        // helper function for trail
        void undo_th_case_split(literal l);

        bool propagate_th_case_split(unsigned qhead);

        bool_var mk_bool_var(expr * n);

        enode * mk_enode(app * n, bool suppress_args, bool merge_tf, bool cgc_enabled);

        void attach_th_var(enode * n, theory * th, theory_var v);

        template<typename Justification>
        justification * mk_justification(Justification const & j) {
            justification * js = new (m_region) Justification(j);
            SASSERT(js->in_region());
            if (js->has_del_eh())
                m_justifications.push_back(js);
            return js;
        }

        // -----------------------------------
        //
        // Engine
        //
        // -----------------------------------
    protected:
        lbool              m_last_search_result;
        failure            m_last_search_failure;
        ptr_vector<theory> m_incomplete_theories; //!< theories that failed to produce a model
        bool               m_searching;
        unsigned           m_num_conflicts;
        unsigned           m_num_conflicts_since_restart;
        unsigned           m_num_conflicts_since_lemma_gc;
        unsigned           m_num_restarts;
        unsigned           m_num_simplifications;
        unsigned           m_restart_threshold;
        unsigned           m_restart_outer_threshold;
        unsigned           m_luby_idx;
        double             m_agility;
        unsigned           m_lemma_gc_threshold;

        void assign_core(literal l, b_justification j, bool decision = false);
        void trace_assign(literal l, b_justification j, bool decision) const;

    public:
        void assign(literal l, const b_justification & j, bool decision = false) {
            SASSERT(l != false_literal);
            SASSERT(l != null_literal);
            switch (get_assignment(l)) {
            case l_false:
                set_conflict(j, ~l);
                break;
            case l_undef:
                assign_core(l, j, decision);
                break;
            case l_true:
                return;
            }
        }

        void assign(literal l, justification * j, bool decision = false) {
            assign(l, j ? b_justification(j) : b_justification::mk_axiom(), decision);
        }

        friend class set_true_first_trail;
        void set_true_first_flag(bool_var v);

        bool try_true_first(bool_var v) const { return get_bdata(v).try_true_first(); }

        bool assume_eq(enode * lhs, enode * rhs);

        bool is_shared(enode * n) const;

        void assign_eq(enode * lhs, enode * rhs, eq_justification const & js) {
            push_eq(lhs, rhs, js);
        }

        /**
           \brief Force the given phase next time we case split v.
           This method has no effect if phase caching is disabled.
        */
        void force_phase(bool_var v, bool phase) {
            bool_var_data & d   = get_bdata(v);
            d.m_phase_available = true;
            d.m_phase           = phase;
        }

        void force_phase(literal l) {
            force_phase(l.var(), !l.sign());
        }

        bool contains_instance(quantifier * q, unsigned num_bindings, enode * const * bindings);

        bool add_instance(quantifier * q, app * pat, unsigned num_bindings, enode * const * bindings, expr* def, unsigned max_generation,
                          unsigned min_top_generation, unsigned max_top_generation, vector<std::tuple<enode *, enode*>> & used_enodes /*gives the equalities used for the pattern match, see mam.cpp for more info*/);

        void set_global_generation(unsigned generation) { m_generation = generation; }

#ifdef Z3DEBUG
        bool slow_contains_instance(quantifier const * q, unsigned num_bindings, enode * const * bindings) const {
            return m_fingerprints.slow_contains(q, q->get_id(), num_bindings, bindings);
        }
#endif

    protected:
        void push_new_th_eq(theory_id th, theory_var lhs, theory_var rhs);

        void push_new_th_diseq(theory_id th, theory_var lhs, theory_var rhs);

        friend class add_eq_trail;

        void add_eq(enode * n1, enode * n2, eq_justification js);

        void remove_parents_from_cg_table(enode * r1);

        void reinsert_parents_into_cg_table(enode * r1, enode * r2, enode * n1, enode * n2, eq_justification js);

        void invert_trans(enode * n);

        theory_var get_closest_var(enode * n, theory_id th_id);

        void merge_theory_vars(enode * r2, enode * r1, eq_justification js);

        void propagate_bool_enode_assignment(enode * r1, enode * r2, enode * n1, enode * n2);

        void propagate_bool_enode_assignment_core(enode * source, enode * target);

        void undo_add_eq(enode * r1, enode * n1, unsigned r2_num_parents);

        void restore_theory_vars(enode * r2, enode * r1);

        void push_eq(enode * lhs, enode * rhs, eq_justification const & js) {
            SASSERT(lhs != rhs);
            SASSERT(lhs->get_root() != rhs->get_root());
            m_eq_propagation_queue.push_back(new_eq(lhs, rhs, js));
        }

        void push_new_congruence(enode * n1, enode * n2, bool used_commutativity) {
            SASSERT(n1->m_cg == n2);
            // if (is_relevant(n1)) mark_as_relevant(n2);
            push_eq(n1, n2, eq_justification::mk_cg(used_commutativity));
        }

        bool add_diseq(enode * n1, enode * n2);

        void assign_quantifier(quantifier * q);

        void set_conflict(const b_justification & js, literal not_l);

        void set_conflict(const b_justification & js) {
            set_conflict(js, null_literal);
        }

    public:
        void set_conflict(justification * js) {
            SASSERT(js);
            set_conflict(b_justification(js));
        }

        bool inconsistent() const {
            return m_conflict != null_b_justification;
        }

        unsigned get_num_conflicts() const {
            return m_num_conflicts;
        }

        static bool is_eq(enode const * n1, enode const * n2) { return n1->get_root() == n2->get_root(); }

        bool is_diseq(enode * n1, enode * n2) const;

        bool is_diseq_slow(enode * n1, enode * n2) const;

        bool is_ext_diseq(enode * n1, enode * n2, unsigned depth);

        enode * get_enode_eq_to(func_decl * f, unsigned num_args, enode * const * args);

        expr* next_decision();

    protected:
        bool decide();

        void update_phase_cache_counter();

#define ACTIVITY_LIMIT 1e100
#define INV_ACTIVITY_LIMIT 1e-100

        void rescale_bool_var_activity();

    public:
        void inc_bvar_activity(bool_var v) {
            double & act = m_activity[v];
            act += m_bvar_inc;
            if (act > ACTIVITY_LIMIT)
                rescale_bool_var_activity();
            m_case_split_queue->activity_increased_eh(v);
            TRACE("case_split", tout << "v" << v << " " << m_bvar_inc << " -> " << act << "\n";);
        }

    protected:

        void decay_bvar_activity() {
            m_bvar_inc *= m_fparams.m_inv_decay;
        }

        bool simplify_clause(clause * cls);

        unsigned simplify_clauses(clause_vector & clauses, unsigned starting_at);

        void simplify_clauses();

        /**
           \brief Return true if the give clause is justifying some literal.
        */
        bool is_justifying(clause * cls) const {
            for (unsigned i = 0; i < 2; i++) {
                b_justification js;
                js = get_justification(cls->get_literal(i).var());
                if (js.get_kind() == b_justification::CLAUSE && js.get_clause() == cls)
                    return true;
            }
            return false;
        }

        bool can_delete(clause * cls) const {
            if (cls->in_reinit_stack())
                return false;
            return !is_justifying(cls);
        }

        void del_inactive_lemmas();

        void del_inactive_lemmas1();

        void del_inactive_lemmas2();

        bool more_than_k_unassigned_literals(clause * cls, unsigned k);

        void internalize_assertions();

        bool validate_assumptions(expr_ref_vector const& asms);

        void init_assumptions(expr_ref_vector const& asms);

        void init_clause(expr_ref_vector const& clause);

        lbool decide_clause();

        void reset_tmp_clauses();

        void reset_assumptions();

        void add_theory_assumptions(expr_ref_vector & theory_assumptions);

        lbool mk_unsat_core(lbool result);

        void validate_unsat_core();

        void init_search();

        void end_search();

        lbool search();

        void inc_limits();

        bool restart(lbool& status, unsigned curr_lvl);

        void tick(unsigned & counter) const;

        lbool bounded_search();

        final_check_status final_check();

        void check_proof(proof * pr);

        void forget_phase_of_vars_in_current_level();

        virtual bool resolve_conflict();

        // -----------------------------------
        //
        // Propagation
        //
        // -----------------------------------
    protected:
        bool bcp();

        bool propagate_eqs();

        bool propagate_atoms();

        void push_new_th_diseqs(enode * r, theory_var v, theory * th);

        void propagate_bool_var_enode(bool_var v);

        bool is_relevant_core(expr * n) const { return m_relevancy_propagator->is_relevant(n); }

        svector<bool>  m_relevant_conflict_literals;
        void record_relevancy(unsigned n, literal const* lits);
        void restore_relevancy(unsigned n, literal const* lits);

    public:
        // event handler for relevancy_propagator class
        void relevant_eh(expr * n);

        bool is_relevant(expr * n) const {
            return !relevancy() || is_relevant_core(n);
        }

        bool is_relevant(enode * n) const {
            return is_relevant(n->get_owner());
        }

        bool is_relevant(bool_var v) const {
            return is_relevant(bool_var2expr(v));
        }

        bool is_relevant(literal l) const {
            SASSERT(l != true_literal && l != false_literal);
            return is_relevant(l.var());
        }

        bool is_relevant_core(literal l) const {
            return is_relevant_core(bool_var2expr(l.var()));
        }

        void mark_as_relevant(expr * n) { m_relevancy_propagator->mark_as_relevant(n); m_relevancy_propagator->propagate(); }

        void mark_as_relevant(enode * n) { mark_as_relevant(n->get_owner()); }

        void mark_as_relevant(bool_var v) { mark_as_relevant(bool_var2expr(v)); }

        void mark_as_relevant(literal l) { mark_as_relevant(l.var()); }

        template<typename Eh>
        relevancy_eh * mk_relevancy_eh(Eh const & eh) {
            return m_relevancy_propagator->mk_relevancy_eh(eh);
        }

        void add_relevancy_eh(expr * source, relevancy_eh * eh) { m_relevancy_propagator->add_handler(source, eh); }
        void add_relevancy_dependency(expr * source, expr * target) { m_relevancy_propagator->add_dependency(source, target); }
        void add_rel_watch(literal l, relevancy_eh * eh) { m_relevancy_propagator->add_watch(bool_var2expr(l.var()), !l.sign(), eh); }
        void add_rel_watch(literal l, expr * n) { m_relevancy_propagator->add_watch(bool_var2expr(l.var()), !l.sign(), n); }

    protected:
        lbool get_assignment_core(expr * n) const;

        void propagate_relevancy(unsigned qhead);

        bool propagate_theories();

        void propagate_th_eqs();

        void propagate_th_diseqs();

        bool can_theories_propagate() const;

        bool propagate();

        void add_rec_funs_to_model();

    public:
        bool can_propagate() const;

        // -----------------------------------
        //
        // Model checking... (must be improved)
        //
        // -----------------------------------
    public:
        bool get_value(enode * n, expr_ref & value);

        // -----------------------------------
        //
        // Pretty Printing
        //
        // -----------------------------------
    protected:
        ast_mark m_pp_visited;

        ast_mark & get_pp_visited() const {  return const_cast<ast_mark&>(m_pp_visited); }

    public:
        void display_enode_defs(std::ostream & out) const;

        void display_bool_var_defs(std::ostream & out) const;

        void display_asserted_formulas(std::ostream & out) const;

        std::ostream& display_literal(std::ostream & out, literal l) const;

        std::ostream& display_detailed_literal(std::ostream & out, literal l) const { l.display(out, m_manager, m_bool_var2expr.c_ptr()); return out; }

        void display_literal_info(std::ostream & out, literal l) const;

        std::ostream& display_literals(std::ostream & out, unsigned num_lits, literal const * lits) const;

        std::ostream& display_literals(std::ostream & out, literal_vector const& lits) const {
            return display_literals(out, lits.size(), lits.c_ptr());
        }

        std::ostream& display_literal_verbose(std::ostream & out, literal lit) const;

        std::ostream& display_literals_verbose(std::ostream & out, unsigned num_lits, literal const * lits) const;
        
        std::ostream& display_literals_verbose(std::ostream & out, literal_vector const& lits) const {
            return display_literals_verbose(out, lits.size(), lits.c_ptr());
        }

        void display_watch_list(std::ostream & out, literal l) const;

        void display_watch_lists(std::ostream & out) const;

        void display_clause_detail(std::ostream & out, clause const * cls) const;

        void display_clause(std::ostream & out, clause const * cls) const;

        void display_clauses(std::ostream & out, ptr_vector<clause> const & v) const;

        void display_binary_clauses(std::ostream & out) const;

        void display_assignment(std::ostream & out) const;

        void display_eqc(std::ostream & out) const;

        void display_app_enode_map(std::ostream & out) const;

        void display_expr_bool_var_map(std::ostream & out) const;

        void display_relevant_exprs(std::ostream & out) const;

        void display_theories(std::ostream & out) const;

        void display_eq_detail(std::ostream & out, enode * n) const;

        void display_parent_eqs(std::ostream & out, enode * n) const;

        void display_hot_bool_vars(std::ostream & out) const;

        void display_lemma_as_smt_problem(std::ostream & out, unsigned num_antecedents, literal const * antecedents, literal consequent = false_literal, symbol const& logic = symbol::null) const;

        unsigned display_lemma_as_smt_problem(unsigned num_antecedents, literal const * antecedents, literal consequent = false_literal, symbol const& logic = symbol::null) const;
        void display_lemma_as_smt_problem(std::ostream & out, unsigned num_antecedents, literal const * antecedents,
                                          unsigned num_antecedent_eqs, enode_pair const * antecedent_eqs,
                                          literal consequent = false_literal, symbol const& logic = symbol::null) const;

        unsigned display_lemma_as_smt_problem(unsigned num_antecedents, literal const * antecedents,
                                          unsigned num_antecedent_eqs, enode_pair const * antecedent_eqs,
                                          literal consequent = false_literal, symbol const& logic = symbol::null) const;

        void display_assignment_as_smtlib2(std::ostream& out, symbol const& logic = symbol::null) const;

        void display_normalized_enodes(std::ostream & out) const;

        void display_enodes_lbls(std::ostream & out) const;

        void display_decl2enodes(std::ostream & out) const;

        void display_subexprs_info(std::ostream & out, expr * n) const;

        void display_var_occs_histogram(std::ostream & out) const;

        void display_num_min_occs(std::ostream & out) const;

        void display_profile_res_sub(std::ostream & out) const;

        void display_profile(std::ostream & out) const;

        void display(std::ostream& out, b_justification j) const;

        // -----------------------------------
        //
        // Debugging support
        //
        // -----------------------------------
    protected:
#ifdef Z3DEBUG
        bool is_watching_clause(literal l, clause const * cls) const;

        bool check_clause(clause const * cls) const;

        bool check_clauses(clause_vector const & v) const;

        bool check_watch_list(literal l) const;

        bool check_watch_list(unsigned l_idx) const;

        bool check_bin_watch_lists() const;

        bool check_enode(enode * n) const;

        bool check_enodes() const;

        bool check_invariant() const;

        bool check_eqc_bool_assignment() const;

        bool check_missing_clause_propagation(clause_vector const & v) const;

        bool check_missing_bin_clause_propagation() const;

        bool check_missing_eq_propagation() const;

        bool check_missing_congruence() const;

        bool check_missing_bool_enode_propagation() const;

        bool check_missing_propagation() const;

        bool check_relevancy(expr_ref_vector const & v) const;

        bool check_relevancy() const;

        bool check_bool_var_vector_sizes() const;

        bool check_th_diseq_propagation() const;

        bool check_missing_diseq_conflict() const;

        bool check_lit_occs(literal l) const;

        bool check_lit_occs() const;
#endif
        // -----------------------------------
        //
        // Introspection
        //
        // -----------------------------------
        unsigned get_lemma_avg_activity() const;
        void display_literal_num_occs(std::ostream & out) const;
        void display_num_assigned_literals_per_lvl(std::ostream & out) const;

        // -----------------------------------
        //
        // Auxiliary
        //
        // -----------------------------------
        void init();
        void flush();
        config_mode get_config_mode(bool use_static_features) const;
        virtual void setup_context(bool use_static_features);
        void setup_components();
        void pop_to_base_lvl();
        void pop_to_search_lvl();
#ifdef Z3DEBUG
        bool already_internalized_theory(theory * th) const;
        bool already_internalized_theory_core(theory * th, expr_ref_vector const & s) const;
#endif
        bool check_preamble(bool reset_cancel);
        lbool check_finalize(lbool r);

        // -----------------------------------
        //
        // API
        //
        // -----------------------------------
        void assert_expr_core(expr * e, proof * pr);

        // copy plugins into a fresh context.
        void copy_plugins(context& src, context& dst);

        static literal translate_literal(
            literal lit, context& src_ctx, context& dst_ctx,
            vector<bool_var> b2v, ast_translation& tr);

        /*
          \brief Utilities for consequence finding.
        */
        typedef hashtable<unsigned, u_hash, u_eq> index_set;
        //typedef uint_set index_set;
        u_map<index_set> m_antecedents;
        obj_map<expr, expr*> m_var2orig;
        obj_map<expr, expr*> m_assumption2orig;
        obj_map<expr, expr*> m_var2val;
        void extract_fixed_consequences(literal lit, index_set const& assumptions, expr_ref_vector& conseq);
        void extract_fixed_consequences(unsigned& idx, index_set const& assumptions, expr_ref_vector& conseq);

        void display_consequence_progress(std::ostream& out, unsigned it, unsigned nv, unsigned fixed, unsigned unfixed, unsigned eq);

        unsigned delete_unfixed(expr_ref_vector& unfixed);

        unsigned extract_fixed_eqs(expr_ref_vector& conseq);

        expr_ref antecedent2fml(index_set const& ante);


        literal mk_diseq(expr* v, expr* val);

        void validate_consequences(expr_ref_vector const& assumptions, expr_ref_vector const& vars,
                                   expr_ref_vector const& conseq, expr_ref_vector const& unfixed);

        bool validate_justification(bool_var v, bool_var_data const& d, b_justification const& j);

        void justify(literal lit, index_set& s);

        void extract_cores(expr_ref_vector const& asms, vector<expr_ref_vector>& cores, unsigned& min_core_size);

        void preferred_sat(literal_vector& literals);

        void display_partial_assignment(std::ostream& out, expr_ref_vector const& asms, unsigned min_core_size);

    public:
        context(ast_manager & m, smt_params & fp, params_ref const & p = params_ref());


        virtual ~context();

        /**
           \brief Return a new context containing the same theories and simplifier plugins, but with an empty
           set of assertions.

           If l == 0, then the logic of this context is used in the new context.
           If p == 0, then this->m_params is used
        */
        context * mk_fresh(symbol const * l = nullptr,  smt_params * smtp = nullptr, params_ref const & p = params_ref());

        static void copy(context& src, context& dst);

        /**
           \brief Translate context to use new manager m.
         */

        app * mk_eq_atom(expr * lhs, expr * rhs);

        bool set_logic(symbol const& logic) { return m_setup.set_logic(logic); }

        void register_plugin(theory * th);

        void assert_expr(expr * e);

        void assert_expr(expr * e, proof * pr);

        void push();

        void pop(unsigned num_scopes);

        lbool check(unsigned num_assumptions = 0, expr * const * assumptions = nullptr, bool reset_cancel = true, bool already_did_theory_assumptions = false);

        lbool check(expr_ref_vector const& cube, vector<expr_ref_vector> const& clauses);

        lbool get_consequences(expr_ref_vector const& assumptions, expr_ref_vector const& vars, expr_ref_vector& conseq, expr_ref_vector& unfixed);

        lbool find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes);

        lbool preferred_sat(expr_ref_vector const& asms, vector<expr_ref_vector>& cores);

        lbool setup_and_check(bool reset_cancel = true);

        // return 'true' if assertions are inconsistent.
        bool reduce_assertions();

        bool resource_limits_exceeded();

        failure get_last_search_failure() const;

        proof * get_proof();

        void get_relevant_labels(expr* cnstr, buffer<symbol> & result);

        void get_relevant_labeled_literals(bool at_lbls, expr_ref_vector & result);

        void get_relevant_literals(expr_ref_vector & result);

        void get_guessed_literals(expr_ref_vector & result);

        void internalize_assertion(expr * n, proof * pr, unsigned generation);

        void internalize_proxies(expr_ref_vector const& asms, vector<std::pair<expr*,expr_ref>>& asm2proxy);

        void internalize_instance(expr * body, proof * pr, unsigned generation) {
            internalize_assertion(body, pr, generation);
            if (relevancy())
                m_case_split_queue->internalize_instance_eh(body, generation);
        }

        bool already_internalized() const { return m_e_internalized_stack.size() > 2 || m_b_internalized_stack.size() > 1; }

        unsigned get_unsat_core_size() const {
            return m_unsat_core.size();
        }

        expr * get_unsat_core_expr(unsigned idx) const {
            return m_unsat_core.get(idx);
        }

        void get_model(model_ref & m) const;

        bool update_model(bool refinalize);

        void get_proto_model(proto_model_ref & m) const;

        bool validate_model();

        unsigned get_num_asserted_formulas() const { return m_asserted_formulas.get_num_formulas(); }

        unsigned get_asserted_formulas_last_level() const { return m_asserted_formulas.get_formulas_last_level(); }

        expr * get_asserted_formula(unsigned idx) const { return m_asserted_formulas.get_formula(idx); }

        proof * get_asserted_formula_proof(unsigned idx) const { return m_asserted_formulas.get_formula_proof(idx); }

        void get_asserted_formulas(ptr_vector<expr>& r) const { m_asserted_formulas.get_assertions(r); }

        //proof * const * get_asserted_formula_proofs() const { return m_asserted_formulas.get_formula_proofs(); }

        void get_assertions(ptr_vector<expr> & result) { m_asserted_formulas.get_assertions(result); }

        void display(std::ostream & out) const;

        void display_unsat_core(std::ostream & out) const;

        void collect_statistics(::statistics & st) const;

        void display_statistics(std::ostream & out) const;
        void display_istatistics(std::ostream & out) const;

        // -----------------------------------
        //
        // Macros
        //
        // -----------------------------------
    public:
        unsigned get_num_macros() const { return m_asserted_formulas.get_num_macros(); }
        unsigned get_first_macro_last_level() const { return m_asserted_formulas.get_first_macro_last_level(); }
        func_decl * get_macro_func_decl(unsigned i) const { return m_asserted_formulas.get_macro_func_decl(i); }
        func_decl * get_macro_interpretation(unsigned i, expr_ref & interp) const { return m_asserted_formulas.get_macro_interpretation(i, interp); }
        quantifier * get_macro_quantifier(func_decl * f) const { return m_asserted_formulas.get_macro_quantifier(f); }
        void insert_macro(func_decl * f, quantifier * m, proof * pr, expr_dependency * dep) { m_asserted_formulas.insert_macro(f, m, pr, dep); }
    };

};

#endif /* SMT_CONTEXT_H_ */

