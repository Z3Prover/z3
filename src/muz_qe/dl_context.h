/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_context.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-18.

Revision History:

--*/
#ifndef _DL_CONTEXT_H_
#define _DL_CONTEXT_H_

#ifdef _CYGWIN
#undef min
#undef max
#endif
#include"arith_decl_plugin.h"
#include"front_end_params.h"
#include"map.h"
#include"th_rewriter.h"
#include"str_hashtable.h"
#include"var_subst.h"
#include"dl_base.h"
#include"dl_costs.h"
#include"dl_decl_plugin.h"
#include"dl_relation_manager.h"
#include"dl_rule_set.h"
#include"pdr_dl_interface.h"
#include"dl_bmc_engine.h"
#include"lbool.h"
#include"statistics.h"
#include"params.h"
#include"trail.h"
#include"dl_external_relation.h"
#include"model_converter.h"
#include"proof_converter.h"
#include"model2expr.h"

namespace datalog {

    class rule_transformer;

    enum execution_result {
        OK,
        TIMEOUT,
        MEMOUT,
        INPUT_ERROR
    };

    class context {
    public:
        typedef unsigned finite_element;
        enum sort_kind {
            SK_UINT64,
            SK_SYMBOL
        };

    private:
        class sort_domain;
        class symbol_sort_domain;
        class uint64_sort_domain;
        class restore_rules;
        class contains_pred;

        typedef hashtable<symbol, symbol_hash_proc, symbol_eq_proc> symbol_set;
        typedef map<symbol, func_decl*, symbol_hash_proc, symbol_eq_proc> sym2decl;
        typedef obj_map<const func_decl, svector<symbol> > pred2syms;
        typedef obj_map<const sort, sort_domain*> sort_domain_map;
        typedef vector<std::pair<func_decl*,relation_fact> > fact_vector;


        ast_manager &      m;
        front_end_params&  m_fparams;
        params_ref         m_params;
        dl_decl_util       m_decl_util;
        th_rewriter        m_rewriter;
        var_subst          m_var_subst;
        relation_manager   m_rmanager;
        rule_manager       m_rule_manager;

        trail_stack<context> m_trail;
        ast_ref_vector     m_pinned;
        app_ref_vector     m_vars;
        sort_domain_map    m_sorts;
        func_decl_set      m_preds;
        sym2decl           m_preds_by_name;
        pred2syms          m_argument_var_names;
        decl_set           m_output_preds;
        rule_set           m_rule_set;
        expr_ref_vector    m_background;

        scoped_ptr<pdr::dl_interface>   m_pdr;
        scoped_ptr<bmc>                 m_bmc;

        bool               m_closed;
        bool               m_saturation_was_run;
        execution_result   m_last_status;
        relation_base *    m_last_result_relation;
        expr_ref           m_last_answer;
        DL_ENGINE          m_engine;
        volatile bool      m_cancel;
        fact_vector        m_table_facts;

        bool is_fact(app * head) const;
        bool has_sort_domain(relation_sort s) const;
        sort_domain & get_sort_domain(relation_sort s);
        const sort_domain & get_sort_domain(relation_sort s) const;

        relation_plugin & get_ordinary_relation_plugin(symbol relation_name);

        class engine_type_proc;


    public:
        context(ast_manager & m, front_end_params& params, params_ref const& p = params_ref());
        ~context();
        void reset();

        void push();
        void pop();
        
        relation_base & get_relation(func_decl * pred) { return get_rmanager().get_relation(pred); }
        relation_base * try_get_relation(func_decl * pred) const { return get_rmanager().try_get_relation(pred); }

        bool saturation_was_run() const { return m_saturation_was_run; }
        void notify_saturation_was_run() { m_saturation_was_run = true; }

        /**
           \brief Store the relation \c rel under the predicate \c pred. The \c context object
           takes over the ownership of the relation object.
        */
        void store_relation(func_decl * pred, relation_base * rel) {
            get_rmanager().store_relation(pred, rel);
        }

        void configure_engine();

        ast_manager & get_manager() const { return m; }
        relation_manager & get_rmanager() { return m_rmanager; }
        const relation_manager & get_rmanager() const { return m_rmanager; }
        rule_manager & get_rule_manager() { return m_rule_manager; }
        front_end_params & get_fparams() const { return m_fparams; }
        params_ref const&  get_params() const { return m_params; }
        DL_ENGINE get_engine() { configure_engine(); return m_engine; }
        th_rewriter& get_rewriter() { return m_rewriter; }
        var_subst & get_var_subst() { return m_var_subst; }
        dl_decl_util & get_decl_util()  { return m_decl_util; }

        bool output_profile() const { return m_params.get_bool(":output-profile", false); } 
        bool fix_unbound_vars() const { return m_params.get_bool(":fix-unbound-vars", false); }
        symbol default_table() const { return m_params.get_sym(":default-table", symbol("sparse")); }
        symbol default_relation() const { return m_params.get_sym(":default-relation", external_relation_plugin::get_name()); }
        symbol default_table_checker() const { return m_params.get_sym(":default-table-checker", symbol("sparse")); }
        bool default_table_checked() const { return m_params.get_bool(":default-table-checked", false); }
        bool dbg_fpr_nonempty_relation_signature() const { return m_params.get_bool(":dbg-fpr-nonempty-relation-signatures", false); } 
        unsigned dl_profile_milliseconds_threshold() const { return m_params.get_uint(":profile-milliseconds-threshold", 0); }
        bool all_or_nothing_deltas() const { return m_params.get_bool(":all-or-nothing-deltas", false); }
        bool compile_with_widening() const { return m_params.get_bool(":compile-with-widening", false); }
        bool unbound_compressor() const { return m_params.get_bool(":unbound-compressor", true); }
        bool similarity_compressor() const { return m_params.get_bool(":similarity-compressor", true); }
        unsigned similarity_compressor_threshold() const { return m_params.get_uint(":similarity-compressor-threshold", 11); }
        unsigned soft_timeout() const { return m_fparams.m_soft_timeout; }
        unsigned initial_restart_timeout() const { return m_params.get_uint(":initial-restart-timeout", 0); } 
        bool generate_explanations() const { return m_params.get_bool(":generate-explanations", false); }
        bool explanations_on_relation_level() const { return m_params.get_bool(":explanations-on-relation-level", false); }
        bool magic_sets_for_queries() const { return m_params.get_bool(":magic-sets-for-queries", false); }
        bool eager_emptiness_checking() const { return m_params.get_bool(":eager-emptiness-checking", true); }

        void register_finite_sort(sort * s, sort_kind k);

        /**
           Register uninterpreted constant to be used as an implicitly quantified variable.
           The variable gets quantified in the formula passed to rule::mk_rule_from_horn.
        */

        void register_variable(func_decl* var);

        app_ref_vector const& get_variables() const { return m_vars; }

        /**
           Register datalog relation.

           If names is true, we associate the predicate with its name, so that it can be 
           retrieved by the try_get_predicate_decl() function. Auxiliary predicates introduced
           e.g. by rule transformations do not need to be named.
         */
        void register_predicate(func_decl * pred, bool named = true);

        bool is_predicate(func_decl * pred) const;
        
        /**
           \brief If a predicate name has a \c func_decl object assigned, return pointer to it;
           otherwise return 0.

           Not all \c func_decl object used as relation identifiers need to be assigned to their
           names. Generally, the names coming from the parses are registered here.
         */
        func_decl * try_get_predicate_decl(symbol pred_name) const;

        /**
           \brief Create a fresh head predicate declaration.

        */
        func_decl * mk_fresh_head_predicate(symbol const & prefix, symbol const & suffix, 
            unsigned arity, sort * const * domain, func_decl* orig_pred=0);


        /**
           \brief Return number of a symbol in a DK_SYMBOL kind sort (\see register_sort() )
         */
        finite_element get_constant_number(relation_sort sort, symbol s);
        /**
           \brief Return number of a symbol in a DK_UINT64 kind sort (\see register_sort() )
         */
        finite_element get_constant_number(relation_sort srt, uint64 el);

        /**
           \brief Output name of constant with number \c num in sort \c sort.
        */
        void print_constant_name(relation_sort sort, uint64 num, std::ostream & out);

        bool try_get_sort_constant_count(relation_sort srt, uint64 & constant_count);

        uint64 get_sort_size_estimate(relation_sort srt);

        /**
           \brief Assign names of variables used in the declaration of a predicate.

           These names are used when printing out the relations to make the output conform 
           to the one of bddbddb.
        */
        void set_argument_names(const func_decl * pred, svector<symbol> var_names);
        symbol get_argument_name(const func_decl * pred, unsigned arg_index);

        void set_predicate_representation(func_decl * pred, unsigned relation_name_cnt, 
            symbol * const relation_names);

        void set_output_predicate(func_decl * pred);
        bool is_output_predicate(func_decl * pred) { return m_output_preds.contains(pred); }
        const decl_set & get_output_predicates() const { return m_output_preds; }

        rule_set const & get_rules() { return m_rule_set; }

        void add_fact(app * head);
        void add_fact(func_decl * pred, const relation_fact & fact);

        
        void add_rule(rule_ref& r);
        void add_rules(rule_ref_vector& rs);
        
        void assert_expr(expr* e);
        expr_ref get_background_assertion();

        /**
           Method exposed from API for adding rules.
        */
        void add_rule(expr* rl, symbol const& name);
        

        /**
           Update a named rule.
         */
        void update_rule(expr* rl, symbol const& name);

        /**
           Retrieve the maximal number of relevant unfoldings of 'pred'
           with respect to the current state.
         */
        unsigned get_num_levels(func_decl* pred);

        /**
           Retrieve the current cover of 'pred' up to 'level' unfoldings.
           Return just the delta that is known at 'level'. To
           obtain the full set of properties of 'pred' one should query
           at 'level+1', 'level+2' etc, and include level=-1.
        */
        expr_ref get_cover_delta(int level, func_decl* pred);
       
        /**
           Add a property of predicate 'pred' at 'level'. 
           It gets pushed forward when possible.
         */
        void add_cover(int level, func_decl* pred, expr* property);

        /**
           \brief Check rule subsumption.
        */
        bool check_subsumes(rule const& stronger_rule, rule const& weaker_rule);

        /**
          \brief Check if rule is well-formed according to engine.
        */
        void check_rule(rule_ref& r);

        /**
           \brief Return true if facts to \c pred can be added using the \c add_table_fact() function.

           This function should return true if \c pred is represented by a table_relation
           and there is no transformation of relation values before they are put into the
           table.
         */
        bool can_add_table_fact(func_decl * pred);
        void add_table_fact(func_decl * pred, const table_fact & fact);
        void add_table_fact(func_decl * pred, unsigned num_args, unsigned args[]);

        /**
           \brief To be called after all rules are added.
        */
        void close();
        void ensure_closed();

        /**
           \brief Undo the effect of the \c close operation.
         */
        void reopen();
        void ensure_opened();

        void transform_rules(model_converter_ref& mc, proof_converter_ref& pc);
        void transform_rules(rule_transformer& trans, model_converter_ref& mc, proof_converter_ref& pc);
        void replace_rules(rule_set & rs);

        void apply_default_transformation(model_converter_ref& mc, proof_converter_ref& pc);

        void collect_params(param_descrs& r);
        
        void updt_params(params_ref const& p);

        void collect_predicates(decl_set & res);
        /**
           \brief Restrict the set of used predicates to \c res.

           The function deallocates unsused relations, it does not deal with rules.
         */
        void restrict_predicates(const decl_set & res);

        void display_rules(std::ostream & out) const {
            m_rule_set.display(out);
        }
        void display_facts(std::ostream & out) const {
            m_rmanager.display(out);
        }

        void display(std::ostream & out) const {
            display_rules(out);
            display_facts(out);
        }

        void display_smt2(unsigned num_queries, expr* const* queries, std::ostream& out);

        // -----------------------------------
        //
        // basic usage methods
        //
        // -----------------------------------

        void cancel();

        void cleanup();

        /**
           \brief check if query 'q' is satisfied under asserted rules and background.

           If successful, return OK and into \c result assign a relation with all 
           tuples matching the query. Otherwise return reason for failure and do not modify
           \c result.

           The numbers of variables in the query body must form a contiguous sequence
           starting from zero.

           The caller becomes an owner of the relation object returned in \c result. The
           relation object, however, should not outlive the datalog context since it is 
           linked to a relation plugin in the context.
         */

        lbool query(expr* q);

        /**
           Query multiple output relations.
        */
        lbool dl_query(unsigned num_rels, func_decl * const* rels);

        /**
           Reset tables that are under negation.
         */
        void reset_negated_tables();

        /**
           Just reset all tables.
        */
        void reset_tables(); 

        /**
           \brief retrieve last proof status.
        */
        execution_result get_status();

        /**
           \brief retrieve formula corresponding to query that returns l_true.
           The formula describes one or more instances of the existential variables
           in the query that are derivable.
        */
        expr* get_answer_as_formula();


        void collect_statistics(statistics& st);

        /**
           \brief Display a certificate for reachability and/or unreachability.
        */
        bool display_certificate(std::ostream& out);

        /**
           \brief query result if it contains fact.
         */
        bool result_contains_fact(relation_fact const& f);

        /**
           \brief display facts generated for query.
        */
        void display_output_facts(std::ostream & out) const {
            m_rmanager.display_output_tables(out);
        }

        /**
           \brief expose datalog saturation for test.
        */
        lbool dl_saturate();

    private:

        void ensure_pdr();

        void ensure_bmc();

        void new_query();

        lbool dl_query(expr* query);

        lbool pdr_query(expr* query);

        lbool bmc_query(expr* query);

        void check_quantifier_free(rule_ref& r);        
        void check_uninterpreted_free(rule_ref& r);
        void check_existential_tail(rule_ref& r);
        void check_positive_predicates(rule_ref& r);

        // auxilary functions for SMT2 pretty-printer.
        void declare_vars(expr_ref_vector& rules, mk_fresh_name& mk_fresh, std::ostream& out);

        //undefined and private copy constructor and operator=
        context(const context&);
        context& operator=(const context&);
    };

};

#endif /* _DL_CONTEXT_H_ */

