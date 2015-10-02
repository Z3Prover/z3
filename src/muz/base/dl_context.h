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
#ifndef DL_CONTEXT_H_
#define DL_CONTEXT_H_

#ifdef _CYGWIN
#undef min
#undef max
#endif
#include"arith_decl_plugin.h"
#include"map.h"
#include"th_rewriter.h"
#include"str_hashtable.h"
#include"var_subst.h"
#include"dl_costs.h"
#include"dl_decl_plugin.h"
#include"dl_rule_set.h"
#include"lbool.h"
#include"statistics.h"
#include"params.h"
#include"trail.h"
#include"model_converter.h"
#include"model2expr.h"
#include"smt_params.h"
#include"dl_rule_transformer.h"
#include"expr_functors.h"
#include"dl_engine_base.h"
#include"bind_variables.h"
#include"rule_properties.h"

struct fixedpoint_params;

namespace datalog {

    enum execution_result {
        OK,
        TIMEOUT,
        MEMOUT,
        INPUT_ERROR,
        APPROX,
	BOUNDED,
        CANCELED
    };

    class relation_manager;

    typedef sort * relation_sort;
    typedef uint64 table_element;
    typedef svector<table_element> table_fact;

    typedef app * relation_element;
    typedef app_ref relation_element_ref;

    class relation_fact : public app_ref_vector {
    public:
        class el_proxy {
            friend class relation_fact;

            relation_fact & m_parent;
            unsigned m_idx;

            el_proxy(relation_fact & parent, unsigned idx) : m_parent(parent), m_idx(idx) {}
        public:
            operator relation_element() const {
                return m_parent.get(m_idx);
            }
            relation_element operator->() const {
                return m_parent.get(m_idx);
            }
            relation_element operator=(const relation_element & val) const {
                m_parent.set(m_idx, val);
                return m_parent.get(m_idx);
            }
            relation_element operator=(const el_proxy & val) {
                m_parent.set(m_idx, val);
                return m_parent.get(m_idx);
            }
        };

        typedef const relation_element * iterator;

        relation_fact(ast_manager & m) : app_ref_vector(m) {}
        relation_fact(ast_manager & m, unsigned sz) : app_ref_vector(m) { resize(sz); }
        relation_fact(context & ctx);
        
        iterator begin() const { return c_ptr(); }
        iterator end() const { return c_ptr()+size(); }

        relation_element operator[](unsigned i) const { return get(i); }
        el_proxy operator[](unsigned i) { return el_proxy(*this, i); }
    };

    // attempt to modularize context code.
    class rel_context_base : public engine_base {
    public:
        rel_context_base(ast_manager& m, char const* name): engine_base(m, name) {}
        virtual ~rel_context_base() {}
        virtual relation_manager & get_rmanager() = 0;
        virtual const relation_manager & get_rmanager() const = 0;
        virtual relation_base & get_relation(func_decl * pred) = 0;
        virtual relation_base * try_get_relation(func_decl * pred) const = 0;
        virtual bool is_empty_relation(func_decl* pred) const = 0;
        virtual expr_ref try_get_formula(func_decl * pred) const = 0;
        virtual void display_output_facts(rule_set const& rules, std::ostream & out) const = 0;
        virtual void display_facts(std::ostream & out) const = 0;
        virtual void display_profile(std::ostream& out) = 0;
        virtual void restrict_predicates(func_decl_set const& predicates) = 0;
        virtual bool result_contains_fact(relation_fact const& f) = 0;
        virtual void add_fact(func_decl* pred, relation_fact const& fact) = 0;
        virtual void add_fact(func_decl* pred, table_fact const& fact) = 0;
        virtual bool has_facts(func_decl * pred) const = 0;
        virtual void store_relation(func_decl * pred, relation_base * rel) = 0;
        virtual void inherit_predicate_kind(func_decl* new_pred, func_decl* orig_pred) = 0;
        virtual void set_predicate_representation(func_decl * pred, unsigned relation_name_cnt, 
                                                  symbol const * relation_names) = 0;
        virtual bool output_profile() const = 0;
        virtual void collect_non_empty_predicates(func_decl_set& preds) = 0;
        virtual void transform_rules() = 0;
        virtual bool try_get_size(func_decl* pred, unsigned& rel_sz) const = 0;
        virtual lbool saturate() = 0;
    };

    class context {
    public:
        typedef unsigned finite_element;
        enum sort_kind {
            SK_UINT64,
            SK_SYMBOL
        };
        class contains_pred : public i_expr_pred {
            context const& ctx;
        public:
            contains_pred(context& ctx): ctx(ctx) {}
            virtual ~contains_pred() {}
            
            virtual bool operator()(expr* e) {
                return ctx.is_predicate(e);
            }
        };


    private:
        class sort_domain;
        class symbol_sort_domain;
        class uint64_sort_domain;
        class restore_rules;

        typedef hashtable<symbol, symbol_hash_proc, symbol_eq_proc> symbol_set;
        typedef map<symbol, func_decl*, symbol_hash_proc, symbol_eq_proc> sym2decl;
        typedef obj_map<const func_decl, svector<symbol> > pred2syms;
        typedef obj_map<const sort, sort_domain*> sort_domain_map;


        ast_manager &      m;
        register_engine_base& m_register_engine;
        smt_params &       m_fparams;
        params_ref         m_params_ref;
        fixedpoint_params*  m_params;
        bool               m_generate_proof_trace;      // cached configuration parameter
        bool               m_unbound_compressor;        // cached configuration parameter
        symbol             m_default_relation;          // cached configuration parameter
        dl_decl_util       m_decl_util;
        th_rewriter        m_rewriter;
        var_subst          m_var_subst;
        rule_manager       m_rule_manager;
        contains_pred      m_contains_p;
        rule_properties    m_rule_properties;
        rule_transformer   m_transf;
        trail_stack<context> m_trail;
        ast_ref_vector     m_pinned;
        bind_variables     m_bind_variables;
        sort_domain_map    m_sorts;
        func_decl_set      m_preds;
        sym2decl           m_preds_by_name;
        pred2syms          m_argument_var_names;
        rule_set           m_rule_set;
        rule_set           m_transformed_rule_set;
        expr_free_vars     m_free_vars;
        unsigned           m_rule_fmls_head;
        expr_ref_vector    m_rule_fmls;
        svector<symbol>    m_rule_names;
        vector<unsigned>   m_rule_bounds;
        expr_ref_vector    m_background;
        model_converter_ref m_mc;
        proof_converter_ref m_pc;

        rel_context_base*               m_rel;
        scoped_ptr<engine_base>         m_engine;

        bool               m_closed;
        bool               m_saturation_was_run;
        bool               m_enable_bind_variables;
        execution_result   m_last_status;
        expr_ref           m_last_answer;
        DL_ENGINE          m_engine_type;
        volatile bool      m_cancel;



        bool is_fact(app * head) const;
        bool has_sort_domain(relation_sort s) const;
        sort_domain & get_sort_domain(relation_sort s);
        const sort_domain & get_sort_domain(relation_sort s) const;

        class engine_type_proc;


    public:
        context(ast_manager & m, register_engine_base& re, smt_params& fp, params_ref const& p = params_ref());
        ~context();
        void reset();

        void push();
        void pop();
        
        bool saturation_was_run() const { return m_saturation_was_run; }
        void notify_saturation_was_run() { m_saturation_was_run = true; }

        void configure_engine();

        ast_manager & get_manager() const { return m; }
        rule_manager & get_rule_manager() { return m_rule_manager; }
        smt_params & get_fparams() const { return m_fparams; }
        fixedpoint_params const&  get_params() const { return *m_params; }
        DL_ENGINE get_engine() { configure_engine(); return m_engine_type; }
        register_engine_base& get_register_engine() { return m_register_engine; }
        th_rewriter& get_rewriter() { return m_rewriter; }
        var_subst & get_var_subst() { return m_var_subst; }
        dl_decl_util & get_decl_util()  { return m_decl_util; }

        bool generate_proof_trace() const;
        bool output_profile() const;
        bool output_tuples() const;
        bool use_map_names() const;
        bool fix_unbound_vars() const;
        symbol default_table() const;
        symbol default_relation() const;
        void set_default_relation(symbol const& s);
        symbol default_table_checker() const;        
        symbol check_relation() const;
        bool default_table_checked() const;
        bool dbg_fpr_nonempty_relation_signature() const;
        unsigned dl_profile_milliseconds_threshold() const;
        bool all_or_nothing_deltas() const;
        bool compile_with_widening() const;
        bool unbound_compressor() const;
        void set_unbound_compressor(bool f);
        bool similarity_compressor() const;
        symbol print_aig() const;
        symbol tab_selection() const;
        unsigned similarity_compressor_threshold() const;
        unsigned soft_timeout() const;
        unsigned initial_restart_timeout() const;
        bool generate_explanations() const;
        bool explanations_on_relation_level() const;
        bool magic_sets_for_queries() const;
        bool karr() const;
        bool scale() const;
        bool magic() const;
        bool quantify_arrays() const;
        bool instantiate_quantifiers() const;
        bool xform_bit_blast() const;        
        bool xform_slice() const;
        bool xform_coi() const;

        void register_finite_sort(sort * s, sort_kind k);

        /**
           Register uninterpreted constant to be used as an implicitly quantified variable.
           The variable gets quantified in the formula passed to rule::mk_rule_from_horn.
        */

        void register_variable(func_decl* var);

        /*
          Replace constants that have been registered as 
          variables by de-Bruijn indices and corresponding
          universal (if is_forall is true) or existential 
          quantifier.
         */
        expr_ref bind_vars(expr* fml, bool is_forall);

        bool& bind_vars_enabled() { return m_enable_bind_variables; }

        /**
           Register datalog relation.

           If named is true, we associate the predicate with its name, so that it can be 
           retrieved by the try_get_predicate_decl() function. Auxiliary predicates introduced
           e.g. by rule transformations do not need to be named.
         */
        void register_predicate(func_decl * pred, bool named);

        /**
           Restrict reltaions to set of predicates.
         */
        void restrict_predicates(func_decl_set const& preds);

        /**
           \brief Retrieve predicates
        */
        func_decl_set const& get_predicates() const { return m_preds; }
	ast_ref_vector const &get_pinned() const {return m_pinned; }

        bool is_predicate(func_decl* pred) const { return m_preds.contains(pred); }
        bool is_predicate(expr * e) const { return is_app(e) && is_predicate(to_app(e)->get_decl()); }

        /**
           \brief If a predicate name has a \c func_decl object assigned, return pointer to it;
           otherwise return 0.
           
           Not all \c func_decl object used as relation identifiers need to be assigned to their
           names. Generally, the names coming from the parses are registered here.
        */
        func_decl * try_get_predicate_decl(symbol const& pred_name) const {
            func_decl * res = 0;
            m_preds_by_name.find(pred_name, res);
            return res;
        }        

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
            symbol const *  relation_names);

        void set_output_predicate(func_decl * pred) { m_rule_set.set_output_predicate(pred); }

        rule_set & get_rules() { flush_add_rules(); return m_rule_set; }

        void get_rules_as_formulas(expr_ref_vector& fmls, expr_ref_vector& qs, svector<symbol>& names);
        void get_raw_rule_formulas(expr_ref_vector& fmls, svector<symbol>& names, vector<unsigned> &bounds);

        void add_fact(app * head);
        void add_fact(func_decl * pred, const relation_fact & fact);

        bool has_facts(func_decl * pred) const;
        
        void add_rule(rule_ref& r);
        
        void assert_expr(expr* e);
        expr_ref get_background_assertion();
        unsigned get_num_assertions() { return m_background.size(); }
        expr*    get_assertion(unsigned i) const { return m_background[i]; }

        /**
           Method exposed from API for adding rules.
        */
        void add_rule(expr* rl, symbol const& name, unsigned bound = UINT_MAX);
        

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
        void check_rules(rule_set& r);

        /**
           \brief Return true if facts to \c pred can be added using the \c add_table_fact() function.

           This function should return true if \c pred is represented by a table_relation
           and there is no transformation of relation values before they are put into the
           table.
         */
        void add_table_fact(func_decl * pred, const table_fact & fact);
        void add_table_fact(func_decl * pred, unsigned num_args, unsigned args[]);

        /**
           \brief To be called after all rules are added.
        */
        void close();
        void ensure_closed();
        bool is_closed() { return m_closed; }

        /**
           \brief Undo the effect of the \c close operation.
         */
        void reopen();
        void ensure_opened();

        model_converter_ref& get_model_converter() { return m_mc; }
        void add_model_converter(model_converter* mc) { m_mc = concat(m_mc.get(), mc); }
        proof_converter_ref& get_proof_converter() { return m_pc; }
        void add_proof_converter(proof_converter* pc) { m_pc = concat(m_pc.get(), pc); }

        void transform_rules(rule_transformer& transf); 
        void transform_rules(rule_transformer::plugin* plugin);
        void replace_rules(rule_set const& rs);
        void record_transformed_rules();

        void apply_default_transformation(); 

        void collect_params(param_descrs& r);
        
        void updt_params(params_ref const& p);

        void display_rules(std::ostream & out) const {
            m_rule_set.display(out);
        }

        void display(std::ostream & out) const;

        void display_smt2(unsigned num_queries, expr* const* qs, std::ostream& out);

        void display_profile(std::ostream& out) const;

        // -----------------------------------
        //
        // basic usage methods
        //
        // -----------------------------------

        void cancel();
        bool canceled() const { return m_cancel; }

        void cleanup();
        void reset_cancel() { cleanup(); }

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
           \brief retrieve model from inductive invariant that shows query is unsat.
           
           \pre engine == 'pdr' || engine == 'duality' - this option is only supported
           for PDR mode and Duality mode.
         */
        model_ref get_model();

        /**
           \brief retrieve proof from derivation of the query.
           
           \pre engine == 'pdr'  || engine == 'duality'- this option is only supported
	   for PDR mode and Duality mode.
         */
        proof_ref get_proof();


        /**
           Query multiple output relations.
        */
        lbool rel_query(unsigned num_rels, func_decl * const* rels);


        /**
           \brief retrieve last proof status.
        */
        execution_result get_status();

        void set_status(execution_result r) { m_last_status = r; }

        /**
           \brief retrieve formula corresponding to query that returns l_true.
           The formula describes one or more instances of the existential variables
           in the query that are derivable.
        */
        expr* get_answer_as_formula();


        void collect_statistics(statistics& st) const;

        void reset_statistics();

        /**
           \brief Display a certificate for reachability and/or unreachability.
        */
        void display_certificate(std::ostream& out);

        /**
           \brief query result if it contains fact.
         */
        bool result_contains_fact(relation_fact const& f);

        rel_context_base* get_rel_context() { ensure_engine(); return m_rel; }

    private:

        /**
           Just reset all tables.
        */
        void reset_tables(); 


        void flush_add_rules();

        void ensure_engine();

        // auxilary functions for SMT2 pretty-printer.
        void declare_vars(expr_ref_vector& rules, mk_fresh_name& mk_fresh, std::ostream& out);

        //undefined and private copy constructor and operator=
        context(const context&);
        context& operator=(const context&);
    };

};

#endif /* DL_CONTEXT_H_ */

