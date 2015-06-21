/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_rule.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-17.

Revision History:

--*/

#ifndef _DL_RULE_H_
#define _DL_RULE_H_

#include"ast.h"
#include"dl_costs.h"
#include"dl_util.h"
#include"used_vars.h"
#include"proof_converter.h"
#include"model_converter.h"
#include"ast_counter.h"
#include"rewriter.h"
#include"hnf.h"
#include"qe_lite.h"
#include"var_subst.h"
#include"datatype_decl_plugin.h"

namespace datalog {

    class rule;
    class rule_manager;
    class rule_set;
    class table;
    class context;

    typedef obj_ref<rule, rule_manager> rule_ref;
    typedef ref_vector<rule, rule_manager> rule_ref_vector;
    typedef ptr_vector<rule> rule_vector;


    struct uninterpreted_function_finder_proc {
        ast_manager& m;
        datatype_util m_dt;
        dl_decl_util  m_dl;
        bool m_found;
        func_decl* m_func;
        uninterpreted_function_finder_proc(ast_manager& m): 
            m(m), m_dt(m), m_dl(m), m_found(false), m_func(0) {}
        void operator()(var * n) { }
        void operator()(quantifier * n) { }
        void operator()(app * n) {
            if (is_uninterp(n) && !m_dl.is_rule_sort(n->get_decl()->get_range())) {
                m_found = true;
                m_func = n->get_decl();
            }
            else if (m_dt.is_accessor(n)) {
                sort* s = m.get_sort(n->get_arg(0));
                SASSERT(m_dt.is_datatype(s));
                if (m_dt.get_datatype_constructors(s)->size() > 1) {
                    m_found = true;
                    m_func = n->get_decl();
                }
            }
        }
        void reset() { m_found = false; m_func = 0; }

        bool found(func_decl*& f) const { f = m_func; return m_found; }
    };

    struct quantifier_finder_proc {
        bool m_exist;
        bool m_univ;
        quantifier_finder_proc() : m_exist(false), m_univ(false) {}
        void operator()(var * n) { }
        void operator()(quantifier * n) {
            if (n->is_forall()) {
                m_univ = true;
            }
            else {
                SASSERT(n->is_exists());
                m_exist = true;
            }
        }
        void operator()(app * n) { }
        void reset() { m_exist = m_univ = false; }
    };


    /**
       \brief Manager for the \c rule class

       \remark \c rule_manager objects are interchangable as long as they
         contain the same \c ast_manager object.
    */
    class rule_manager
    {
        class remove_label_cfg : public default_rewriter_cfg {
            family_id m_label_fid;
        public:        
            remove_label_cfg(ast_manager& m): m_label_fid(m.get_label_family_id()) {}
            virtual ~remove_label_cfg();
            
            br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, 
                                 proof_ref & result_pr);
        };
    
        ast_manager&         m;
        context&             m_ctx;
        rule_counter         m_counter;
        used_vars            m_used;
        var_idx_set          m_var_idx;
        expr_free_vars       m_free_vars;
        app_ref_vector       m_body;
        app_ref              m_head;
        expr_ref_vector      m_args;
        svector<bool>        m_neg;
        hnf                  m_hnf;
        qe_lite              m_qe;
        remove_label_cfg               m_cfg;
        rewriter_tpl<remove_label_cfg> m_rwr;
        mutable uninterpreted_function_finder_proc m_ufproc;
        mutable quantifier_finder_proc m_qproc;
        mutable expr_sparse_mark       m_visited;


        // only the context can create a rule_manager
        friend class context;

        explicit rule_manager(context& ctx);

        /**
           \brief Move functions from predicate tails into the interpreted tail by introducing new variables.
        */
        void hoist_compound_predicates(unsigned num_bound, app_ref& head, app_ref_vector& body);

        void hoist_compound(unsigned& num_bound, app_ref& fml, app_ref_vector& body);

        void flatten_body(app_ref_vector& body);

        void remove_labels(expr_ref& fml, proof_ref& pr);

        app_ref ensure_app(expr* e);

        void check_app(expr* e);

        bool contains_predicate(expr* fml) const;

        void bind_variables(expr* fml, bool is_forall, expr_ref& result);

        void mk_negations(app_ref_vector& body, svector<bool>& is_negated);

        void mk_rule_core(expr* fml, proof* p, rule_set& rules, symbol const& name);

        void mk_horn_rule(expr* fml, proof* p, rule_set& rules, symbol const& name);

        static expr_ref mk_implies(app_ref_vector const& body, expr* head);

        unsigned extract_horn(expr* fml, app_ref_vector& body, app_ref& head);

        /**
           \brief Perform cheap quantifier elimination to reduce the number of variables in the interpreted tail.
         */
        void reduce_unbound_vars(rule_ref& r);

        void reset_collect_vars();

        var_idx_set& finalize_collect_vars();

    public:

        ast_manager& get_manager() const { return m; }

        void inc_ref(rule * r);

        void dec_ref(rule * r);

        used_vars& reset_used() { m_used.reset(); return m_used; }

        var_idx_set& collect_vars(expr * pred);

        var_idx_set& collect_vars(expr * e1, expr* e2);

        var_idx_set& collect_rule_vars(rule * r);

        var_idx_set& collect_rule_vars_ex(rule * r, app* t);

        var_idx_set& collect_tail_vars(rule * r);

        void accumulate_vars(expr* pred);

        // ptr_vector<sort>& get_var_sorts() { return m_vars; }

        var_idx_set&      get_var_idx() { return m_var_idx; }

        /**
           \brief Create a Datalog rule from a Horn formula.
           The formula is of the form (forall (...) (forall (...) (=> (and ...) head)))
           
        */
        void mk_rule(expr* fml, proof* p, rule_set& rules, symbol const& name = symbol::null);

        /**
           \brief Create a Datalog query from an expression.
           The formula is of the form (exists (...) (exists (...) (and ...))
        */
        func_decl* mk_query(expr* query, rule_set& rules);

        /**
           \brief Create a Datalog rule head :- tail[0], ..., tail[n-1].
           Return 0 if it is not a valid rule.
           
           \remark A tail may contain negation. tail[i] is assumed to be negated if is_neg != 0 && is_neg[i] == true
        */
        rule * mk(app * head, unsigned n, app * const * tail, bool const * is_neg = 0, 
                  symbol const& name = symbol::null, bool normalize = true);

        /**
           \brief Create a rule with the same tail as \c source and with a specified head.
        */
        rule * mk(rule const * source, app * new_head, symbol const& name = symbol::null);

        /**
           \brief Create a copy of the given rule.
        */
        rule * mk(rule const * source, symbol const& name = symbol::null);

        /** make sure there are not non-quantified variables that occur only in interpreted predicates */
        void fix_unbound_vars(rule_ref& r, bool try_quantifier_elimination);

        /**
           \brief add proof that new rule is obtained by rewriting old rule.
         */
        void mk_rule_rewrite_proof(rule& old_rule, rule& new_rule);

        /**
           \brief tag rule as asserted.
         */
        void mk_rule_asserted_proof(rule& r);

        /**
           \brief apply substitution to variables of rule.
        */
        void substitute(rule_ref& r, unsigned sz, expr*const* es);

        /**
            \brief Check that head :- tail[0], ..., tail[n-1]
            is a valid Datalog rule.
         */
        void check_valid_rule(app * head, unsigned n, app * const * tail) const;

        /**
            \brief Check that \c head may occur as a Datalog rule head.
        */
        void check_valid_head(expr * head) const;

        /**
            \brief Return true if \c head may occur as a fact.
        */
        bool is_fact(app * head) const;

        static bool is_forall(ast_manager& m, expr* e, quantifier*& q);

        rule_counter& get_counter() { return m_counter; }

        void to_formula(rule const& r, expr_ref& result);

        std::ostream& display_smt2(rule const& r, std::ostream & out);

        bool has_uninterpreted_non_predicates(rule const& r, func_decl*& f) const;
        void has_quantifiers(rule const& r, bool& existential, bool& universal) const;
        bool has_quantifiers(rule const& r) const;

    };

    class rule : public accounted_object {
        friend class rule_manager;

        app *    m_head;
        proof*   m_proof;
        unsigned m_tail_size:20;
        // unsigned m_reserve:12;
        unsigned m_ref_cnt;
        unsigned m_positive_cnt;
        unsigned m_uninterp_cnt;
        symbol   m_name;
        /**
           The following field is an array of tagged pointers. 
           - Tag 0: the atom is not negated
           - Tag 1: the atom is negated.

           The order of tail formulas is the following:

           uninterpreted positive,
           uninterpreted negative,
           interpreted.

           The negated flag is never set for interpreted tails.
        */
        app *   m_tail[0]; 
        
        static unsigned get_obj_size(unsigned n) { return sizeof(rule) + n * sizeof(app *); }

        rule() : m_ref_cnt(0) {}
        ~rule() {}

        void deallocate(ast_manager & m);

        void get_used_vars(used_vars& uv) const;
        
    public:

        proof * get_proof() const { return m_proof; }

        void set_proof(ast_manager& m, proof* p);
        
        app * get_head() const { return m_head; }

        func_decl* get_decl() const { return get_head()->get_decl(); }

        unsigned get_tail_size() const { return m_tail_size; }

        /**
           \brief Return number of positive uninterpreted predicates in the tail.

           These predicates are the first in the tail.
        */
        unsigned get_positive_tail_size() const { return m_positive_cnt; }
        unsigned get_uninterpreted_tail_size() const { return m_uninterp_cnt; }

        /**
           \brief Return i-th tail atom. The first \c get_uninterpreted_tail_size() 
             atoms are uninterpreted and the first \c get_positive_tail_size() are 
             uninterpreted and non-negated.
        */
        app * get_tail(unsigned i) const { SASSERT(i < m_tail_size); return UNTAG(app *, m_tail[i]); }

        func_decl* get_decl(unsigned i) const { SASSERT(i < get_uninterpreted_tail_size()); return get_tail(i)->get_decl(); }

        bool is_neg_tail(unsigned i) const { SASSERT(i < m_tail_size); return GET_TAG(m_tail[i]) == 1; }

        /**
           A predicate P(Xj) can be annotated by adding an interpreted predicate of the form ((_ min P N) ...)
           where N is the column number that should be used for the min aggregation function.
           Such an interpreted predicate is an example for which this function returns true.
        */
        bool is_min_tail(unsigned i) const { return dl_decl_plugin::is_aggregate(get_tail(i)->get_decl()); }

        /**
        Check whether predicate p is in the interpreted tail.
        
        If only_positive is true, only the positive predicate tail atoms are checked.
        */
        bool is_in_tail(const func_decl * p, bool only_positive=false) const;

        bool has_negation() const;

        /**
           \brief Store in d the (direct) dependencies of the given rule.
        */

        void norm_vars(rule_manager & rm);

        void get_vars(ast_manager& m, ptr_vector<sort>& sorts) const;

        void display(context & ctx, std::ostream & out) const;

        symbol const& name() const { return m_name; }

        unsigned hash() const;

    };

    struct rule_eq_proc { 
        bool operator()(const rule * r1, const rule * r2) const;
    };
    struct rule_hash_proc {
        unsigned operator()(const rule * r) const;
    };

};

#endif /* _DL_RULE_H_ */

