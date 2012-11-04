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

namespace datalog {

    class rule;
    class rule_manager;
    class table;
    class context;

    typedef obj_ref<rule, rule_manager> rule_ref;
    typedef ref_vector<rule, rule_manager> rule_ref_vector;
    typedef ptr_vector<rule> rule_vector;
    /**
       \brief Manager for the \c rule class

       \remark \c rule_manager objects are interchangable as long as they
         contain the same \c ast_manager object.
    */
    class rule_manager
    {
        ast_manager&        m;
        context&            m_ctx;
        var_counter         m_var_counter;
        obj_map<expr, app*> m_memoize_disj;
        expr_ref_vector     m_refs;

        // only the context can create a rule_manager
        friend class context;

        explicit rule_manager(context& ctx);

        /**
           \brief Move functions from predicate tails into the interpreted tail by introducing new variables.
        */
        void hoist_compound(unsigned& num_bound, app_ref& fml, app_ref_vector& body);

        void flatten_body(app_ref_vector& body);

        void remove_labels(expr_ref& fml);

        void eliminate_disjunctions(app_ref_vector::element_ref& body, rule_ref_vector& rules, symbol const& name);

        void eliminate_disjunctions(app_ref_vector& body, rule_ref_vector& rules, symbol const& name);        

        void eliminate_quantifier_body(app_ref_vector::element_ref& body, rule_ref_vector& rules, symbol const& name);

        void eliminate_quantifier_body(app_ref_vector& body, rule_ref_vector& rules, symbol const& name);

        app_ref ensure_app(expr* e);

        void check_app(expr* e);

        bool contains_predicate(expr* fml) const;

        void bind_variables(expr* fml, bool is_forall, expr_ref& result);

        void mk_rule_core(expr* fml, rule_ref_vector& rules, symbol const& name);

        unsigned hoist_quantifier(bool is_forall, expr_ref& fml, svector<symbol>* names);

        /**
           \brief Perform cheap quantifier elimination to reduce the number of variables in the interpreted tail.
         */
        void reduce_unbound_vars(rule_ref& r);

    public:

        ast_manager& get_manager() const { return m; }

        void inc_ref(rule * r);

        void dec_ref(rule * r);

        /**
           \brief Create a Datalog rule from a Horn formula.
           The formula is of the form (forall (...) (forall (...) (=> (and ...) head)))
           
        */
        void mk_rule(expr* fml, rule_ref_vector& rules, symbol const& name = symbol::null);

        /**
           \brief Create a Datalog query from an expression.
           The formula is of the form (exists (...) (exists (...) (and ...))
        */
        void mk_query(expr* query, func_decl_ref& query_pred, rule_ref_vector& query_rules, rule_ref& query_rule);

        /**
           \brief Create a Datalog rule head :- tail[0], ..., tail[n-1].
           Return 0 if it is not a valid rule.
           
           \remark A tail may contain negation. tail[i] is assumed to be negated if is_neg != 0 && is_neg[i] == true
        */
        rule * mk(app * head, unsigned n, app * const * tail, bool const * is_neg = 0, 
                         symbol const& name = symbol::null);

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


        bool is_predicate(func_decl * f) const;
        bool is_predicate(expr * e) const {
            return is_app(e) && is_predicate(to_app(e)->get_decl());
        }

        static bool is_forall(ast_manager& m, expr* e, quantifier*& q);

        var_counter& get_var_counter() { return m_var_counter; }

    };

    class rule : public accounted_object {
        friend class rule_manager;

        app *    m_head;
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
        Check whether predicate p is in the interpreted tail.
        
        If only_positive is true, only the positive predicate tail atoms are checked.
        */
        bool is_in_tail(const func_decl * p, bool only_positive=false) const;

        bool has_uninterpreted_non_predicates(func_decl*& f) const;
        void has_quantifiers(bool& existential, bool& universal) const;
        bool has_quantifiers() const;

        /**
           \brief Store in d the (direct) dependencies of the given rule.
        */

        void norm_vars(rule_manager & rm);

        void get_vars(sort_ref_vector& sorts) const;

        void to_formula(expr_ref& result) const;

        void display(context & ctx, std::ostream & out) const;

        std::ostream& display_smt2(ast_manager& m, std::ostream & out) const;

        symbol const& name() { return m_name; }

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

