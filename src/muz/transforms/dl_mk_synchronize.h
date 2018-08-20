/*++
Copyright (c) 2017-2018 Saint-Petersburg State University

Module Name:

    dl_mk_synchronize.h

Abstract:

    Rule transformer that attempts to merge recursive iterations
    relaxing the shape of the inductive invariant.

Example:

    Q(z)  :- A(x), B(y), phi1(x,y,z).
    A(x)  :- A(x'), phi2(x,x').
    A(x)  :- phi3(x).
    B(y)  :- C(y'), phi4(y,y').
    C(y)  :- B(y'), phi5(y,y').
    B(y)  :- phi6(y).

    Transformed clauses:

    Q(z)    :- AB(x,y), phi1(x,y,z).
    AB(x,y) :- AC(x',y'), phi2(x,x'), phi4(y,y').
    AC(x,y) :- AB(x',y'), phi2(x,x'), phi5(y,y').
    AB(x,y) :- AC(x, y'), phi3(x), phi4(y,y').
    AC(x,y) :- AB(x, y'), phi3(x), phi5(y,y').
    AB(x,y) :- AB(x',y), phi2(x,x'), phi6(y).
    AB(x,y) :- phi3(x), phi6(y).

Author:

    Dmitry Mordvinov (dvvrd) 2017-05-24
    Lidiia Chernigovskaia (LChernigovskaya) 2017-10-20

Revision History:

--*/
#ifndef DL_MK_SYNCHRONIZE_H_
#define DL_MK_SYNCHRONIZE_H_

#include"muz/base/dl_context.h"
#include"muz/base/dl_rule_set.h"
#include"util/uint_set.h"
#include"muz/base/dl_rule_transformer.h"
#include"muz/transforms/dl_mk_rule_inliner.h"

namespace datalog {

    /**
       \brief Implements a synchronous product transformation.
    */
    class mk_synchronize : public rule_transformer::plugin {
    public:
        typedef ptr_vector<rule_stratifier::item_set> item_set_vector;
    private:
        context&        m_ctx;
        ast_manager&    m;
        rule_manager&   rm;

        scoped_ptr<rule_dependencies> m_deps;
        scoped_ptr<rule_stratifier> m_stratifier;

        // symbol table that maps new predicate names to corresponding
        // func_decl
        map<symbol, func_decl*, symbol_hash_proc, symbol_eq_proc> m_cache;

        /// returns true if decl is recursive in the given rule
        /// requires that decl appears in the tail of r
        bool is_recursive(rule &r, func_decl &decl) const;
        bool is_recursive(rule &r, expr &e) const {
            SASSERT(is_app(&e));
            return is_app(&e) && is_recursive(r, *to_app(&e)->get_decl());
        }

        /// returns true if the top-level predicate of app is recursive
        bool has_recursive_premise(app * app) const;

        item_set_vector add_merged_decls(ptr_vector<app> & apps);

        /**
            Compute Cartesian product of decls and create a new
            predicate for each element. For example, if decls is

            ( (a, b), (c, d) ) )

            create new predicates: a!!c, a!!d, b!!c, and b!!d
        */
        void add_new_rel_symbols(unsigned idx, item_set_vector const & decls,
                                 ptr_vector<func_decl> & buf, bool & was_added);

        /**
           Convert vector of predicate apps into a single app. For example,
           (Foo a) (Bar b) becomes (Foo!!Bar a b)
         */
        app_ref product_application(ptr_vector<app> const & apps);

        /**
            Replace a given rule by a rule in which conjunction of
            predicates is replaced by a single product predicate
         */
        void replace_applications(rule & r, rule_set & rules,
                                  ptr_vector<app> & apps);

        rule_ref rename_bound_vars_in_rule(rule * r, unsigned & var_idx);
        vector<rule_ref_vector> rename_bound_vars(item_set_vector const & heads,
                                                  rule_set & rules);

        void add_rec_tail(vector< ptr_vector<app> > & recursive_calls,
                          app_ref_vector & new_tail,
                          svector<bool> & new_tail_neg, unsigned & tail_idx);
        void add_non_rec_tail(rule & r, app_ref_vector & new_tail,
                              svector<bool> & new_tail_neg,
                              unsigned & tail_idx);

        rule_ref product_rule(rule_ref_vector const & rules);

        void merge_rules(unsigned idx, rule_ref_vector & buf,
            vector<rule_ref_vector> const & merged_rules, rule_set & all_rules);
        void merge_applications(rule & r, rule_set & rules);

    public:
        /**
           \brief Create synchronous product transformer.
         */
        mk_synchronize(context & ctx, unsigned priority = 22500);

        rule_set * operator()(rule_set const & source);
    };

};

#endif /* DL_MK_SYNCHRONIZE_H_ */
