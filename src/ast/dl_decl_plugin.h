/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    dl_decl_plugin.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2010-04-10

Revision History:

--*/
#ifndef DL_DECL_PLUGIN_H_
#define DL_DECL_PLUGIN_H_

#include"ast.h"
#include "arith_decl_plugin.h"
#include "bv_decl_plugin.h"

namespace datalog {


    enum dl_sort_kind {
        DL_RELATION_SORT,
        DL_FINITE_SORT,
        DL_RULE_SORT
    };

    enum dl_op_kind {
        OP_RA_STORE,
        OP_RA_EMPTY,
        OP_RA_IS_EMPTY,
        OP_RA_JOIN,
        OP_RA_UNION,
        OP_RA_WIDEN,
        OP_RA_PROJECT,
        OP_RA_FILTER,
        OP_RA_NEGATION_FILTER,
        OP_RA_RENAME,
        OP_RA_COMPLEMENT,
        OP_RA_SELECT,
        OP_RA_CLONE,
        OP_DL_CONSTANT,
        OP_DL_LT,
        OP_DL_REP,
        OP_DL_ABS,
        OP_DL_MIN,
        LAST_RA_OP
    };
    
    class dl_decl_plugin : public decl_plugin {
        symbol m_store_sym;
        symbol m_empty_sym;
        symbol m_is_empty_sym;
        symbol m_join_sym;
        symbol m_union_sym;
        symbol m_widen_sym;
        symbol m_project_sym;
        symbol m_filter_sym;
        symbol m_negation_filter_sym;
        symbol m_rename_sym;
        symbol m_complement_sym;
        symbol m_select_sym;
        symbol m_clone_sym;
        symbol m_num_sym;
        symbol m_lt_sym;
        symbol m_le_sym;
        symbol m_rule_sym;
        symbol m_min_sym;

        bool check_bounds(char const* msg, unsigned low, unsigned up, unsigned val) const;
        bool check_domain(unsigned low, unsigned up, unsigned val) const;
        bool check_params(unsigned low, unsigned up, unsigned val) const;

        bool is_rel_sort(sort* s);
        bool is_rel_sort(sort* s, ptr_vector<sort>& sorts);
        bool is_fin_sort(sort* r);

        func_decl * mk_store_select(decl_kind k, unsigned arity, sort * const * domain);
        func_decl * mk_empty(parameter const& p);
        func_decl * mk_is_empty(sort* r);
        func_decl * mk_join(unsigned num_params, parameter const* params, sort* r1, sort* r2);                        
        func_decl * mk_unionw(decl_kind k, sort* s1, sort* s2);
        func_decl * mk_project(unsigned num_params, parameter const * params, sort* r); 
        func_decl * mk_filter(parameter const& p, sort* r); 
        func_decl * mk_rename(unsigned num_params, parameter const * params, sort* r);
        func_decl * mk_complement(sort* r);
        func_decl * mk_negation_filter(unsigned num_params, parameter const* params, sort* r1, sort* r2);
        func_decl * mk_constant(parameter const* params);
        func_decl * mk_compare(decl_kind k, symbol const& sym, sort*const* domain);
        func_decl * mk_clone(sort* r);
        func_decl * mk_rule(unsigned arity);
        func_decl * mk_min(decl_kind k, unsigned num_parameters, parameter const * parameters);
                                
        sort * mk_finite_sort(unsigned num_params, parameter const* params);
        sort * mk_relation_sort(unsigned num_params, parameter const* params);
        sort * mk_rule_sort();

    public:
        /**
        Is \c decl a min aggregation function?
        */
        static bool is_aggregate(const func_decl* const decl)
        {
            return decl->get_decl_kind() == OP_DL_MIN;
        }

        /**
        \pre: is_aggregate(aggregate)

        \returns function declaration of predicate which is subject to min aggregation function
        */
        static func_decl * min_func_decl(const func_decl* const aggregate)
        {
            SASSERT(is_aggregate(aggregate));
            parameter const & relation_parameter = aggregate->get_parameter(0);
            return to_func_decl(relation_parameter.get_ast());
        }

        /**
        \pre: is_aggregate(aggregate)

        \returns column identifier (starting at zero) which is minimized by aggregation function
        */
        static unsigned min_col(const func_decl* const aggregate)
        {
            SASSERT(is_aggregate(aggregate));
            return (unsigned)aggregate->get_parameter(1).get_int();
        }

        /**
        \pre: is_aggregate(aggregate)

        \returns column identifiers for the "group by" in the given min aggregation function
        */
        static unsigned_vector group_by_cols(const func_decl* const aggregate)
        {
            SASSERT(is_aggregate(aggregate));
            unsigned _min_col = min_col(aggregate);
            if (aggregate->get_arity() == 0U)
                return unsigned_vector();

            unsigned col_num = 0;
            unsigned_vector cols(aggregate->get_arity() - 1U);
            for (unsigned i = 0; i < cols.size(); ++i, ++col_num)
            {
                if (col_num == _min_col)
                    ++col_num;

                cols[i] = col_num;
            }

            return cols;
        }

        dl_decl_plugin();
        virtual ~dl_decl_plugin() {}

        virtual decl_plugin * mk_fresh() { return alloc(dl_decl_plugin); }
        
        //
        // Contract for sort DL_RELATION_SORT 
        //   parameters[0]     - 1st dimension 
        //   ...
        //   parameters[n-1]   - nth dimension
        //
        // Contract for sort DL_FINITE_SORT
        //   parameters[0]     - name
        //   parameters[1]     - uint64
        //
        virtual sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters);
        
        //
        // Contract for func_decl:
        //   parameters[0]     - array sort
        // Contract for OP_DL_CONSTANT:
        //   parameters[0]     - rational containing uint64 with constant value
        //   parameters[1]     - a DL_FINITE_SORT sort of the constant
        // Contract for others:
        //   no parameters
        virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                         unsigned arity, sort * const * domain, sort * range);
        
        virtual void get_op_names(svector<builtin_name> & op_names, symbol const & logic);
        
        virtual void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic);

        virtual bool is_value(app * e) const { return is_app_of(e, m_family_id, OP_DL_CONSTANT); }
        virtual bool is_unique_value(app * e) const { return is_value(e); }

    };

    class dl_decl_util {
        /**
        Some plugins need to be registered in the ast_manager before we 
        create some of the member objects (the bv_util requires bv plugin 
        installed).
        
        Doing this in the constructor of the dl_decl_plugin object is too late (as
        member objects are created before we get into the constructor), so we 
        have this auxiliary object that is the first object of the context,
        so that it gets created first. It's only purpose is that in its 
        constructor the required plugins are added to the ast manager.
        */
        class ast_plugin_registrator {
        public:
            ast_plugin_registrator(ast_manager& m);
        };

        ast_plugin_registrator m_plugin_registrator;

        ast_manager& m;
        arith_util   m_arith;
        bv_util      m_bv;
        family_id    m_fid;

    public:
        dl_decl_util(ast_manager& m);
        // create a constant belonging to a given finite domain.
        // the options include the DL_FINITE_SORT, BV_SORT, and BOOL_SORT
        app* mk_numeral(uint64 value, sort* s);

        app* mk_lt(expr* a, expr* b);

        app* mk_le(expr* a, expr* b);

        bool is_lt(const expr* a) const { return is_app_of(a, m_fid, OP_DL_LT); }

        bool is_numeral(const expr* c) const { return is_app_of(c, m_fid, OP_DL_CONSTANT); }

        bool is_numeral(const expr* e, uint64& v) const;

        //
        // Utilities for extracting constants 
        // from bit-vectors and finite domains.
        // 
        bool is_numeral_ext(expr* c, uint64& v) const;

        bool is_numeral_ext(expr* c) const;        

        sort* mk_sort(const symbol& name, uint64  domain_size);

        bool try_get_size(const sort *, uint64& size) const;

        bool is_finite_sort(sort* s) const { 
            return is_sort_of(s, m_fid, DL_FINITE_SORT); 
        }

        bool is_finite_sort(expr* e) const { 
            return is_finite_sort(m.get_sort(e)); 
        }

        bool is_rule_sort(sort* s) const { 
            return is_sort_of(s, m_fid, DL_RULE_SORT); 
        }

        sort* mk_rule_sort();

        app* mk_rule(symbol const& name, unsigned num_args = 0, expr* const* args = 0);

        app* mk_fact(symbol const& name) { return mk_rule(name, 0, 0); }

        ast_manager& get_manager() const { return m; }

        family_id get_family_id() const { return m_fid; }

    };
    
};
#endif /* DL_DECL_PLUGIN_H_ */

