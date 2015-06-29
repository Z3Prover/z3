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
#include<sstream>

#include "ast_pp.h"
#include "array_decl_plugin.h"
#include "datatype_decl_plugin.h"
#include "dl_decl_plugin.h"
#include "warning.h"
#include "reg_decl_plugins.h"

namespace datalog {

    dl_decl_plugin::dl_decl_plugin() :
        m_store_sym("store"),
        m_empty_sym("empty"),
        m_is_empty_sym("is_empty"),
        m_join_sym("join"),
        m_union_sym("union"),
        m_widen_sym("widen"),
        m_project_sym("project"),
        m_filter_sym("filter"),
        m_negation_filter_sym("negation_filter"),
        m_rename_sym("rename"),
        m_complement_sym("complement"),
        m_select_sym("select"),
        m_clone_sym("clone"),
        m_num_sym("N"),
        m_lt_sym("<"),
        m_le_sym("<="),
        m_rule_sym("R"),
        m_min_sym("min")
    {
    }

    bool dl_decl_plugin::check_bounds(char const* msg, unsigned low, unsigned up, unsigned val) const {
        if (low <= val && val <= up) {
            return true;
        }
        std::ostringstream buffer;
        buffer << msg << ", value is not within bound " << low << " <= " << val << " <= " << up;
        m_manager->raise_exception(buffer.str().c_str());
        return false;
    }

    bool dl_decl_plugin::check_domain(unsigned low, unsigned up, unsigned val) const {
        return check_bounds("unexpected number of arguments", low, up, val);
    }

    bool dl_decl_plugin::check_params(unsigned low, unsigned up, unsigned val) const {
        return check_bounds("unexpected number of parameters", low, up, val);
    }

    sort * dl_decl_plugin::mk_relation_sort( unsigned num_parameters, parameter const * parameters) {
                bool is_finite = true;
        rational r(1);
        for (unsigned i = 0; is_finite && i < num_parameters; ++i) {
            if (!parameters[i].is_ast() || !is_sort(parameters[i].get_ast())) {
                m_manager->raise_exception("expecting sort parameters");
                return 0;
            }
            sort* s = to_sort(parameters[i].get_ast());
            sort_size sz1 = s->get_num_elements();
            if (sz1.is_finite()) {
                r *= rational(sz1.size(),rational::ui64());
            }
            else {
                is_finite = false;
            }
        }
        sort_size sz;
        if (is_finite && r.is_uint64()) {
            sz = sort_size::mk_finite(r.get_uint64());
        }
        else {
            sz = sort_size::mk_very_big();
        }
        sort_info info(m_family_id, DL_RELATION_SORT, sz, num_parameters, parameters);
        return m_manager->mk_sort(symbol("Table"),info);
    }

    sort * dl_decl_plugin::mk_finite_sort(unsigned num_params, parameter const* params) {
        if (num_params != 2) {
            m_manager->raise_exception("expecting two parameters");
            return 0;
        }
        if (!params[0].is_symbol()) {
            m_manager->raise_exception("expecting symbol");
            return 0;
        }

        if (!params[1].is_rational() || !params[1].get_rational().is_uint64()) {
            m_manager->raise_exception("expecting rational");
            return 0;
        }
        sort_size sz = sort_size::mk_finite(params[1].get_rational().get_uint64());
        sort_info info(m_family_id, DL_FINITE_SORT, sz, num_params, params);
        return m_manager->mk_sort(params[0].get_symbol(),info);
    }

    sort* dl_decl_plugin::mk_rule_sort() {
        sort_size sz(sort_size::mk_infinite());
        sort_info info(m_family_id, DL_RULE_SORT, sz, 0, 0);
        return m_manager->mk_sort(m_rule_sym, info);
    }

    sort * dl_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
        switch(k) {
        case DL_RELATION_SORT:
            return mk_relation_sort(num_parameters, parameters);
        case DL_FINITE_SORT:
            return mk_finite_sort(num_parameters, parameters);
        case DL_RULE_SORT:
            return mk_rule_sort();
        default:
            UNREACHABLE();
        }
        return 0;
    }

    bool dl_decl_plugin::is_rel_sort(sort* r) {
        ptr_vector<sort> sorts;
        return is_rel_sort(r, sorts);
    }

    bool dl_decl_plugin::is_rel_sort(sort* r, ptr_vector<sort>& sorts) {
        if (!is_sort_of(r, m_family_id, DL_RELATION_SORT)) {
            m_manager->raise_exception("expected relation sort");
            return false;
        }
        unsigned n = r->get_num_parameters();
        for (unsigned i = 0; i < n; ++i) {
            parameter const& p = r->get_parameter(i);
            if (!p.is_ast() || !is_sort(p.get_ast())) {
                m_manager->raise_exception("exptected sort parameter");
                return false;
            }
            sorts.push_back(to_sort(p.get_ast()));
        }
        return true;
    }

    bool dl_decl_plugin::is_fin_sort(sort* r) {
        if (!is_sort_of(r, m_family_id, DL_FINITE_SORT)) {
            m_manager->raise_exception("expected finite sort");
            return false;
        }
        return true;
    }

    func_decl* dl_decl_plugin::mk_store_select(decl_kind k, unsigned arity, sort* const* domain) {
        bool is_store = (k == OP_RA_STORE);
        ast_manager& m = *m_manager;
        symbol sym = is_store?m_store_sym:m_select_sym;
        sort * r = domain[0];
        if (!is_store) {
            r = m.mk_bool_sort();
        }
        ptr_vector<sort> sorts;
        if (!is_rel_sort(r, sorts)) {
            return 0;
        }
        if (sorts.size() + 1 != arity) {
            m_manager->raise_exception("wrong arity supplied to relational access");
            return 0;
        }
        for (unsigned i = 0; i < sorts.size(); ++i) {
            if (sorts[i] != domain[i+1]) {
                IF_VERBOSE(0,
                           verbose_stream() << "Domain: " << mk_pp(domain[0], m) << "\n" <<
                           mk_pp(sorts[i], m) << "\n" <<
                           mk_pp(domain[i+1], m) << "\n";);
                m_manager->raise_exception("sort miss-match for relational access");
                return 0;
            }
        }
        func_decl_info info(m_family_id, k, 0, 0);            
        return m.mk_func_decl(sym, arity, domain, r, info); 
    }

    func_decl * dl_decl_plugin::mk_empty(parameter const& p) {
        ast_manager& m = *m_manager;
        if (!p.is_ast() || !is_sort(p.get_ast())) {
            m_manager->raise_exception("expected sort parameter");
            return 0;
        }
        sort* r = to_sort(p.get_ast());
        if (!is_rel_sort(r)) {                
            return 0;
        }
        func_decl_info info(m_family_id, OP_RA_EMPTY, 1, &p);
        return m.mk_func_decl(m_empty_sym, 0, (sort*const*)0, r, info);
    }

    func_decl* dl_decl_plugin::mk_project(unsigned num_params, parameter const* params, sort* r) {
        ast_manager& m = *m_manager;
        ptr_vector<sort> sorts;
        vector<parameter> ps;
        TRACE("dl_decl_plugin", 
                tout << mk_pp(r, m) << " ";
                for (unsigned i = 0; i < num_params; ++i) {
                    tout << params[i] << " ";
                }
                tout << "\n";
                );
        if (!is_rel_sort(r, sorts)) {
            return 0;
        }
        SASSERT(sorts.size() >= num_params);
        // populate ps
        unsigned j = 0, i = 0;
        for (; i < num_params; ++i) {
            if (!params[i].is_int()) {
                m_manager->raise_exception("expecting integer parameter");
                return 0;
            }
            unsigned k = params[i].get_int();
            if (j > k) {
                m_manager->raise_exception("arguments to projection should be increasing");
                return 0;
            }
            while (j < k) {
                ps.push_back(parameter(sorts[j]));
                ++j;
            }
            ++j;
        }
        for (; j < sorts.size(); ++j) {
            ps.push_back(parameter(sorts[j]));
        }
        SASSERT(ps.size() + num_params == sorts.size());
        sort* r2 = m.mk_sort(m_family_id, DL_RELATION_SORT, ps.size(), ps.c_ptr());        
        func_decl_info info(m_family_id, OP_RA_PROJECT, num_params, params);            
        return m.mk_func_decl(m_project_sym, 1, &r, r2, info);
    }

    func_decl * dl_decl_plugin::mk_unionw(decl_kind k, sort* s1, sort* s2) {
        ast_manager& m = *m_manager;
        if (s1 != s2) {
            m_manager->raise_exception("sort miss-match for arguments to union");
            return 0;
        }
        if (!is_rel_sort(s1)) {                
            return 0;
        }
        sort* domain[2] = { s1, s2 };
        func_decl_info info(m_family_id, k, 0, 0);            
        return m.mk_func_decl(m_union_sym, 2, domain, s1, info);
    }

    func_decl * dl_decl_plugin::mk_filter(parameter const& p, sort* r) {
        ast_manager& m = *m_manager;
        ptr_vector<sort> sorts;
        if (!is_rel_sort(r, sorts)) {
            return 0;
        }
        if (!p.is_ast() || !is_expr(p.get_ast())) {
            m_manager->raise_exception("ast expression expected to filter");
        }
        expr* f = to_expr(p.get_ast());
        // 1. f is of Boolean type.
        // 2. the free variables in f correspond to column types of r.
        if (!m.is_bool(f)) {
            m_manager->raise_exception("filter predicate should be of Boolean type");
            return 0;
        }
        ptr_vector<expr> todo;
        todo.push_back(f);
        ast_mark mark;
        while (!todo.empty()) {
            expr* e = todo.back();
            todo.pop_back();
            if (mark.is_marked(e)) {
                continue;
            }
            mark.mark(e, true);
            unsigned idx;
            switch(e->get_kind()) {
            case AST_VAR: 
                idx = to_var(e)->get_idx();
                if (idx >= sorts.size()) {
                    m_manager->raise_exception("illegal index");
                    return 0;
                }
                if (sorts[idx] != m.get_sort(e)) {
                    m_manager->raise_exception("sort miss-match in filter");
                    return 0;
                }
                break;
            case AST_APP:
                for (unsigned i = 0; i < to_app(e)->get_num_args(); ++i) {
                    todo.push_back(to_app(e)->get_arg(i));
                }
                break;
            case AST_QUANTIFIER:
                m_manager->raise_exception("quantifiers are not allowed in filter expressions");
                return 0;
            default:
                m_manager->raise_exception("unexpected filter expression kind");
                return 0;
            }
        }
        func_decl_info info(m_family_id, OP_RA_FILTER, 1, &p);            
        return m.mk_func_decl(m_filter_sym, 1, &r, r, info);
    }

    func_decl * dl_decl_plugin::mk_rename(unsigned num_params, parameter const* params, sort* r) {
        ptr_vector<sort> sorts;
        if (!is_rel_sort(r, sorts)) {
            return 0;
        }
        unsigned index0;
        sort* last_sort = 0;
        SASSERT(num_params > 0);
        for (unsigned i = 0; i < num_params; ++i) {
            parameter const& p = params[i];
            if (!p.is_int()) {
                m_manager->raise_exception("expected integer parameter");
                return 0;
            }
            unsigned j = p.get_int();
            if (j >= sorts.size()) {
                // We should not use ast_pp anymore on error messages.
                // m_manager->raise_exception("index %d out of bound %s : %d", j, ast_pp(r, *m_manager).c_str(), sorts.size());
                m_manager->raise_exception("index out of bound");
                return 0;
            }
            if (i == 0) {
                index0 = j;
                last_sort = sorts[j];
            }
            else {
                std::swap(last_sort, sorts[j]);
            }
        }
        sorts[index0] = last_sort;
        vector<parameter> params2;
        for (unsigned i = 0; i < sorts.size(); ++i) {
            params2.push_back(parameter(sorts[i]));
        }
        sort* rng = m_manager->mk_sort(m_family_id, DL_RELATION_SORT, params2.size(), params2.c_ptr());
        func_decl_info info(m_family_id, OP_RA_RENAME, num_params, params);            
        return m_manager->mk_func_decl(m_rename_sym, 1, &r, rng, info);
    }

    func_decl * dl_decl_plugin::mk_join(unsigned num_params, parameter const* params, sort* r1, sort* r2) {
        vector<parameter> params2;
        ptr_vector<sort> sorts1, sorts2;
        if (!is_rel_sort(r1, sorts1)) {
            return 0;
        }
        if (!is_rel_sort(r2, sorts2)) {
            return 0;
        }
        for (unsigned i = 0; i < sorts1.size(); ++i) {
            params2.push_back(parameter(sorts1[i]));
        }
        for (unsigned i = 0; i < sorts2.size(); ++i) {
            params2.push_back(parameter(sorts2[i]));
        }
        if (0 != num_params % 2) {
            m_manager->raise_exception("expecting an even number of parameters to join");
            return 0;
        }
        for (unsigned i = 0; i + 1 < num_params; i += 2) {
            parameter const& p1 = params[i];
            parameter const& p2 = params[i+1];
            if (!p1.is_int() || !p2.is_int()) {
                m_manager->raise_exception("encountered non-integer parameter");
                return 0;
            }
            unsigned i1 = p1.get_int();
            unsigned i2 = p2.get_int();
            if (i1 >= sorts1.size() || i2 >= sorts2.size()) {
                m_manager->raise_exception("index out of bounds");
                return 0;
            }
            if (sorts1[i1] != sorts2[i2]) {
                m_manager->raise_exception("sort miss-match in join");
                return 0;
            }
        }
        sort* args[2] = { r1, r2 };
        sort* rng = m_manager->mk_sort(m_family_id, DL_RELATION_SORT, params2.size(), params2.c_ptr());
        func_decl_info info(m_family_id, OP_RA_JOIN, num_params, params);            
        return m_manager->mk_func_decl(m_join_sym, 2, args, rng, info);
    }

    func_decl* dl_decl_plugin::mk_complement(sort* s) {
        if (!is_rel_sort(s)) {
            return 0;
        }
        func_decl_info info(m_family_id, OP_RA_COMPLEMENT, 0, 0);
        return m_manager->mk_func_decl(m_complement_sym, 1, &s, s, info);        
    }

    func_decl * dl_decl_plugin::mk_negation_filter(unsigned num_params, parameter const* params, sort* r1, sort* r2) {
        ptr_vector<sort> sorts1, sorts2;
        if (!is_rel_sort(r1, sorts1)) {
            return 0;
        }
        if (!is_rel_sort(r2, sorts2)) {
            return 0;
        }
        if (0 != num_params % 2) {
            m_manager->raise_exception("expecting an even number of parameters to negation filter");
            return 0;
        }
        for (unsigned i = 0; i + 1 < num_params; i += 2) {
            parameter const& p1 = params[i];
            parameter const& p2 = params[i+1];
            if (!p1.is_int() || !p2.is_int()) {
                m_manager->raise_exception("encountered non-integer parameter");
                return 0;
            }
            unsigned i1 = p1.get_int();
            unsigned i2 = p2.get_int();
            if (i1 >= sorts1.size() || i2 >= sorts2.size()) {
                m_manager->raise_exception("index out of bounds");
                return 0;
            }
            if (sorts1[i1] != sorts2[i2]) {
                m_manager->raise_exception("sort miss-match in join");
                return 0;
            }
        }
        sort* args[2] = { r1, r2 };
        func_decl_info info(m_family_id, OP_RA_NEGATION_FILTER, num_params, params);            
        return m_manager->mk_func_decl(m_negation_filter_sym, 2, args, r1, info);
    }

    func_decl * dl_decl_plugin::mk_is_empty(sort* s) {
        if (!is_rel_sort(s)) {
            return 0;
        }
        func_decl_info info(m_family_id, OP_RA_IS_EMPTY, 0, 0);
        sort* rng = m_manager->mk_bool_sort();
        return m_manager->mk_func_decl(m_is_empty_sym, 1, &s, rng, info);  
    }

    func_decl * dl_decl_plugin::mk_constant(parameter const* params) {
        parameter const& p = params[0];
        parameter const& ps = params[1];
        if (!p.is_rational() || !p.get_rational().is_uint64()) {
            m_manager->raise_exception("first parameter should be a rational");
            return 0;
        }
        if (!ps.is_ast() || !is_sort(ps.get_ast()) || !is_fin_sort(to_sort(ps.get_ast()))) {
            m_manager->raise_exception("second paramter should be a finite domain sort");
            return 0;
        }
        sort* s = to_sort(ps.get_ast());
        func_decl_info info(m_family_id, OP_DL_CONSTANT, 2, params);
        return m_manager->mk_func_decl(m_num_sym, 0, (sort*const*)0, s, info);
    }

    func_decl * dl_decl_plugin::mk_compare(decl_kind k, symbol const& sym, sort *const* domain) {
        if (!is_sort_of(domain[0], m_family_id, DL_FINITE_SORT)) {
            m_manager->raise_exception("expecting finite domain sort");
            return 0;
        }
        if (domain[0] != domain[1]) {
            m_manager->raise_exception("expecting two identical finite domain sorts");
            return 0;
        }
        func_decl_info info(m_family_id, k, 0, 0);
        return m_manager->mk_func_decl(sym, 2, domain, m_manager->mk_bool_sort(), info);
    }

    func_decl * dl_decl_plugin::mk_clone(sort* s) {
        if (!is_rel_sort(s)) {
            return 0;
        }
        func_decl_info info(m_family_id, OP_RA_CLONE, 0, 0);
        return m_manager->mk_func_decl(m_clone_sym, 1, &s, s, info);
    }

    /**
      In SMT2 syntax, we can write \c "(min v)" where \c v is a variable (also
      known as a "constant" in SMT2 parlance). The minimization of \c v is determined
      by the group-by clause, which is inferred from the head in a rule.

      Example:

        (define-sort nibble_t () (_ BitVec 4))
        (declare-rel triples (nibble_t nibble_t nibble_t))
        (declare-rel pairs (nibble_t nibble_t))

        (declare-var x nibble_t)
        (declare-var y nibble_t)
        (declare-var z nibble_t)

        (rule (triples #x0 #x3 #x5))
        (rule (triples #x0 #x1 #x4))

        (rule (=> (and (triples x y z) (min y)) (pairs x y)))

      This says that we want to find the minimum of \c y in \c pairs grouped by
      \c x because \c y is syntactically different from \c x and \c y appears in the
      head \c "(pairs x y)". Therefore the \c pairs relation will contain a single row
      where \c "x = #x0" and \c "y = #x1".

      Note that "min" refers to a family of functions where each function
      has a different domain.
    */
    func_decl * dl_decl_plugin::mk_min(decl_kind k, unsigned num_parameters, parameter const * parameters,
        sort * const * domain) {
        if (num_parameters) {
            m_manager->raise_exception("invalid min aggregate definition");
            return 0;
        }

        func_decl_info info(m_family_id, k);
        return m_manager->mk_func_decl(m_min_sym, domain[0], m_manager->mk_bool_sort(), info);
    }

    func_decl * dl_decl_plugin::mk_func_decl(
        decl_kind k, unsigned num_parameters, parameter const * parameters, 
        unsigned arity, sort * const * domain, sort * range) {
            func_decl* result = 0;
            switch(k) {

            case OP_RA_STORE: 
            case OP_RA_SELECT:
                if (!check_params(0, 0, num_parameters) ||
                    !check_domain(1, UINT_MAX, arity)) {
                        return 0;
                }
                result = mk_store_select(k, arity, domain);           
                break;

            case OP_RA_EMPTY: 
                if (!check_params( 1, 1, num_parameters) ||
                    !check_domain(0, 0, arity)) {
                        return 0;
                }
                result = mk_empty(parameters[0]);                          
                break;

            case OP_RA_JOIN: 
                if (!check_params(0, UINT_MAX, num_parameters) ||
                    !check_domain(2, 2, arity)) {
                        return 0;
                }
                result = mk_join(num_parameters,  parameters, domain[0], domain[1]);
                break;

            case OP_RA_UNION:
            case OP_RA_WIDEN: 
                if (!check_params( 0, 0, num_parameters) ||
                    !check_domain(2, 2, arity)) {
                        return 0;
                }
                result = mk_unionw(k, domain[0], domain[1]);
                break;

            case OP_RA_PROJECT: 
                if (!check_params( 1, UINT_MAX, num_parameters) ||
                    !check_domain(1, 1, arity)) {
                        return 0;
                }
                result = mk_project(num_parameters, parameters, domain[0]);
                break;

            case OP_RA_FILTER:   
                if (!check_params( 1, 1, num_parameters) ||
                    !check_domain(1, 1, arity)) {
                        return 0;
                }
                result = mk_filter(parameters[0], domain[0]);
                break;

            case OP_RA_IS_EMPTY:
                if (!check_params( 0, 0, num_parameters) ||
                    !check_domain(1, 1, arity)) {
                        return 0;
                }
                result = mk_is_empty(domain[0]);
                break;

            case OP_RA_RENAME:
                if (!check_params( 2, UINT_MAX, num_parameters) ||
                    !check_domain(1, 1, arity)) {
                        return 0;
                }
                result = mk_rename(num_parameters, parameters, domain[0]);
                break;

            case OP_RA_COMPLEMENT:
                if (!check_params( 0, 0, num_parameters) ||
                    !check_domain(1, 1, arity)) {
                        return 0;
                }
                result = mk_complement(domain[0]);
                break;

            case OP_RA_NEGATION_FILTER:
                if (!check_params(1, UINT_MAX, num_parameters) ||
                    !check_domain(2, 2, arity)) {
                        return 0;
                }
                result = mk_negation_filter(num_parameters,  parameters, domain[0], domain[1]);
                break;

            case OP_RA_CLONE:
                if (!check_params(0, 0, num_parameters) || !check_domain(1, 1, arity)) {
                    return 0;
                }
                result = mk_clone(domain[0]);
                break;                

            case OP_DL_CONSTANT:
                if (!check_params( 2, 2, num_parameters) ||
                    !check_domain(0, 0, arity)) {
                        return 0;
                }
                result = mk_constant(parameters);
                break;

            case OP_DL_LT:
                if (!check_params( 0, 0, num_parameters) ||
                    !check_domain(2, 2, arity)) {
                        return 0;
                }
                result = mk_compare(OP_DL_LT, m_lt_sym, domain);
                break;   

            case OP_DL_REP: {
                if (!check_domain(0, 0, num_parameters) ||
                    !check_domain(1, 1, arity)) return 0;
                func_decl_info info(m_family_id, k, 0, 0);
                result = m_manager->mk_func_decl(symbol("rep"), 1, domain, range, info);
                break;
            }
                
            case OP_DL_ABS: {
                if (!check_domain(0, 0, num_parameters) ||
                    !check_domain(1, 1, arity)) return 0;
                func_decl_info info(m_family_id, k, 0, 0);
                result = m_manager->mk_func_decl(symbol("abs"), 1, domain, range, info);
                break;
            }

            case OP_DL_MIN:
                return mk_min(k, num_parameters, parameters, domain);

            default:
                m_manager->raise_exception("operator not recognized");
                return 0;
            }

        TRACE("dl_decl_plugin", tout << mk_pp(result, *m_manager) << "\n";);
        return result;
    }

    void dl_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
        op_names.push_back(builtin_name(m_min_sym.bare_str(), OP_DL_MIN));
    }

    void dl_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {

    }


    dl_decl_util::ast_plugin_registrator::ast_plugin_registrator(ast_manager& m)
    {
        // ensure required plugins are installed into the ast_manager
        reg_decl_plugins(m);
    }

    dl_decl_util::dl_decl_util(ast_manager& m):
        m_plugin_registrator(m),
        m(m), 
        m_arith(m),
        m_bv(m),
        m_fid(m.mk_family_id(symbol("datalog_relation")))
    {}

    // create a constant belonging to a given finite domain.

    app* dl_decl_util::mk_numeral(uint64 value, sort* s) {
        if (is_finite_sort(s)) {
            uint64 sz = 0;
            if (try_get_size(s, sz) && sz <= value) {
                m.raise_exception("value is out of bounds");
            }
            parameter params[2] = { parameter(rational(value, rational::ui64())), parameter(s) };
            return m.mk_const(m.mk_func_decl(m_fid, OP_DL_CONSTANT, 2, params, 0, (sort*const*)0));
        }        
        if (m_arith.is_int(s) || m_arith.is_real(s)) {
            return m_arith.mk_numeral(rational(value, rational::ui64()), s);
        }
        if (m_bv.is_bv_sort(s)) {
            return m_bv.mk_numeral(rational(value, rational::ui64()), s);
        }
        if (m.is_bool(s)) {
            if (value == 0) {
                return m.mk_false();
            }
            SASSERT(value == 1);
            return m.mk_true();
        }
        std::stringstream strm;
        strm << "sort '" << mk_pp(s, m) << "' is not recognized as a sort that contains numeric values.\nUse Bool, BitVec, Int, Real, or a Finite domain sort";
        m.raise_exception(strm.str().c_str());
        return 0;
    }

    bool dl_decl_util::is_numeral(const expr* e, uint64& v) const {
        if (is_numeral(e)) {
            const app* c = to_app(e);
            SASSERT(c->get_decl()->get_num_parameters() == 2);
            parameter const& p = c->get_decl()->get_parameter(0);
            SASSERT(p.is_rational());
            SASSERT(p.get_rational().is_uint64());
            v = p.get_rational().get_uint64();
            return true;
        }
        return false;
    }

    bool dl_decl_util::is_numeral_ext(expr* e, uint64& v) const {
        if (is_numeral(e, v)) {
            return true;
        }
        rational val;
        unsigned bv_size = 0;
        if (m_bv.is_numeral(e, val, bv_size) && bv_size < 64) {
            SASSERT(val.is_uint64());
            v = val.get_uint64();
            return true;
        }
        if (m.is_true(e)) {
            v = 1;
            return true;
        }
        if (m.is_false(e)) {
            v = 0;
            return true;
        }
        return false;
    }

    bool dl_decl_util::is_numeral_ext(expr* c) const {
        if (is_numeral(c)) return true;
        rational val;
        unsigned bv_size = 0;        
        if (m_arith.is_numeral(c, val) && val.is_uint64()) return true;
        if (m_bv.is_numeral(c, val, bv_size) && bv_size < 64) return true;
        return m.is_true(c) || m.is_false(c);
    }

    sort* dl_decl_util::mk_sort(const symbol& name, uint64  domain_size) {
        if (domain_size == 0) {
            std::stringstream sstm;
            sstm << "Domain size of sort '" << name << "' may not be 0";
            throw default_exception(sstm.str());
        }
        parameter params[2] = { parameter(name), parameter(rational(domain_size, rational::ui64())) };
        return m.mk_sort(m_fid, DL_FINITE_SORT, 2, params);
    }

    bool dl_decl_util::try_get_size(const sort * s, uint64& size) const {
        sort_size sz = s->get_info()->get_num_elements();
        if (sz.is_finite()) {
            size = sz.size();
            return true;
        }
        return false;
    }

    app* dl_decl_util::mk_lt(expr* a, expr* b) {
        expr* args[2] = { a, b };
        return m.mk_app(m_fid, OP_DL_LT, 0, 0, 2, args);
    }

    app* dl_decl_util::mk_le(expr* a, expr* b) {
        expr* args[2] = { b, a };
        return m.mk_not(m.mk_app(m_fid, OP_DL_LT, 0, 0, 2, args));
    }

    sort* dl_decl_util::mk_rule_sort() {
        return m.mk_sort(m_fid, DL_RULE_SORT);
    }

    app* dl_decl_util::mk_rule(symbol const& name, unsigned num_args, expr* const* args) {
        ptr_buffer<sort> sorts;
        for (unsigned i = 0; i < num_args; ++i) {
            sorts.push_back(m.get_sort(args[i]));
        }
        func_decl* f = m.mk_func_decl(name, num_args, sorts.c_ptr(), mk_rule_sort());
        return m.mk_app(f, num_args, args);
    }

};
