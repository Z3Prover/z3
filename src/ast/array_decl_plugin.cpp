/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    array_decl_plugin.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-09

Revision History:

--*/
#include<sstream>
#include"array_decl_plugin.h"
#include"warning.h"
#include"ast_pp.h"
#include"ast_ll_pp.h"

array_decl_plugin::array_decl_plugin():
    m_store_sym("store"),
    m_select_sym("select"),
    m_const_sym("const"),
    m_default_sym("default"),
    m_map_sym("map"),
    m_set_union_sym("union"),
    m_set_intersect_sym("intersect"),
    m_set_difference_sym("difference"),
    m_set_complement_sym("complement"),
    m_set_subset_sym("subset"),
    m_array_ext_sym("array-ext"),
    m_as_array_sym("as-array") {
}

#define ARRAY_SORT_STR "Array"

sort * array_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {

    if (k == _SET_SORT) {
        if (num_parameters != 1) {
            m_manager->raise_exception("invalid array sort definition, invalid number of parameters");
            return 0;
        }
        parameter params[2] = { parameters[0], parameter(m_manager->mk_bool_sort()) };
        return mk_sort(ARRAY_SORT, 2, params);
    }
    SASSERT(k == ARRAY_SORT);
    if (num_parameters < 2) {
        m_manager->raise_exception("invalid array sort definition, invalid number of parameters");
        return 0;
    }
    
    for (unsigned i = 0; i < num_parameters; i++) {
        if (!parameters[i].is_ast() || !is_sort(parameters[i].get_ast())) {
            m_manager->raise_exception("invalid array sort definition, parameter is not a sort");
            return 0;
        }
    }
    sort * range = to_sort(parameters[num_parameters - 1].get_ast());
    TRACE("array_decl_plugin_bug", tout << mk_pp(range, *m_manager) << "\n";);
    if (!range->is_infinite() && !range->is_very_big() && (1 == range->get_num_elements().size())) {
        return m_manager->mk_sort(symbol(ARRAY_SORT_STR), sort_info(m_family_id, ARRAY_SORT, 1, 
                                                             num_parameters, parameters));
    }
    bool is_infinite = false;
    bool is_very_big = false;
    for (unsigned i = 0; i < num_parameters; i++) {
        sort * s = to_sort(parameters[i].get_ast());
        if (s->is_infinite()) {
            is_infinite = true;
        }
        if (s->is_very_big()) {
            is_very_big = true;
        }
    }
    if (is_infinite) {
        return m_manager->mk_sort(symbol(ARRAY_SORT_STR), sort_info(m_family_id, ARRAY_SORT, num_parameters, parameters));
    }
    else if (is_very_big) {
        return m_manager->mk_sort(symbol(ARRAY_SORT_STR), sort_info(m_family_id, ARRAY_SORT, sort_size::mk_very_big(),
                                                             num_parameters, parameters));
    }
    else {
        rational domain_sz(1);
        rational num_elements;
        for (unsigned i = 0; i < num_parameters - 1; i++) {
            domain_sz *= rational(to_sort(parameters[i].get_ast())->get_num_elements().size(),rational::ui64());
        }
        if (domain_sz <= rational(128)) {
            num_elements = rational(range->get_num_elements().size(),rational::ui64());
            num_elements = power(num_elements, static_cast<int>(domain_sz.get_int64()));
        }

        if (domain_sz > rational(128) || !num_elements.is_uint64()) {
            // too many elements...
            return m_manager->mk_sort(symbol(ARRAY_SORT_STR), 
                                      sort_info(m_family_id, 
                                                ARRAY_SORT, 
                                                sort_size::mk_very_big(), 
                                                num_parameters, 
                                                parameters));
        }
        else {
            return m_manager->mk_sort(symbol(ARRAY_SORT_STR), sort_info(m_family_id, ARRAY_SORT, num_elements.get_uint64(), 
                                                                 num_parameters, parameters));
        }
    }
}

bool array_decl_plugin::is_array_sort(sort* s) const {
    return m_family_id == s->get_family_id() && s->get_decl_kind() == ARRAY_SORT;
}


func_decl * array_decl_plugin::mk_const(sort * s, unsigned arity, sort * const * domain) {
    if (arity != 1) {
        m_manager->raise_exception("invalid const array definition, invalid domain size");
        return 0;
    }
    if (!is_array_sort(s)) {
        m_manager->raise_exception("invalid const array definition, parameter is not an array sort");
        return 0;
    }
    if (!m_manager->compatible_sorts(get_array_range(s), domain[0])) {
        m_manager->raise_exception("invalid const array definition, sort mismatch between array range and argument");
        return 0;
    }
    parameter param(s);
    func_decl_info info(m_family_id, OP_CONST_ARRAY, 1, &param);
    info.m_private_parameters = true;
    return m_manager->mk_func_decl(m_const_sym, arity, domain, s, info);
}

func_decl * array_decl_plugin::mk_map(func_decl* f, unsigned arity, sort* const* domain) {
    if (arity != f->get_arity()) {
        std::ostringstream buffer;
        buffer << "map expects to take as many arguments as the function being mapped, "
               << "it was given " << arity << " but expects " << f->get_arity();
        m_manager->raise_exception(buffer.str().c_str());
        return 0;        
    }
    if (arity == 0) {
        m_manager->raise_exception("don't use map on constants");
        return 0;
    }
    //
    // check that each domain[i] is an array sort 
    // with the same domains and same ranges.
    // and that the ranges coincide with the domain of f.
    //
    unsigned dom_arity = get_array_arity(domain[0]);
    for (unsigned i = 0; i < arity; ++i) {
        if (!is_array_sort(domain[i])) {
            std::ostringstream buffer;
            buffer << "map expects an array sort as argument at position " << i;
            m_manager->raise_exception(buffer.str().c_str());
            return 0;        
        }
        if (get_array_arity(domain[i]) != dom_arity) {
            std::ostringstream buffer;
            buffer << "map expects all arguments to have the same array domain,  "
                   << "this is not the case for argument " << i;
            m_manager->raise_exception(buffer.str().c_str());
            return 0;                    
        }
        for (unsigned j = 0; j < dom_arity; ++j) {
            if (get_array_domain(domain[i],j) != get_array_domain(domain[0],j)) {
                std::ostringstream buffer;
                buffer << "map expects all arguments to have the same array domain, "
                       << "this is not the case for argument " << i;
                m_manager->raise_exception(buffer.str().c_str());
                return 0;                    
            }
        }
        if (get_array_range(domain[i]) != f->get_domain(i)) {
            std::ostringstream buffer;
            buffer << "map expects the argument at position " << i 
                   << " to have the array range the same as the function";
            m_manager->raise_exception(buffer.str().c_str());
            return 0;                                
        }
    }
    vector<parameter> parameters;
    for (unsigned i = 0; i < dom_arity; ++i) {
        parameters.push_back(domain[0]->get_parameter(i));
    }
    parameters.push_back(parameter(f->get_range()));
    sort* range = mk_sort(ARRAY_SORT, parameters.size(), parameters.c_ptr());
    parameter param(f);
    func_decl_info info(m_family_id, OP_ARRAY_MAP, 1, &param);
    //
    // left_associative, right_associative, commutative are inherited.
    // m_injective is inherited, since:
    // forall x . g(f(x)) = x implies forall X .  map(g)(map(f)(X)) = X
    // since map(g)(map(f)(X))[i] = g(f(X[i])) = X[i]
    // 

    info.set_right_associative(f->is_right_associative());
    info.set_left_associative(f->is_left_associative());
    info.set_commutative(f->is_commutative());
    info.set_injective(f->is_injective());
    return m_manager->mk_func_decl(m_map_sym, arity, domain, range, info);
}


func_decl * array_decl_plugin::mk_default(unsigned domain_size, sort * const * domain) {
    if (domain_size != 1) {
        m_manager->raise_exception("invalid default array definition, invalid domain size");
        return 0;
    }
    // check that domain[0] is an array sort.
    unsigned num_parameters = domain[0]->get_num_parameters();

    if (num_parameters <= 1) {
        m_manager->raise_exception("parameter mismatch. There should be more than one parameter to defaults");
        return 0;
    }
    parameter param(domain[0]->get_parameter(num_parameters-1));
    if (!param.is_ast() || !is_sort(param.get_ast())) {
        m_manager->raise_exception("last parameter should be a sort");
        return 0;
    }
    sort * s = to_sort(param.get_ast());
        
    return m_manager->mk_func_decl(m_default_sym, domain_size, domain, s,
                                   func_decl_info(m_family_id, OP_ARRAY_DEFAULT));
}


func_decl* array_decl_plugin::mk_select(unsigned arity, sort * const * domain) {
    if (arity <= 1) {
        m_manager->raise_exception("select takes at least two arguments");
        return 0;
    }
    sort * s = domain[0];
    unsigned num_parameters = s->get_num_parameters();
    parameter const* parameters = s->get_parameters();
 
    if (num_parameters != arity) {
        m_manager->raise_exception("select requires as many arguments as the size of the domain");
        return 0;
    }
    ptr_buffer<sort> new_domain; // we need this because of coercions.
    new_domain.push_back(s);
    for (unsigned i = 0; i + 1 < num_parameters; ++i) {
        if (!parameters[i].is_ast() || 
            !is_sort(parameters[i].get_ast()) || 
            !m_manager->compatible_sorts(domain[i+1], to_sort(parameters[i].get_ast()))) {
            m_manager->raise_exception("domain sort and parameter do not match");
            UNREACHABLE();
            return 0;
        }
        new_domain.push_back(to_sort(parameters[i].get_ast()));
    }
    SASSERT(new_domain.size() == arity);
    return m_manager->mk_func_decl(m_select_sym, arity, new_domain.c_ptr(), get_array_range(domain[0]),
                                   func_decl_info(m_family_id, OP_SELECT));
}

func_decl * array_decl_plugin::mk_store(unsigned arity, sort * const * domain) {
    if (arity < 3) {
        m_manager->raise_exception("store takes at least 3 arguments");
        return 0;
    }
    sort * s = domain[0];
    unsigned num_parameters = s->get_num_parameters();
    parameter const * parameters = s->get_parameters();
    if (!is_array_sort(s)) {
        m_manager->raise_exception("store expects the first argument sort to be an array");
        UNREACHABLE();
        return 0;
    }
    if (arity != num_parameters+1) {
        std::ostringstream buffer;
        buffer << "store expects the first argument to be an array taking " << num_parameters+1 
               << ", instead it was passed " << (arity - 1) << "arguments";
        m_manager->raise_exception(buffer.str().c_str());
        UNREACHABLE();
        return 0;
    }
    ptr_buffer<sort> new_domain; // we need this because of coercions.
    new_domain.push_back(s);
    for (unsigned i = 0; i < num_parameters; ++i) {
        if (!parameters[i].is_ast() || !is_sort(parameters[i].get_ast())) {
            m_manager->raise_exception("expecting sort parameter");
            return 0;
        }
        if (!m_manager->compatible_sorts(to_sort(parameters[i].get_ast()), domain[i+1])) {
            m_manager->raise_exception("domain sort and parameter do not match");
            UNREACHABLE();
            return 0;
        }
        new_domain.push_back(to_sort(parameters[i].get_ast()));
    }
    SASSERT(new_domain.size() == arity);
    return m_manager->mk_func_decl(m_store_sym, arity, new_domain.c_ptr(), domain[0],
                                   func_decl_info(m_family_id, OP_STORE));
}

func_decl * array_decl_plugin::mk_array_ext(unsigned arity, sort * const * domain, unsigned i) {
    if (arity != 2 || domain[0] != domain[1]) {
        UNREACHABLE();
        return 0;
    }
    sort * s = domain[0];
    unsigned num_parameters = s->get_num_parameters();
    if (num_parameters == 0 || i >= num_parameters - 1) {
        UNREACHABLE();
        return 0;
    }
    sort * r = to_sort(s->get_parameter(i).get_ast());
    parameter param(s);
    return m_manager->mk_func_decl(m_array_ext_sym, arity, domain, r, func_decl_info(m_family_id, OP_ARRAY_EXT, 1, &param));
}


bool array_decl_plugin::check_set_arguments(unsigned arity, sort * const * domain) {
    for (unsigned i = 0; i < arity; ++i) {
        if (domain[i] != domain[0]) {
            std::ostringstream buffer;
            buffer << "arguments " << 1 << " and " << (i+1) << " have different sorts";
            m_manager->raise_exception(buffer.str().c_str());
            return false;
        }
        if (domain[i]->get_family_id() != m_family_id) {
            std::ostringstream buffer;
            buffer << "argument " << (i+1) << " is not of array sort";
            m_manager->raise_exception(buffer.str().c_str());
            return false;
        }
    }
    if (arity > 0) {
        unsigned num_params = domain[0]->get_num_parameters();
        parameter const* params = domain[0]->get_parameters();
        if (1 >= num_params) {
            m_manager->raise_exception("expecting 2 or more parameters");
            UNREACHABLE();
            return false;
        }
        if (!params[num_params-1].is_ast()) {
            m_manager->raise_exception("expecting term parameters");
            UNREACHABLE();
            return false;
        }
        if (!is_sort(params[num_params-1].get_ast()) || !m_manager->is_bool(to_sort(params[num_params-1].get_ast()))) {
            m_manager->raise_exception("expecting boolean range");
            UNREACHABLE();
            return false;
        }
    }
    return true;
}

func_decl * array_decl_plugin::mk_set_union(unsigned arity, sort * const * domain) {

    if (arity == 0) {
        m_manager->raise_exception("union takes at least one argument");
        return 0;
    }
    sort * s = domain[0];
    if (!check_set_arguments(arity, domain)) {
        return 0;
    }
    parameter param(s);
    func_decl_info info(m_family_id, OP_SET_UNION, 1, &param);
    info.set_associative();
    info.set_commutative();
    info.set_idempotent();
    sort* domain2[2] = { domain[0], domain[0] };
    return m_manager->mk_func_decl(m_set_union_sym, 2, domain2, domain[0], info);
}

func_decl * array_decl_plugin::mk_set_intersect(unsigned arity, sort * const * domain) {
    
    if (arity == 0) {
        m_manager->raise_exception("intersection takes at least one argument");
        return 0;
    }
    if (!check_set_arguments(arity, domain)) {
        return 0;
    }
    func_decl_info info(m_family_id, OP_SET_INTERSECT);
    info.set_associative();
    info.set_commutative();
    info.set_idempotent();
    sort* domain2[2] = { domain[0], domain[0] };
    return m_manager->mk_func_decl(m_set_intersect_sym, 2, domain2, domain[0], info);
}

func_decl * array_decl_plugin::mk_set_difference(unsigned arity, sort * const * domain) {
    if (arity != 2) {
        m_manager->raise_exception("set difference takes precisely two arguments");
        return 0;
    }
    if (!check_set_arguments(arity, domain)) {
        return 0;
    }
    return m_manager->mk_func_decl(m_set_difference_sym, arity, domain, domain[0], 
                                   func_decl_info(m_family_id, OP_SET_DIFFERENCE));
}

func_decl * array_decl_plugin::mk_set_complement(unsigned arity, sort * const * domain) {
    if (arity != 1) {
        m_manager->raise_exception("set complement takes one argument");
        return 0;
    }
    if (!check_set_arguments(arity, domain)) {
        return 0;
    }
    return m_manager->mk_func_decl(m_set_complement_sym, arity, domain, domain[0], 
                                   func_decl_info(m_family_id, OP_SET_COMPLEMENT));
}

func_decl * array_decl_plugin::mk_set_subset(unsigned arity, sort * const * domain) {
    if (arity != 2) {
        m_manager->raise_exception("subset takes two arguments");
        return 0;
    }
    if (!check_set_arguments(arity, domain)) {
        return 0;
    }
    sort * bool_sort = m_manager->mk_bool_sort();
    return m_manager->mk_func_decl(m_set_subset_sym, arity, domain, bool_sort, 
                                   func_decl_info(m_family_id, OP_SET_SUBSET));
}

func_decl * array_decl_plugin::mk_as_array(func_decl * f) {
    vector<parameter> parameters;
    for (unsigned i = 0; i < f->get_arity(); i++) {
        parameters.push_back(parameter(f->get_domain(i)));
    }
    parameters.push_back(parameter(f->get_range()));
    sort * s = mk_sort(ARRAY_SORT, parameters.size(), parameters.c_ptr());
    parameter param(f);
    func_decl_info info(m_family_id, OP_AS_ARRAY, 1, &param);
    return m_manager->mk_const_decl(m_as_array_sym, s, info);
}


func_decl * array_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                            unsigned arity, sort * const * domain, sort * range) {
    switch (k) {
    case OP_SELECT: 
        return mk_select(arity, domain);
    case OP_STORE:
        return mk_store(arity, domain);
    case OP_CONST_ARRAY: {
        if (num_parameters == 1 && parameters[0].is_ast() && is_sort(parameters[0].get_ast())) {
            sort * s = to_sort(parameters[0].get_ast());
            return mk_const(s, arity, domain);
        }
        else if (range != 0) {
            return mk_const(range, arity, domain); 
        }
        else {
            m_manager->raise_exception("array operation requires one sort parameter (the array sort)");
            UNREACHABLE();
            return 0;
        }
    }
    case OP_ARRAY_MAP: {
        if (num_parameters != 1 || !parameters[0].is_ast() || !is_func_decl(parameters[0].get_ast())) {
            m_manager->raise_exception("array operation requires one function declaration parameter (the function to be mapped)");
            UNREACHABLE();
            return 0;
        }
        func_decl * f = to_func_decl(parameters[0].get_ast());
        return mk_map(f, arity, domain);        
    }
    case OP_ARRAY_EXT:
        if (num_parameters == 0) {
            return mk_array_ext(arity, domain, 0);
        }
        if (num_parameters != 1 || !parameters[0].is_int()) {
            UNREACHABLE();
            return 0;
        }
        return mk_array_ext(arity, domain, parameters[0].get_int());
    case OP_ARRAY_DEFAULT:
        return mk_default(arity, domain);
    case OP_SET_UNION:
        return mk_set_union(arity, domain);
    case OP_SET_INTERSECT:
        return mk_set_intersect(arity, domain);
    case OP_SET_DIFFERENCE:
        return mk_set_difference(arity, domain);
    case OP_SET_COMPLEMENT:
        return mk_set_complement(arity, domain);
    case OP_SET_SUBSET:
        return mk_set_subset(arity, domain);
    case OP_AS_ARRAY: {
        if (num_parameters != 1 ||
            !parameters[0].is_ast() || 
            !is_func_decl(parameters[0].get_ast()) || 
            to_func_decl(parameters[0].get_ast())->get_arity() == 0) {
            TRACE("array_bug",
                  tout << "num_parameters: " << num_parameters << std::endl;
                  tout << "parameter.kind: " << parameters[0].is_int() << " " << parameters[0].is_ast() << " " << parameters[0].is_symbol() << "\n";
                  tout << "as-array-bug: " << to_func_decl(parameters[0].get_ast())->get_name() << " " << to_func_decl(parameters[0].get_ast())->get_arity() << std::endl;);
            m_manager->raise_exception("as-array takes one parameter, a function declaration with arity greater than zero");
            UNREACHABLE();
            return 0;
        }
        func_decl * f = to_func_decl(parameters[0].get_ast());
        return mk_as_array(f);
    }
    default: return 0;
    }
}

void array_decl_plugin::get_sort_names(svector<builtin_name>& sort_names, symbol const & logic) {
    sort_names.push_back(builtin_name(ARRAY_SORT_STR, ARRAY_SORT));
    // TBD: this could easily break users even though it is already used in CVC4: 
    // sort_names.push_back(builtin_name("Set", _SET_SORT));
}

void array_decl_plugin::get_op_names(svector<builtin_name>& op_names, symbol const & logic) {
    op_names.push_back(builtin_name("store",OP_STORE));
    op_names.push_back(builtin_name("select",OP_SELECT));
    if (logic == symbol::null || logic == symbol("HORN")) {
        // none of the SMT2 logics support these extensions
        op_names.push_back(builtin_name("const",OP_CONST_ARRAY));
        op_names.push_back(builtin_name("map",OP_ARRAY_MAP));
        op_names.push_back(builtin_name("default",OP_ARRAY_DEFAULT));
        op_names.push_back(builtin_name("union",OP_SET_UNION));
        op_names.push_back(builtin_name("intersect",OP_SET_INTERSECT));
        op_names.push_back(builtin_name("difference",OP_SET_DIFFERENCE));
        op_names.push_back(builtin_name("complement",OP_SET_COMPLEMENT));
        op_names.push_back(builtin_name("subset",OP_SET_SUBSET));
        op_names.push_back(builtin_name("as-array", OP_AS_ARRAY));
        op_names.push_back(builtin_name("array-ext", OP_ARRAY_EXT));
    }
}


expr * array_decl_plugin::get_some_value(sort * s) {
    SASSERT(s->is_sort_of(m_family_id, ARRAY_SORT));
    sort * r = to_sort(s->get_parameter(s->get_num_parameters() - 1).get_ast());
    expr * v = m_manager->get_some_value(r);
    parameter p(s);
    return m_manager->mk_app(m_family_id, OP_CONST_ARRAY, 1, &p, 1, &v);
}

bool array_decl_plugin::is_fully_interp(sort const * s) const {
    SASSERT(s->is_sort_of(m_family_id, ARRAY_SORT));
    unsigned sz = get_array_arity(s);
    for (unsigned i = 0; i < sz; i++) {
        if (!m_manager->is_fully_interp(get_array_domain(s, i)))
            return false;
    }
    return m_manager->is_fully_interp(get_array_range(s));
}

func_decl * array_recognizers::get_as_array_func_decl(app * n) const { 
    SASSERT(is_as_array(n)); 
    return to_func_decl(n->get_decl()->get_parameter(0).get_ast()); 
}

array_util::array_util(ast_manager& m): 
    array_recognizers(m.mk_family_id("array")),
    m_manager(m) {
}

bool array_util::is_as_array_tree(expr * n) {
    ptr_buffer<expr, 32> todo;
    todo.push_back(n);
    while (!todo.empty()) {
        expr * curr = todo.back();
        todo.pop_back();
        if (is_as_array(curr))
            continue;
        if (m_manager.is_ite(curr)) {
            todo.push_back(to_app(curr)->get_arg(1));
            todo.push_back(to_app(curr)->get_arg(2));
            continue;
        }
        return false;
    }
    return true;
}

sort * array_util::mk_array_sort(unsigned arity, sort* const* domain, sort* range) {
    vector<parameter> params;
    for (unsigned i = 0; i < arity; ++i) {
        params.push_back(parameter(domain[i]));
    }
    params.push_back(parameter(range));
    return m_manager.mk_sort(m_fid, ARRAY_SORT, params.size(), params.c_ptr());
}
