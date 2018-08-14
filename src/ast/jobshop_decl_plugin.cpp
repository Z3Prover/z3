/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    jobshop_decl_plugin.h

Abstract:

    Declarations used for a job-shop scheduling domain.

Author:

    Nikolaj Bjorner (nbjorner) 2018-8-9 

Revision History:


--*/
#include "ast/jobshop_decl_plugin.h"
#include "ast/arith_decl_plugin.h"

void jobshop_decl_plugin::set_manager(ast_manager* m, family_id fid) {
    decl_plugin::set_manager(m, fid);
    m_int_sort = m_manager->mk_sort(m_manager->mk_family_id("arith"), INT_SORT);
    m_alist_sort = m_manager->mk_sort(symbol("AList"), sort_info(m_family_id, ALIST_SORT));
    m_job_sort = m_manager->mk_sort(symbol("Job"), sort_info(m_family_id, JOB_SORT));
    m_resource_sort = m_manager->mk_sort(symbol("Resource"), sort_info(m_family_id, RESOURCE_SORT));
    m_manager->inc_ref(m_int_sort);
    m_manager->inc_ref(m_resource_sort);
    m_manager->inc_ref(m_job_sort);
    m_manager->inc_ref(m_alist_sort);
}

void jobshop_decl_plugin::finalize() {
    m_manager->dec_ref(m_alist_sort);
    m_manager->dec_ref(m_job_sort);
    m_manager->dec_ref(m_resource_sort);
    m_manager->dec_ref(m_int_sort);
}

sort * jobshop_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    if (num_parameters != 0) {
        m_manager->raise_exception("no parameters expected with job-shop sort");
    }
    switch (static_cast<js_sort_kind>(k)) {
    case JOB_SORT: return m_job_sort;
    case RESOURCE_SORT: return m_resource_sort;
    case ALIST_SORT: return m_alist_sort;
    default: UNREACHABLE(); return nullptr;
    }    
}

func_decl * jobshop_decl_plugin::mk_func_decl(
    decl_kind k, unsigned num_parameters, parameter const * parameters, unsigned arity, sort * const * domain, sort *) {
    switch (static_cast<js_op_kind>(k)) {
    case OP_JS_JOB:       
        check_arity(arity);
        check_index1(num_parameters, parameters);
        return m_manager->mk_func_decl(symbol("job"), arity, domain, m_job_sort, func_decl_info(m_family_id, k, num_parameters, parameters));
    case OP_JS_RESOURCE:
        check_arity(arity);
        check_index1(num_parameters, parameters);
        return m_manager->mk_func_decl(symbol("resource"), arity, domain, m_resource_sort, func_decl_info(m_family_id, k, num_parameters, parameters));
    case OP_JS_START:
        if (arity != 1 || domain[0] != m_job_sort) m_manager->raise_exception("start expects a job argument");
        if (num_parameters > 0) m_manager->raise_exception("no parameters");
        return m_manager->mk_func_decl(symbol("job-start"), arity, domain, m_int_sort, func_decl_info(m_family_id, k, num_parameters, parameters));
    case OP_JS_END:
        if (arity != 1 || domain[0] != m_job_sort) m_manager->raise_exception("resource expects a job argument");
        if (num_parameters > 0) m_manager->raise_exception("no parameters");
        return m_manager->mk_func_decl(symbol("job-end"), arity, domain, m_int_sort, func_decl_info(m_family_id, k, num_parameters, parameters));
    case OP_JS_JOB2RESOURCE:
        if (arity != 1 || domain[0] != m_job_sort) m_manager->raise_exception("job2resource expects a job argument");
        if (num_parameters > 0) m_manager->raise_exception("no parameters");
        return m_manager->mk_func_decl(symbol("job2resource"), arity, domain, m_resource_sort, func_decl_info(m_family_id, k, num_parameters, parameters));


    case OP_JS_MODEL:
        // has no parameters
        // all arguments are of sort alist
        return m_manager->mk_func_decl(symbol("js-model"), arity, domain, m_manager->mk_bool_sort(), func_decl_info(m_family_id, k, num_parameters, parameters));
    case OP_AL_KV:
        // has two parameters, first is symbol
        // has no arguments
        return m_manager->mk_func_decl(symbol("kv"), arity, domain, m_alist_sort, func_decl_info(m_family_id, k, num_parameters, parameters));                
    case OP_AL_LIST:
        // has no parameters
        // all arguments are of sort alist        
        return m_manager->mk_func_decl(symbol("alist"), arity, domain, m_alist_sort, func_decl_info(m_family_id, k, num_parameters, parameters));        
    case OP_JS_JOB_RESOURCE:        
        if (arity != 5) m_manager->raise_exception("add-job-resource expects 5 arguments");
        if (domain[0] != m_job_sort) m_manager->raise_exception("first argument of add-job-resource expects should be a job");
        if (domain[1] != m_resource_sort) m_manager->raise_exception("second argument of add-job-resource expects should be a resource");
        if (domain[2] != m_int_sort) m_manager->raise_exception("3rd argument of add-job-resource expects should be an integer");
        if (domain[3] != m_int_sort) m_manager->raise_exception("4th argument of add-job-resource expects should be an integer");
        if (domain[4] != m_int_sort) m_manager->raise_exception("5th argument of add-job-resource expects should be an integer");
        return m_manager->mk_func_decl(symbol("add-job-resource"), arity, domain, m_alist_sort, func_decl_info(m_family_id, k, num_parameters, parameters));
    case OP_JS_RESOURCE_AVAILABLE:
        if (arity != 4) m_manager->raise_exception("add-resource-available expects 4 arguments");        
        if (domain[0] != m_resource_sort) m_manager->raise_exception("first argument of add-resource-available expects should be a resource");
        if (domain[1] != m_int_sort) m_manager->raise_exception("2nd argument of add-resource-available expects should be an integer");
        if (domain[2] != m_int_sort) m_manager->raise_exception("3rd argument of add-resource-available expects should be an integer");
        if (domain[3] != m_int_sort) m_manager->raise_exception("4th argument of add-resource-available expects should be an integer");
        return m_manager->mk_func_decl(symbol("add-resource-available"), arity, domain, m_alist_sort, func_decl_info(m_family_id, k, num_parameters, parameters));
    case OP_JS_JOB_PREEMPTABLE:
        if (arity != 1 || domain[0] != m_job_sort) m_manager->raise_exception("set-preemptable expects one argument, which is a job");
        return m_manager->mk_func_decl(symbol("set-preemptable"), arity, domain, m_alist_sort, func_decl_info(m_family_id, k, num_parameters, parameters));
    default: 
        UNREACHABLE(); return nullptr;        
    }    
}

void jobshop_decl_plugin::check_arity(unsigned arity) {
    if (arity > 0)
        m_manager->raise_exception("jobshop variables use parameters only and take no arguments");
}

void jobshop_decl_plugin::check_index1(unsigned num_parameters, parameter const* ps) {
    if (num_parameters != 1 || !ps[0].is_int())
        m_manager->raise_exception("jobshop variable expects a single integer parameter");
}

void jobshop_decl_plugin::check_index2(unsigned num_parameters, parameter const* ps) {
    if (num_parameters != 2 || !ps[0].is_int() || !ps[1].is_int())
        m_manager->raise_exception("jobshop variable expects two integer parameters");
}


bool jobshop_decl_plugin::is_value(app * e) const {
    return is_app_of(e, m_family_id, OP_JS_JOB) || is_app_of(e, m_family_id, OP_JS_RESOURCE);
}

void jobshop_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    if (logic == symbol("CSP")) {
        op_names.push_back(builtin_name("job", OP_JS_JOB));
        op_names.push_back(builtin_name("resource", OP_JS_RESOURCE));
        op_names.push_back(builtin_name("job-start", OP_JS_START));
        op_names.push_back(builtin_name("job-end", OP_JS_END));
        op_names.push_back(builtin_name("job2resource", OP_JS_JOB2RESOURCE));
        op_names.push_back(builtin_name("js-model", OP_JS_MODEL));
        op_names.push_back(builtin_name("kv", OP_AL_KV));
        op_names.push_back(builtin_name("alist", OP_AL_LIST));
        op_names.push_back(builtin_name("add-job-resource", OP_JS_JOB_RESOURCE));
        op_names.push_back(builtin_name("add-resource-available", OP_JS_RESOURCE_AVAILABLE));
        op_names.push_back(builtin_name("set-preemptable", OP_JS_JOB_PREEMPTABLE));

    }
}

void jobshop_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
    if (logic == symbol("CSP")) {
        sort_names.push_back(builtin_name("Job", JOB_SORT));
        sort_names.push_back(builtin_name("Resource", RESOURCE_SORT));
    }
}

expr * jobshop_decl_plugin::get_some_value(sort * s) {
    parameter p(0);
    if (is_sort_of(s, m_family_id, JOB_SORT))
        return m_manager->mk_const(mk_func_decl(OP_JS_JOB, 1, &p, 0, nullptr, nullptr));
    if (is_sort_of(s, m_family_id, RESOURCE_SORT))
        return m_manager->mk_const(mk_func_decl(OP_JS_RESOURCE, 1, &p, 0, nullptr, nullptr));
    UNREACHABLE();
    return nullptr;
}


jobshop_util::jobshop_util(ast_manager& m): m(m) {
    m_fid = m.mk_family_id("csp");
    m_plugin = static_cast<jobshop_decl_plugin*>(m.get_plugin(m_fid));
}

sort* jobshop_util::mk_job_sort() { 
    return m_plugin->mk_job_sort(); 
}

sort* jobshop_util::mk_resource_sort() { 
    return m_plugin->mk_resource_sort(); 
}

app* jobshop_util::mk_job(unsigned j) {
    parameter p(j);
    return m.mk_const(m.mk_func_decl(m_fid, OP_JS_JOB, 1, &p, 0, (sort*const*)nullptr, nullptr));
}

unsigned jobshop_util::job2id(expr* j) {
    if (is_app_of(j, m_fid, OP_JS_JOB)) {
        return to_app(j)->get_decl()->get_parameter(0).get_int();
    }
    SASSERT(is_app_of(j, m_fid, OP_JS_START) || 
            is_app_of(j, m_fid, OP_JS_END) ||
            is_app_of(j, m_fid, OP_JS_JOB2RESOURCE));
    return job2id(to_app(j)->get_arg(0));
}

app* jobshop_util::mk_resource(unsigned r) {
    parameter p(r);
    return m.mk_const(m.mk_func_decl(m_fid, OP_JS_RESOURCE, 1, &p, 0, (sort*const*)nullptr, nullptr));
}

unsigned jobshop_util::resource2id(expr* r) {
    SASSERT(is_app_of(r, m_fid, OP_JS_RESOURCE));
    return to_app(r)->get_decl()->get_parameter(0).get_int();
}

app* jobshop_util::mk_start(unsigned j) { 
    app_ref job(mk_job(j), m);
    sort* js = m.get_sort(job);
    return m.mk_app(m.mk_func_decl(m_fid, OP_JS_START, 0, nullptr, 1, &js, nullptr), job);
}
        
app* jobshop_util::mk_end(unsigned j) {    
    app_ref job(mk_job(j), m);
    sort* js = m.get_sort(job);
    return m.mk_app(m.mk_func_decl(m_fid, OP_JS_END, 0, nullptr, 1, &js, nullptr), job);
}

app* jobshop_util::mk_job2resource(unsigned j) { 
    app_ref job(mk_job(j), m);
    sort* js = m.get_sort(job);
    return m.mk_app(m.mk_func_decl(m_fid, OP_JS_JOB2RESOURCE, 0, nullptr, 1, &js, nullptr), job);
}

bool jobshop_util::is_resource(expr* e, unsigned& r) {
    return is_app_of(e, m_fid, OP_JS_RESOURCE) && (r = resource2id(e), true);
}

bool jobshop_util::is_job(expr* e, unsigned& j) {
    return is_app_of(e, m_fid, OP_JS_JOB) && (j = job2id(e), true);
}

bool jobshop_util::is_add_resource_available(expr * e, expr *& res, unsigned& loadpct, uint64_t& start, uint64_t& end) {
    if (!is_app_of(e, m_fid, OP_JS_RESOURCE_AVAILABLE)) return false;
    res = to_app(e)->get_arg(0);
    arith_util a(m);
    rational r;
    if (!a.is_numeral(to_app(e)->get_arg(1), r) || !r.is_unsigned()) return false;
    loadpct = r.get_unsigned();
    if (!a.is_numeral(to_app(e)->get_arg(2), r) || !r.is_uint64()) return false;
    start = r.get_uint64();
    if (!a.is_numeral(to_app(e)->get_arg(3), r) || !r.is_uint64()) return false;
    end = r.get_uint64();
    return true;
}

bool jobshop_util::is_add_job_resource(expr * e, expr *& job, expr*& res, unsigned& loadpct, uint64_t& capacity, uint64_t& end) {
    if (!is_app_of(e, m_fid, OP_JS_JOB_RESOURCE)) return false;
    job = to_app(e)->get_arg(0);
    res = to_app(e)->get_arg(1);
    arith_util a(m);
    rational r;
    if (!a.is_numeral(to_app(e)->get_arg(2), r) || !r.is_unsigned()) return false;
    loadpct = r.get_unsigned();
    if (!a.is_numeral(to_app(e)->get_arg(3), r) || !r.is_uint64()) return false;
    capacity = r.get_uint64();
    if (!a.is_numeral(to_app(e)->get_arg(4), r) || !r.is_uint64()) return false;
    end = r.get_uint64();
    return true;
}

bool jobshop_util::is_set_preemptable(expr* e, expr *& job) {
    if (!is_app_of(e, m_fid, OP_JS_JOB_PREEMPTABLE)) return false;
    job = to_app(e)->get_arg(0);
    return true;
}
