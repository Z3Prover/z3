/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    csp_decl_plugin.h

Abstract:

    Declarations used for a job-shop scheduling domain.

Author:

    Nikolaj Bjorner (nbjorner) 2018-8-9 

Revision History:


--*/
#include "ast/csp_decl_plugin.h"
#include "ast/arith_decl_plugin.h"

void csp_decl_plugin::set_manager(ast_manager* m, family_id fid) {
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

void csp_decl_plugin::finalize() {
    m_manager->dec_ref(m_alist_sort);
    m_manager->dec_ref(m_job_sort);
    m_manager->dec_ref(m_resource_sort);
    m_manager->dec_ref(m_int_sort);
}

sort * csp_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
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

func_decl * csp_decl_plugin::mk_func_decl(
    decl_kind k, unsigned num_parameters, parameter const * parameters, unsigned arity, sort * const * domain, sort *) {
    symbol name;
    sort* rng = nullptr;
    switch (static_cast<js_op_kind>(k)) {
    case OP_JS_JOB:       
        check_arity(arity);
        check_index1(num_parameters, parameters);
        name = symbol("job");
        rng = m_job_sort;
        break;
    case OP_JS_RESOURCE:
        check_arity(arity);
        check_index1(num_parameters, parameters);
        name = symbol("resource");
        rng = m_resource_sort;
        break;
    case OP_JS_RESOURCE_MAKESPAN:
        if (arity != 1 || domain[0] != m_resource_sort) m_manager->raise_exception("makespan expects a resource argument");
        name = symbol("makespan");
        rng = m_int_sort;
        break;
    case OP_JS_START:
        if (arity != 1 || domain[0] != m_job_sort) m_manager->raise_exception("start expects a job argument");
        if (num_parameters > 0) m_manager->raise_exception("no parameters");
        name = symbol("job-start");
        rng = m_int_sort;
        break;
    case OP_JS_END:
        if (arity != 1 || domain[0] != m_job_sort) m_manager->raise_exception("resource expects a job argument");
        if (num_parameters > 0) m_manager->raise_exception("no parameters");
        name = symbol("job-end");
        rng = m_int_sort;
        break;
    case OP_JS_JOB2RESOURCE:
        if (arity != 1 || domain[0] != m_job_sort) m_manager->raise_exception("job2resource expects a job argument");
        if (num_parameters > 0) m_manager->raise_exception("no parameters");
        name = symbol("job2resource");
        rng = m_resource_sort;
        break;
    case OP_JS_MODEL:
        // has no parameters
        // all arguments are of sort alist
        name = symbol("js-model");
        rng = m_manager->mk_bool_sort();
        break;
    case OP_JS_JOB_RESOURCE:        
        if (arity != 6) m_manager->raise_exception("add-job-resource expects 6 arguments");
        if (domain[0] != m_job_sort) m_manager->raise_exception("first argument of add-job-resource expects should be a job");
        if (domain[1] != m_resource_sort) m_manager->raise_exception("second argument of add-job-resource expects should be a resource");
        if (domain[2] != m_int_sort) m_manager->raise_exception("3rd argument of add-job-resource expects should be an integer");
        if (domain[3] != m_int_sort) m_manager->raise_exception("4th argument of add-job-resource expects should be an integer");
        if (domain[4] != m_int_sort) m_manager->raise_exception("5th argument of add-job-resource expects should be an integer");
        if (domain[5] != m_alist_sort) m_manager->raise_exception("6th argument of add-job-resource should be a list of properties");
        name = symbol("add-job-resource");
        rng = m_alist_sort;
        break;
    case OP_JS_RESOURCE_AVAILABLE:
        if (arity != 6) m_manager->raise_exception("add-resource-available expects 6 arguments");        
        if (domain[0] != m_resource_sort) m_manager->raise_exception("first argument of add-resource-available expects should be a resource");
        if (domain[1] != m_int_sort) m_manager->raise_exception("2nd argument of add-resource-available expects should be an integer");
        if (domain[2] != m_int_sort) m_manager->raise_exception("3rd argument of add-resource-available expects should be an integer");
        if (domain[3] != m_int_sort) m_manager->raise_exception("4th argument of add-resource-available expects should be an integer");
        if (domain[4] != m_int_sort) m_manager->raise_exception("5th argument of add-resource-available expects should be an integer");
        if (domain[5] != m_alist_sort) m_manager->raise_exception("6th argument of add-resource-available should be a list of properties");
        name = symbol("add-resource-available");
        rng = m_alist_sort;
        break;
    case OP_JS_JOB_PREEMPTABLE:
        if (arity != 1 || domain[0] != m_job_sort) 
            m_manager->raise_exception("set-preemptable expects one argument, which is a job");
        name = symbol("set-preemptable");
        rng = m_alist_sort;
        break;
    case OP_JS_PROPERTIES:
        if (arity != 0) m_manager->raise_exception("js-properties takes no arguments");
        for (unsigned i = 0; i < num_parameters; ++i) {
            if (!parameters[i].is_symbol()) m_manager->raise_exception("js-properties expects a list of keyword parameters");
        }
        name = symbol("js-properties");
        rng = m_alist_sort;
        break;
    case OP_JS_JOB_GOAL:
        if (arity != 1 || domain[0] != m_job_sort) 
            m_manager->raise_exception("add-job-goal expects one argument, which is a job");
        if (num_parameters != 2 || !parameters[0].is_symbol() || !parameters[1].is_int())
            m_manager->raise_exception("add-job-goal expects one symbol and one integer parameter");
        name = symbol("add-job-goal");
        rng = m_alist_sort;
        break;
    case OP_JS_OBJECTIVE:
        if (arity != 0)
            m_manager->raise_exception("add-optimization-objective expects no arguments");
        if (num_parameters != 1 || !parameters[0].is_symbol())
            m_manager->raise_exception("add-optimization-objective expects one symbol parameter");
        name = symbol("add-optimization-objective");
        rng = m_alist_sort;
        break;
    default: 
        UNREACHABLE(); 
        return nullptr;        
    }    
    return m_manager->mk_func_decl(name, arity, domain, rng, func_decl_info(m_family_id, k, num_parameters, parameters));

}

void csp_decl_plugin::check_arity(unsigned arity) {
    if (arity > 0)
        m_manager->raise_exception("csp variables use parameters only and take no arguments");
}

void csp_decl_plugin::check_index1(unsigned num_parameters, parameter const* ps) {
    if (num_parameters != 1 || !ps[0].is_int())
        m_manager->raise_exception("csp variable expects a single integer parameter");
}

void csp_decl_plugin::check_index2(unsigned num_parameters, parameter const* ps) {
    if (num_parameters != 2 || !ps[0].is_int() || !ps[1].is_int())
        m_manager->raise_exception("csp variable expects two integer parameters");
}


bool csp_decl_plugin::is_value(app * e) const {
    return is_app_of(e, m_family_id, OP_JS_JOB) || is_app_of(e, m_family_id, OP_JS_RESOURCE);
}

void csp_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    if (logic == symbol("CSP")) {
        op_names.push_back(builtin_name("job", OP_JS_JOB));
        op_names.push_back(builtin_name("resource", OP_JS_RESOURCE));
        op_names.push_back(builtin_name("makespan", OP_JS_RESOURCE_MAKESPAN));
        op_names.push_back(builtin_name("job-start", OP_JS_START));
        op_names.push_back(builtin_name("job-end", OP_JS_END));
        op_names.push_back(builtin_name("job2resource", OP_JS_JOB2RESOURCE));
        op_names.push_back(builtin_name("js-model", OP_JS_MODEL));
        op_names.push_back(builtin_name("add-job-resource", OP_JS_JOB_RESOURCE));
        op_names.push_back(builtin_name("add-resource-available", OP_JS_RESOURCE_AVAILABLE));
        op_names.push_back(builtin_name("set-preemptable", OP_JS_JOB_PREEMPTABLE));
        op_names.push_back(builtin_name("js-properties", OP_JS_PROPERTIES));
        op_names.push_back(builtin_name("add-job-goal", OP_JS_JOB_GOAL));
        op_names.push_back(builtin_name("add-optimization-objective", OP_JS_OBJECTIVE));
    }
}

void csp_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
    if (logic == symbol("CSP")) {
        sort_names.push_back(builtin_name("Job", JOB_SORT));
        sort_names.push_back(builtin_name("Resource", RESOURCE_SORT));
    }
}

expr * csp_decl_plugin::get_some_value(sort * s) {
    parameter p(0);
    if (is_sort_of(s, m_family_id, JOB_SORT))
        return m_manager->mk_const(mk_func_decl(OP_JS_JOB, 1, &p, 0, nullptr, nullptr));
    if (is_sort_of(s, m_family_id, RESOURCE_SORT))
        return m_manager->mk_const(mk_func_decl(OP_JS_RESOURCE, 1, &p, 0, nullptr, nullptr));
    UNREACHABLE();
    return nullptr;
}


csp_util::csp_util(ast_manager& m): m(m) {
    m_fid = m.mk_family_id("csp");
    m_plugin = static_cast<csp_decl_plugin*>(m.get_plugin(m_fid));
}

sort* csp_util::mk_job_sort() { 
    return m_plugin->mk_job_sort(); 
}

sort* csp_util::mk_resource_sort() { 
    return m_plugin->mk_resource_sort(); 
}

app* csp_util::mk_job(unsigned j) {
    parameter p(j);
    return m.mk_const(m.mk_func_decl(m_fid, OP_JS_JOB, 1, &p, 0, (sort*const*)nullptr, nullptr));
}

unsigned csp_util::job2id(expr* j) {
    if (is_app_of(j, m_fid, OP_JS_JOB)) {
        return to_app(j)->get_decl()->get_parameter(0).get_int();
    }
    SASSERT(is_app_of(j, m_fid, OP_JS_START) || 
            is_app_of(j, m_fid, OP_JS_END) ||
            is_app_of(j, m_fid, OP_JS_JOB2RESOURCE));
    return job2id(to_app(j)->get_arg(0));
}

app* csp_util::mk_resource(unsigned r) {
    parameter p(r);
    return m.mk_const(m.mk_func_decl(m_fid, OP_JS_RESOURCE, 1, &p, 0, (sort*const*)nullptr, nullptr));
}

unsigned csp_util::resource2id(expr* r) {
    SASSERT(is_app_of(r, m_fid, OP_JS_RESOURCE));
    return to_app(r)->get_decl()->get_parameter(0).get_int();
}

app* csp_util::mk_start(unsigned j) { 
    app_ref job(mk_job(j), m);
    sort* js = m.get_sort(job);
    return m.mk_app(m.mk_func_decl(m_fid, OP_JS_START, 0, nullptr, 1, &js, nullptr), job);
}
        
app* csp_util::mk_end(unsigned j) {    
    app_ref job(mk_job(j), m);
    sort* js = m.get_sort(job);
    return m.mk_app(m.mk_func_decl(m_fid, OP_JS_END, 0, nullptr, 1, &js, nullptr), job);
}

app* csp_util::mk_job2resource(unsigned j) { 
    app_ref job(mk_job(j), m);
    sort* js = m.get_sort(job);
    return m.mk_app(m.mk_func_decl(m_fid, OP_JS_JOB2RESOURCE, 0, nullptr, 1, &js, nullptr), job);
}

app* csp_util::mk_makespan(unsigned r) {
    app_ref resource(mk_resource(r), m);
    sort* rs = m.get_sort(resource);
    return m.mk_app(m.mk_func_decl(m_fid, OP_JS_RESOURCE_MAKESPAN, 0, nullptr, 1, &rs, nullptr), resource);
}

bool csp_util::is_resource(expr* e, unsigned& r) {
    return is_app_of(e, m_fid, OP_JS_RESOURCE) && (r = resource2id(e), true);
}

bool csp_util::is_makespan(expr * e, unsigned& r) {
    return is_app_of(e, m_fid, OP_JS_RESOURCE_MAKESPAN) && is_resource(to_app(e)->get_arg(0), r);
}

bool csp_util::is_job(expr* e, unsigned& j) {
    return is_app_of(e, m_fid, OP_JS_JOB) && (j = job2id(e), true);
}

bool csp_util::is_job2resource(expr* e, unsigned& j) {
    return is_app_of(e, m_fid, OP_JS_JOB2RESOURCE) && (j = job2id(e), true);
}

bool csp_util::is_add_resource_available(expr * e, expr *& res, unsigned& loadpct, unsigned& cap_time, uint64_t& start, uint64_t& end, svector<symbol>& properties) {
    if (!is_app_of(e, m_fid, OP_JS_RESOURCE_AVAILABLE)) return false;
    res = to_app(e)->get_arg(0);
    arith_util a(m);
    rational r;
    if (!a.is_numeral(to_app(e)->get_arg(1), r) || !r.is_unsigned()) return false;
    loadpct = r.get_unsigned();
    if (!a.is_numeral(to_app(e)->get_arg(2), r) || !r.is_unsigned()) return false;
    cap_time = r.get_unsigned();
    if (!a.is_numeral(to_app(e)->get_arg(3), r) || !r.is_uint64()) return false;
    start = r.get_uint64();
    if (!a.is_numeral(to_app(e)->get_arg(4), r) || !r.is_uint64()) return false;
    end = r.get_uint64();
    if (!is_js_properties(to_app(e)->get_arg(5), properties)) return false;
    return true;
}

bool csp_util::is_add_job_resource(expr * e, expr *& job, expr*& res, unsigned& loadpct, uint64_t& capacity, uint64_t& end, svector<symbol>& properties) {
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
    if (!is_js_properties(to_app(e)->get_arg(5), properties)) return false;
    return true;
}

bool csp_util::is_set_preemptable(expr* e, expr *& job) {
    if (!is_app_of(e, m_fid, OP_JS_JOB_PREEMPTABLE)) return false;
    job = to_app(e)->get_arg(0);
    return true;
}

bool csp_util::is_js_properties(expr* e, svector<symbol>& properties) {
    if (!is_app_of(e, m_fid, OP_JS_PROPERTIES)) 
        return false;
    unsigned sz = to_app(e)->get_decl()->get_num_parameters();
    for (unsigned i = 0; i < sz; ++i) {
        properties.push_back(to_app(e)->get_decl()->get_parameter(i).get_symbol());
    }
    return true;
}

bool csp_util::is_job_goal(expr* e, js_job_goal& goal, unsigned& level, expr*& job) {
    if (!is_app_of(e, m_fid, OP_JS_JOB_GOAL)) 
        return false;
    SASSERT(2 == to_app(e)->get_decl()->get_num_parameters());
    SASSERT(1 == to_app(e)->get_num_args());
    symbol g = to_app(e)->get_decl()->get_parameter(0).get_symbol();
    level = to_app(e)->get_decl()->get_parameter(1).get_int();
    if (g == ":earliest-end-time" || g == "earliest-end-time")
        goal = JS_JOB_GOAL_EARLIEST_END_TIME;
    else if (g == ":latest-start-time" || g == "latest-start-time")
        goal = JS_JOB_GOAL_LATEST_START_TIME;
    else 
        return false;
    job = to_app(e)->get_arg(0);
    return true;
}

bool csp_util::is_objective(expr* e, js_optimization_objective& objective) {
    if (!is_app_of(e, m_fid, OP_JS_OBJECTIVE))
        return false;
    SASSERT(1 == to_app(e)->get_decl()->get_num_parameters());    
    symbol obj = to_app(e)->get_decl()->get_parameter(0).get_symbol();
    if (obj == ":duration" || obj == "duration")
        objective = JS_OBJECTIVE_DURATION;
    else if (obj == ":priority" || obj == "priority") 
        objective = JS_OBJECTIVE_PRIORITY;
    else 
        return false;
    return true;
}


