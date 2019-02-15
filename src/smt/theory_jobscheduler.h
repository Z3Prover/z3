/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    theory_jobscheduling.h

Abstract:

    Propagation solver for jobscheduling problems.
    It relies on an external module to tighten bounds of 
    job variables.

Author:

    Nikolaj Bjorner (nbjorner) 2018-09-08.

Revision History:

--*/
#pragma once

#include "util/uint_set.h"
#include "ast/csp_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "smt/smt_theory.h"

namespace smt {

    typedef uint64_t time_t;
    
    class theory_jobscheduler : public theory {
    public:
        typedef svector<symbol> properties;
    protected:

        struct job_resource {
            unsigned m_resource_id;   // id of resource
            time_t   m_capacity;      // amount of resource to use
            unsigned m_loadpct;       // assuming loadpct
            time_t   m_finite_capacity_end;   
            properties m_properties;
            job_resource(unsigned r, time_t cap, unsigned loadpct, time_t end, properties const& ps):
                m_resource_id(r), m_capacity(cap), m_loadpct(loadpct), m_finite_capacity_end(end), m_properties(ps) {}
        };

        struct job_time {
            unsigned m_job;
            time_t   m_time;
            job_time(unsigned j, time_t time): m_job(j), m_time(time) {}

            struct compare {
                bool operator()(job_time const& jt1, job_time const& jt2) const {
                    return jt1.m_time < jt2.m_time;
                }
            };
        };

        struct job_info {
            bool                 m_is_preemptable; // can job be pre-empted
            vector<job_resource> m_resources; // resources allowed to run job.
            u_map<unsigned>      m_resource2index; // resource to index into vector 
            enode*               m_job;
            enode*               m_start;
            enode*               m_end;
            enode*               m_job2resource;
            bool                 m_is_bound;
            job_info(): m_is_preemptable(false), m_job(nullptr), m_start(nullptr), m_end(nullptr), m_job2resource(nullptr), m_is_bound(false)  {}
        };

        struct res_available {
            unsigned   m_loadpct;
            time_t     m_start;
            time_t     m_end;
            properties m_properties;
            res_available(unsigned load_pct, time_t start, time_t end, properties const& ps):
                m_loadpct(load_pct),
                m_start(start),
                m_end(end),
                m_properties(ps)
            {}
            struct compare {
                bool operator()(res_available const& ra1, res_available const& ra2) const {
                    return ra1.m_start < ra2.m_start;
                }
            };
        };

        struct res_info {
            unsigned_vector       m_jobs;      // jobs allocated to run on resource
            vector<res_available> m_available; // time intervals where resource is available
            enode*                m_resource;
            enode*                m_makespan;
            res_info(): m_resource(nullptr), m_makespan(nullptr) {}
        };
        
        ast_manager&     m;
        csp_util         u;
        arith_util       a;
        vector<job_info> m_jobs;
        vector<res_info> m_resources;
        unsigned_vector  m_bound_jobs;
        unsigned         m_bound_qhead;
        struct scope {
            unsigned m_bound_jobs_lim;
            unsigned m_bound_qhead;
        };
        svector<scope> m_scopes;
        
    protected:

        theory_var mk_var(enode * n) override;        

        bool internalize_atom(app * atom, bool gate_ctx) override;

        bool internalize_term(app * term) override;

        void assign_eh(bool_var v, bool is_true) override {}

        void new_eq_eh(theory_var v1, theory_var v2) override;

        void new_diseq_eh(theory_var v1, theory_var v2) override;

        void push_scope_eh() override;

        void pop_scope_eh(unsigned num_scopes) override;

        final_check_status final_check_eh() override;

        bool can_propagate() override;

        void propagate() override;
        
    public:

        theory_jobscheduler(ast_manager& m);

        ~theory_jobscheduler() override {}
        
        void display(std::ostream & out) const override;
        
        void collect_statistics(::statistics & st) const override;

        bool include_func_interp(func_decl* f) override;

        void init_model(model_generator & m) override;

        model_value_proc * mk_value(enode * n, model_generator & mg) override;

        bool get_value(enode * n, expr_ref & r) override;

        theory * mk_fresh(context * new_ctx) override; 

        res_info& ensure_resource(unsigned r);
        job_info& ensure_job(unsigned j);

    public:
        // set up job/resource global constraints
        void set_preemptable(unsigned j, bool is_preemptable);
        void add_job_resource(unsigned j, unsigned r, unsigned loadpct, time_t cap, time_t end, properties const& ps);
        void add_resource_available(unsigned r, unsigned max_loadpct, time_t start, time_t end, properties const& ps);
        void add_done();

        // assignments
        time_t est(unsigned j);      // earliest start time of job j
        time_t lst(unsigned j);      // last start time
        time_t ect(unsigned j);      // earliest completion time
        time_t lct(unsigned j);      // last completion time
        time_t start(unsigned j);    // start time of job j
        time_t end(unsigned j);      // end time of job j
        time_t get_lo(expr* e);
        time_t get_up(expr* e);
        time_t get_value(expr* e);
        unsigned resource(unsigned j); // resource of job j

        // derived bounds
        time_t ect(unsigned j, unsigned r, time_t start);
        bool lst(unsigned j, unsigned r, time_t& t);
        
        bool resource_available(job_resource const& jr, res_available const& ra) const;
        bool first_available(job_resource const& jr, res_info const& ri, unsigned& idx) const;
        bool last_available(job_resource const& jr, res_info const& ri, unsigned& idx) const;

        time_t solve_for_start(unsigned load_pct, unsigned job_load_pct, time_t end, time_t cap);
        time_t solve_for_end(unsigned load_pct, unsigned job_load_pct, time_t start, time_t cap);
        time_t solve_for_capacity(unsigned load_pct, unsigned job_load_pct, time_t start, time_t end);

        // validate assignment
        void validate_assignment();
        bool resource_available(unsigned r, time_t t, unsigned& idx); // load available on resource r at time t.
        time_t capacity_used(unsigned j, unsigned r, time_t start, time_t end);        // capacity used between start and end

        job_resource const& get_job_resource(unsigned j, unsigned r) const;
        bool job_has_resource(unsigned j, unsigned r) const;

        // propagation
        void propagate_end_time(unsigned j, unsigned r);
        void propagate_job2resource(unsigned j, unsigned r);

        // final check constraints
        bool constrain_end_time_interval(unsigned j, unsigned r);
        bool constrain_resource_energy(unsigned r);
        bool split_job2resource(unsigned j);

        void assert_last_end_time(unsigned j, unsigned r, job_resource const& jr, literal eq);
        void assert_last_start_time(unsigned j, unsigned r, literal eq);
        void assert_first_start_time(unsigned j, unsigned r, literal eq);
        void assert_job_not_in_gap(unsigned j, unsigned r, unsigned idx, unsigned idx1, literal eq);
        void assert_job_non_preemptable(unsigned j, unsigned r, unsigned idx, unsigned idx1, literal eq);

        void block_job_overlap(unsigned r, uint_set const& jobs, unsigned last_job);

        class job_overlap {
            time_t m_start;
            vector<job_time> & m_starts, &m_ends;
            unsigned s_idx, e_idx; // index into starts/ends
            uint_set m_jobs;
        public:
            job_overlap(vector<job_time>& starts, vector<job_time>& ends);
            bool next();
            uint_set const& jobs() const { return m_jobs; }
        };

        // term builders
        literal mk_ge(expr* e, time_t t);
        expr* mk_ge_expr(expr* e, time_t t);
        literal mk_ge(enode* e, time_t t);
        literal mk_le(expr* e, time_t t);
        expr* mk_le_expr(expr* e, time_t t);
        literal mk_le(enode* e, time_t t);
        literal mk_le(enode* l, enode* r);
        literal mk_literal(expr* e);
        literal mk_eq_lit(enode * l, enode * r) { return mk_eq_lit(l->get_owner(), r->get_owner()); }
        literal mk_eq_lit(expr * l, expr * r);

        void internalize_cmd(expr* cmd);
        void unrecognized_argument(expr* arg) { invalid_argument("unrecognized argument ", arg); }
        void invalid_argument(char const* msg, expr* arg);

        std::ostream& display(std::ostream & out, res_info const& r) const;
        std::ostream& display(std::ostream & out, res_available const& r) const;
        std::ostream& display(std::ostream & out, job_info const& r) const;
        std::ostream& display(std::ostream & out, job_resource const& r) const;

    };    
};

