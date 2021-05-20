/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    opt_solver.h

Abstract:

    Wraps smt::kernel as a solver for optimization

Author:

    Anh-Dung Phan (t-anphan) 2013-10-16

Notes:

    Based directly on smt_solver.
   
--*/
#pragma once

#include "util/inf_rational.h"
#include "util/inf_eps_rational.h"
#include "ast/ast.h"
#include "util/params.h"
#include "solver/solver_na2as.h"
#include "smt/smt_kernel.h"
#include "smt/params/smt_params.h"
#include "smt/smt_types.h"
#include "smt/theory_opt.h"
#include "tactic/generic_model_converter.h"

namespace opt {

    typedef inf_eps_rational<inf_rational> inf_eps;

    // Adjust bound bound |-> m_offset + (m_negate?-1:1)*bound
    class adjust_value {
        rational m_offset;
        bool     m_negate;
    public:
        adjust_value(rational const& offset, bool neg):
            m_offset(offset),
            m_negate(neg)
        {}
        adjust_value(): m_offset(0), m_negate(false) {}
        void set_offset(rational const& o) { m_offset = o; }
        void set_negate(bool neg) { m_negate = neg; }
        rational const& get_offset() const { return m_offset; }
        bool get_negate() { return m_negate; }
        inf_eps operator()(inf_eps const& r) const {
            inf_eps result = r;
            if (m_negate) result.neg();
            result += m_offset;
            return result;
        }
        rational operator()(rational const& r) const {
            rational result = r;
            if (m_negate) result.neg();
            result += m_offset;
            return result;
        }
    };


    class opt_solver : public solver_na2as {
    private:
        smt_params          m_params;
        smt::kernel         m_context;
        ast_manager&        m;
        generic_model_converter& m_fm;
        progress_callback * m_callback;
        symbol              m_logic;
        model_ref           m_last_model;
        svector<smt::theory_var>  m_objective_vars;
        vector<inf_eps>     m_objective_values;
        sref_vector<model>  m_models;
        expr_ref_vector     m_objective_terms;
        bool                m_dump_benchmarks;
        static unsigned     m_dump_count;
        statistics          m_stats;
        bool                m_first;
        bool                m_was_unknown;
    public:
        opt_solver(ast_manager & m, params_ref const & p, generic_model_converter& fm);
        ~opt_solver() override;

        solver* translate(ast_manager& m, params_ref const& p) override;
        void updt_params(params_ref const& p) override;
        void collect_param_descrs(param_descrs & r) override;
        void collect_statistics(statistics & st) const override;
        void assert_expr_core(expr * t) override;
        void push_core() override;
        void pop_core(unsigned n) override;
        lbool check_sat_core2(unsigned num_assumptions, expr * const * assumptions) override;
        void get_unsat_core(expr_ref_vector & r) override;
        void get_model_core(model_ref & _m) override;
        proof * get_proof() override;
        std::string reason_unknown() const override;
        void set_reason_unknown(char const* msg) override;
        void get_labels(svector<symbol> & r) override;
        void set_progress_callback(progress_callback * callback) override;
        unsigned get_num_assertions() const override;
        expr * get_assertion(unsigned idx) const override;
        ast_manager& get_manager() const override { return m; }
        lbool find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes) override;
        lbool preferred_sat(expr_ref_vector const& asms, vector<expr_ref_vector>& cores) override;
        void get_levels(ptr_vector<expr> const& vars, unsigned_vector& depth) override; 
        expr_ref_vector get_trail() override { return m_context.get_trail(); }
        expr_ref_vector cube(expr_ref_vector&, unsigned) override { return expr_ref_vector(m); }
        void set_phase(expr* e) override { m_context.set_phase(e); }
        phase* get_phase() override { return m_context.get_phase(); }
        void set_phase(phase* p) override { m_context.set_phase(p); }
        void move_to_front(expr* e) override { m_context.move_to_front(e); }

        void set_logic(symbol const& logic);

        smt::theory_var add_objective(app* term);
        void reset_objectives();
        bool maximize_objective(unsigned i, expr_ref& blocker);
        bool maximize_objectives1(expr_ref_vector& blockers);
        inf_eps const & saved_objective_value(unsigned obj_index);
        inf_eps current_objective_value(unsigned obj_index);
        model* get_model_idx(unsigned obj_index) { return m_models[obj_index]; }

        bool was_unknown() const { return m_was_unknown; }

        vector<inf_eps> const& get_objective_values();
        expr_ref mk_ge(unsigned obj_index, inf_eps const& val);

        static opt_solver& to_opt(solver& s);
        bool dump_benchmarks();

        smt::context& get_context() { return m_context.get_context(); } // used by weighted maxsat.
        void ensure_pb();
        
        smt::theory_opt& get_optimizer();

        void to_smt2_benchmark(std::ofstream & buffer, 
                               unsigned num_assumptions, expr * const * assumptions,
                               char const * name = "benchmarks", 
                               symbol const& logic = symbol::null, char const * status = "unknown", char const * attributes = "");

    private:
        bool bound_value(unsigned i, inf_eps& val);
        void set_model(unsigned i);
        lbool adjust_result(lbool r);
    };
}

