/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_solver.cpp

Abstract:

    Wraps smt::kernel as a solver for the external API and cmd_context.

Author:

    Leonardo (leonardo) 2012-10-21

Notes:

--*/
#include "solver/solver_na2as.h"
#include "smt/smt_kernel.h"
#include "ast/reg_decl_plugins.h"
#include "smt/params/smt_params.h"
#include "smt/params/smt_params_helper.hpp"
#include "solver/mus.h"
#include "ast/for_each_expr.h"
#include "ast/ast_smt2_pp.h"
#include "ast/func_decl_dependencies.h"
#include "util/dec_ref_util.h"

namespace {

    class smt_solver : public solver_na2as {

        struct cuber {
            smt_solver& m_solver;
            unsigned    m_round;
            expr_ref    m_result;
            cuber(smt_solver& s):
                m_solver(s),
                m_round(0),
                m_result(s.get_manager()) {}
            expr_ref cube() {
                switch (m_round) {
                case 0:
                    m_result = m_solver.m_context.next_cube();
                    break;
                case 1:
                    m_result = m_solver.get_manager().mk_not(m_result);
                    break;
                default:
                    m_result = m_solver.get_manager().mk_false();
                    break;
                }
                ++m_round;
                return m_result;
            }
        };

        smt_params           m_smt_params;
        smt::kernel          m_context;
        cuber*               m_cuber;
        symbol               m_logic;
        bool                 m_minimizing_core;
        bool                 m_core_extend_patterns;
        unsigned             m_core_extend_patterns_max_distance;
        bool                 m_core_extend_nonlocal_patterns;
        obj_map<expr, expr*> m_name2assertion;

    public:
        smt_solver(ast_manager & m, params_ref const & p, symbol const & l) :
            solver_na2as(m),
            m_smt_params(p),
            m_context(m, m_smt_params),
            m_cuber(nullptr),
            m_minimizing_core(false),
            m_core_extend_patterns(false),
            m_core_extend_patterns_max_distance(UINT_MAX),
            m_core_extend_nonlocal_patterns(false) {            
            m_logic = l;
            if (m_logic != symbol::null)
                m_context.set_logic(m_logic);
            updt_params(p);
        }

        solver * translate(ast_manager & m, params_ref const & p) override {
            ast_translation translator(get_manager(), m);

            smt_solver * result = alloc(smt_solver, m, p, m_logic);
            smt::kernel::copy(m_context, result->m_context);

            if (mc0()) 
                result->set_model_converter(mc0()->translate(translator));

            for (auto & kv : m_name2assertion) { 
                expr* val = translator(kv.m_value);
                expr* key = translator(kv.m_key);
                result->assert_expr(val, key);
            }

            return result;
        }

        ~smt_solver() override {
            dealloc(m_cuber);
            for (auto& kv : m_name2assertion) {
                get_manager().dec_ref(kv.m_key);
                get_manager().dec_ref(kv.m_value);
            }
        }

        void updt_params(params_ref const & p) override {
            solver::updt_params(p);
            m_smt_params.updt_params(solver::get_params());
            m_context.updt_params(solver::get_params());
            smt_params_helper smth(solver::get_params());
            m_core_extend_patterns = smth.core_extend_patterns();
            m_core_extend_patterns_max_distance = smth.core_extend_patterns_max_distance();
            m_core_extend_nonlocal_patterns = smth.core_extend_nonlocal_patterns();
        }

        params_ref m_params_save;
        smt_params m_smt_params_save;

        void push_params() override {
            m_params_save = params_ref();
            m_params_save.copy(solver::get_params());
            m_smt_params_save = m_smt_params;
        }

        void pop_params() override {
            m_smt_params = m_smt_params_save;
            solver::reset_params(m_params_save);
        }

        void collect_param_descrs(param_descrs & r) override {
            m_context.collect_param_descrs(r);
        }

        void collect_statistics(statistics & st) const override {
            m_context.collect_statistics(st);
        }

        lbool get_consequences_core(expr_ref_vector const& assumptions, expr_ref_vector const& vars, expr_ref_vector& conseq) override {
            expr_ref_vector unfixed(m_context.m());
            return m_context.get_consequences(assumptions, vars, conseq, unfixed);
        }

        lbool find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes) override {
            return m_context.find_mutexes(vars, mutexes);
        }

        void assert_expr_core(expr * t) override {
            m_context.assert_expr(t);
        }

        void assert_expr_core2(expr * t, expr * a) override {
            if (m_name2assertion.contains(a)) {
                throw default_exception("named assertion defined twice");
            }
            solver_na2as::assert_expr_core2(t, a);
            get_manager().inc_ref(t);
            get_manager().inc_ref(a);
            m_name2assertion.insert(a, t);
        }

        void push_core() override {
            m_context.push();
        }

        void pop_core(unsigned n) override {
            unsigned cur_sz = m_assumptions.size();
            if (n > 0 && cur_sz > 0) {
                unsigned lvl = m_scopes.size();
                SASSERT(n <= lvl);
                unsigned new_lvl = lvl - n;
                unsigned old_sz = m_scopes[new_lvl];
                for (unsigned i = cur_sz; i-- > old_sz; ) {
                    expr * key = m_assumptions.get(i);
                    expr * value = m_name2assertion.find(key);
                    m_name2assertion.erase(key);
                    m.dec_ref(value);
                    m.dec_ref(key);
                }
            }
            m_context.pop(n);
        }

        lbool check_sat_core2(unsigned num_assumptions, expr * const * assumptions) override {
            TRACE("solver_na2as", tout << "smt_solver::check_sat_core: " << num_assumptions << "\n";);
            return m_context.check(num_assumptions, assumptions);
        }


        lbool check_sat_cc_core(expr_ref_vector const& cube, vector<expr_ref_vector> const& clauses) override {
            return m_context.check(cube, clauses);
        }

        void get_levels(ptr_vector<expr> const& vars, unsigned_vector& depth) override {
            m_context.get_levels(vars, depth);
        }

        expr_ref_vector get_trail() override {
            return m_context.get_trail();
        }

        struct scoped_minimize_core {
            smt_solver& s;
            expr_ref_vector m_assumptions;
            scoped_minimize_core(smt_solver& s) : s(s), m_assumptions(s.m_assumptions) {
                s.m_minimizing_core = true;
                s.m_assumptions.reset();
            }

            ~scoped_minimize_core() {
                s.m_minimizing_core = false;
                s.m_assumptions.append(m_assumptions);
            }
        };

        void get_unsat_core(expr_ref_vector & r) override {
            unsigned sz = m_context.get_unsat_core_size();
            for (unsigned i = 0; i < sz; i++) {
                r.push_back(m_context.get_unsat_core_expr(i));
            }

            if (!m_minimizing_core && smt_params_helper(get_params()).core_minimize()) {
                scoped_minimize_core scm(*this);
                mus mus(*this);
                mus.add_soft(r.size(), r.c_ptr());
                expr_ref_vector r2(m);
                if (l_true == mus.get_mus(r2)) {
                    r.reset();
                    r.append(r2);
                }
            }

            if (m_core_extend_patterns)
                add_pattern_literals_to_core(r);
            if (m_core_extend_nonlocal_patterns)
                add_nonlocal_pattern_literals_to_core(r);
        }

        void get_model_core(model_ref & m) override {
            m_context.get_model(m);
        }

        proof * get_proof() override {
            return m_context.get_proof();
        }

        std::string reason_unknown() const override {
            return m_context.last_failure_as_string();
        }

        void set_reason_unknown(char const* msg) override {
            m_context.set_reason_unknown(msg);
        }

        void get_labels(svector<symbol> & r) override {
            buffer<symbol> tmp;
            m_context.get_relevant_labels(nullptr, tmp);
            r.append(tmp.size(), tmp.c_ptr());
        }

        ast_manager & get_manager() const override { return m_context.m(); }

        void set_progress_callback(progress_callback * callback) override {
            m_context.set_progress_callback(callback);
        }

        unsigned get_num_assertions() const override {
            return m_context.size();
        }

        expr * get_assertion(unsigned idx) const override {
            SASSERT(idx < get_num_assertions());
            return m_context.get_formula(idx);
        }

        expr_ref_vector cube(expr_ref_vector& vars, unsigned cutoff) override {
            ast_manager& m = get_manager();
            if (!m_cuber) {
                m_cuber = alloc(cuber, *this);
                // force propagation
                push_core();
                pop_core(1);
            }
            expr_ref result = m_cuber->cube();
            expr_ref_vector lits(m);
            if (m.is_false(result)) {
                dealloc(m_cuber);
                m_cuber = nullptr;
            }
            if (m.is_true(result)) {
                dealloc(m_cuber);
                m_cuber = nullptr;
                return lits;
            }
            lits.push_back(result);
            return lits;
        }

        struct collect_fds_proc {
            ast_manager & m;
            func_decl_set & m_fds;
            collect_fds_proc(ast_manager & m, func_decl_set & fds) :
                m(m), m_fds(fds) {
            }
            void operator()(var * n) {}
            void operator()(app * n) {
                func_decl * fd = n->get_decl();
                if (fd->get_family_id() == null_family_id)
                    m_fds.insert_if_not_there(fd);
            }
            void operator()(quantifier * n) {}
        };

        struct collect_pattern_fds_proc {
            ast_manager & m;
            expr_fast_mark1 m_visited;
            func_decl_set & m_fds;
            collect_pattern_fds_proc(ast_manager & m, func_decl_set & fds) :
                m(m), m_fds(fds) {
                m_visited.reset();
            }
            void operator()(var * n) {}
            void operator()(app * n) {}
            void operator()(quantifier * n) {
                collect_fds_proc p(m, m_fds);

                unsigned sz = n->get_num_patterns();
                for (unsigned i = 0; i < sz; i++)
                    quick_for_each_expr(p, m_visited, n->get_pattern(i));

                sz = n->get_num_no_patterns();
                for (unsigned i = 0; i < sz; i++)
                    quick_for_each_expr(p, m_visited, n->get_no_pattern(i));
            }
        };

        void collect_pattern_fds(expr_ref & e, func_decl_set & fds) {
            collect_pattern_fds_proc p(get_manager(), fds);
            expr_mark visited;
            for_each_expr(p, visited, e);
        }

        void compute_assrtn_fds(expr_ref_vector & core, vector<func_decl_set> & assrtn_fds) {
            assrtn_fds.resize(m_name2assertion.size());            
            unsigned i = 0;
            for (auto & kv : m_name2assertion) {
                if (!core.contains(kv.m_key)) {
                    collect_fds_proc p(m, assrtn_fds[i]);
                    expr_fast_mark1 visited;
                    quick_for_each_expr(p, visited, kv.m_value);
                }
                ++i;
            }
        }

        bool fds_intersect(func_decl_set & pattern_fds, func_decl_set & assrtn_fds) {
            for (func_decl * fd : pattern_fds) {
                if (assrtn_fds.contains(fd))
                    return true;
            }
            return false;
        }

        void add_pattern_literals_to_core(expr_ref_vector & core) {
            ast_manager & m = get_manager();
            expr_ref_vector new_core_literals(m);

            func_decl_set pattern_fds;
            vector<func_decl_set> assrtn_fds;

            for (unsigned d = 0; d < m_core_extend_patterns_max_distance; d++) {
                new_core_literals.reset();

                for (expr* c : core) {
                    expr_ref name(c, m);
                    SASSERT(m_name2assertion.contains(name));
                    expr_ref assrtn(m_name2assertion.find(name), m);
                    collect_pattern_fds(assrtn, pattern_fds);
                }

                if (!pattern_fds.empty()) {
                    if (assrtn_fds.empty())
                        compute_assrtn_fds(core, assrtn_fds);

                    unsigned i = 0;
                    for (auto & kv : m_name2assertion) {
                        if (!core.contains(kv.m_key) &&
                            fds_intersect(pattern_fds, assrtn_fds[i]))
                            new_core_literals.push_back(kv.m_key);
                        ++i;
                    }
                }

                core.append(new_core_literals.size(), new_core_literals.c_ptr());

                if (new_core_literals.empty())
                    break;
            }
        }

        struct collect_body_fds_proc {
            ast_manager & m;
            func_decl_set & m_fds;
            collect_body_fds_proc(ast_manager & m, func_decl_set & fds) :
                m(m), m_fds(fds) {
            }
            void operator()(var * n) {}
            void operator()(app * n) {}
            void operator()(quantifier * n) {
                collect_fds_proc p(m, m_fds);
                expr_fast_mark1 visited;
                quick_for_each_expr(p, visited, n->get_expr());
            }
        };

        void collect_body_func_decls(expr_ref & e, func_decl_set & fds) {
            ast_manager & m = get_manager();
            collect_body_fds_proc p(m, fds);
            expr_mark visited;
            for_each_expr(p, visited, e);
        }

        void add_nonlocal_pattern_literals_to_core(expr_ref_vector & core) {
            ast_manager & m = get_manager();
            for (auto const& kv : m_name2assertion) {
                expr_ref name(kv.m_key, m);
                expr_ref assrtn(kv.m_value, m);

                if (!core.contains(name)) {
                    func_decl_set pattern_fds, body_fds;
                    collect_pattern_fds(assrtn, pattern_fds);
                    collect_body_func_decls(assrtn, body_fds);

                    for (func_decl *fd : pattern_fds) {
                        if (!body_fds.contains(fd) && !core.contains(name)) {
                            core.push_back(name);
                            break;
                        }
                    }
                }
            }
        }
    };
}

solver * mk_smt_solver(ast_manager & m, params_ref const & p, symbol const & logic) {
    return alloc(smt_solver, m, p, logic);
}

namespace {
class smt_solver_factory : public solver_factory {
public:
    solver * operator()(ast_manager & m, params_ref const & p, bool proofs_enabled, bool models_enabled, bool unsat_core_enabled, symbol const & logic) override {
        return mk_smt_solver(m, p, logic);
    }
};
}

solver_factory * mk_smt_solver_factory() {
    return alloc(smt_solver_factory);
}

