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
#include"solver_na2as.h"
#include"smt_kernel.h"
#include"reg_decl_plugins.h"
#include"smt_params.h"
#include"smt_params_helper.hpp"
#include"mus.h"
#include"for_each_expr.h"
#include"ast_smt2_pp.h"
#include"func_decl_dependencies.h"
#include"dec_ref_util.h"

namespace smt {

    class solver : public solver_na2as {
        smt_params           m_smt_params;
        params_ref           m_params;
        smt::kernel          m_context;
        progress_callback  * m_callback;
        symbol               m_logic;
        bool                 m_minimizing_core;
        bool                 m_core_extend_patterns;
        unsigned             m_core_extend_patterns_max_distance;
        bool                 m_core_extend_nonlocal_patterns;
        obj_map<expr, expr*> m_name2assertion;

    public:
        solver(ast_manager & m, params_ref const & p, symbol const & l) :
            solver_na2as(m),
            m_smt_params(p),
            m_params(p),
            m_context(m, m_smt_params),
            m_minimizing_core(false),
            m_core_extend_patterns(false),
            m_core_extend_patterns_max_distance(UINT_MAX),
            m_core_extend_nonlocal_patterns(false) {
            m_logic = l;
            if (m_logic != symbol::null)
                m_context.set_logic(m_logic);
            smt_params_helper smth(p);
            m_core_extend_patterns = smth.core_extend_patterns();
            m_core_extend_patterns_max_distance = smth.core_extend_patterns_max_distance();
            m_core_extend_nonlocal_patterns = smth.core_extend_nonlocal_patterns();
        }

        virtual solver * translate(ast_manager & m, params_ref const & p) {
            solver * result = alloc(solver, m, p, m_logic);
            smt::kernel::copy(m_context, result->m_context);

            ast_translation translator(get_manager(), m);
            obj_map<expr, expr*>::iterator it = m_name2assertion.begin();
            obj_map<expr, expr*>::iterator end = m_name2assertion.end();
            for (; it != end; it++)
                result->m_name2assertion.insert(translator(it->m_key),
                                                translator(it->m_value));

            return result;
        }

        virtual ~solver() {
            dec_ref_values(get_manager(), m_name2assertion);
        }

        virtual void updt_params(params_ref const & p) {
            m_smt_params.updt_params(p);
            m_params.copy(p);
            m_context.updt_params(p);
            smt_params_helper smth(p);
            m_core_extend_patterns = smth.core_extend_patterns();
            m_core_extend_patterns_max_distance = smth.core_extend_patterns_max_distance();
            m_core_extend_nonlocal_patterns = smth.core_extend_nonlocal_patterns();
        }

        virtual void collect_param_descrs(param_descrs & r) {
            m_context.collect_param_descrs(r);
        }

        virtual void collect_statistics(statistics & st) const {
            m_context.collect_statistics(st);
        }

        virtual lbool get_consequences_core(expr_ref_vector const& assumptions, expr_ref_vector const& vars, expr_ref_vector& conseq) {
            expr_ref_vector unfixed(m_context.m());
            return m_context.get_consequences(assumptions, vars, conseq, unfixed);
        }

        virtual lbool find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes) {
            return m_context.find_mutexes(vars, mutexes);
        }

        virtual void assert_expr(expr * t) {
            m_context.assert_expr(t);
        }

        virtual void assert_expr(expr * t, expr * a) {
            solver_na2as::assert_expr(t, a);
            SASSERT(!m_name2assertion.contains(a));
            get_manager().inc_ref(t);
            m_name2assertion.insert(a, t);
        }

        virtual void push_core() {
            m_context.push();
        }

        virtual void pop_core(unsigned n) {
            unsigned cur_sz = m_assumptions.size();
            if (n > 0 && cur_sz > 0) {
                unsigned lvl = m_scopes.size();
                SASSERT(n <= lvl);
                unsigned new_lvl = lvl - n;
                unsigned old_sz = m_scopes[new_lvl];
                for (unsigned i = cur_sz; i > old_sz; ) {
                    --i;
                    expr * key = m_assumptions[i].get();
                    SASSERT(m_name2assertion.contains(key));
                    expr * value = m_name2assertion.find(key);
                    m.dec_ref(value);
                    m_name2assertion.erase(key);
                }
            }
            m_context.pop(n);
        }

        virtual lbool check_sat_core(unsigned num_assumptions, expr * const * assumptions) {
            TRACE("solver_na2as", tout << "smt_solver::check_sat_core: " << num_assumptions << "\n";);
            return m_context.check(num_assumptions, assumptions);
        }

        struct scoped_minimize_core {
            solver& s;
            expr_ref_vector m_assumptions;
            scoped_minimize_core(solver& s) : s(s), m_assumptions(s.m_assumptions) {
                s.m_minimizing_core = true;
                s.m_assumptions.reset();
            }

            ~scoped_minimize_core() {
                s.m_minimizing_core = false;
                s.m_assumptions.append(m_assumptions);
            }
        };

        virtual void get_unsat_core(ptr_vector<expr> & r) {
            unsigned sz = m_context.get_unsat_core_size();
            for (unsigned i = 0; i < sz; i++) {
                r.push_back(m_context.get_unsat_core_expr(i));
            }

            if (m_minimizing_core && smt_params_helper(m_params).core_minimize()) {
                scoped_minimize_core scm(*this);
                mus mus(*this);
                mus.add_soft(r.size(), r.c_ptr());
                ptr_vector<expr> r2;
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

        virtual void get_model(model_ref & m) {
            m_context.get_model(m);
        }

        virtual proof * get_proof() {
            return m_context.get_proof();
        }

        virtual std::string reason_unknown() const {
            return m_context.last_failure_as_string();
        }

        virtual void set_reason_unknown(char const* msg) {
            m_context.set_reason_unknown(msg);
        }

        virtual void get_labels(svector<symbol> & r) {
            buffer<symbol> tmp;
            m_context.get_relevant_labels(0, tmp);
            r.append(tmp.size(), tmp.c_ptr());
        }

        virtual ast_manager & get_manager() const { return m_context.m(); }

        virtual void set_progress_callback(progress_callback * callback) {
            m_callback = callback;
            m_context.set_progress_callback(callback);
        }

        virtual unsigned get_num_assertions() const {
            return m_context.size();
        }

        virtual expr * get_assertion(unsigned idx) const {
            SASSERT(idx < get_num_assertions());
            return m_context.get_formulas()[idx];
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

        void compute_assrtn_fds(ptr_vector<expr> & core, vector<func_decl_set> & assrtn_fds) {
            assrtn_fds.resize(m_name2assertion.size());
            obj_map<expr, expr*>::iterator ait = m_name2assertion.begin();
            obj_map<expr, expr*>::iterator aend = m_name2assertion.end();
            for (unsigned i = 0; ait != aend; ait++, i++) {
                if (core.contains(ait->m_key))
                    continue;
                collect_fds_proc p(m, assrtn_fds[i]);
                expr_fast_mark1 visited;
                quick_for_each_expr(p, visited, ait->m_value);
            }
        }

        bool fds_intersect(func_decl_set & pattern_fds, func_decl_set & assrtn_fds) {
            func_decl_set::iterator it = pattern_fds.begin();
            func_decl_set::iterator end = pattern_fds.end();
            for (; it != end; it++) {
                func_decl * fd = *it;
                if (assrtn_fds.contains(fd))
                    return true;
            }
            return false;
        }

        void add_pattern_literals_to_core(ptr_vector<expr> & core) {
            ast_manager & m = get_manager();
            expr_ref_vector new_core_literals(m);

            func_decl_set pattern_fds;
            vector<func_decl_set> assrtn_fds;

            for (unsigned d = 0; d < m_core_extend_patterns_max_distance; d++) {
                new_core_literals.reset();

                unsigned sz = core.size();
                for (unsigned i = 0; i < sz; i++) {
                    expr_ref name(core[i], m);
                    SASSERT(m_name2assertion.contains(name));
                    expr_ref assrtn(m_name2assertion.find(name), m);
                    collect_pattern_fds(assrtn, pattern_fds);
                }

                if (!pattern_fds.empty()) {
                    if (assrtn_fds.empty())
                        compute_assrtn_fds(core, assrtn_fds);

                    obj_map<expr, expr*>::iterator ait = m_name2assertion.begin();
                    obj_map<expr, expr*>::iterator aend = m_name2assertion.end();
                    for (unsigned i = 0; ait != aend; ait++, i++) {
                        if (!core.contains(ait->m_key) &&
                            fds_intersect(pattern_fds, assrtn_fds[i]))
                            new_core_literals.push_back(ait->m_key);
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

        void add_nonlocal_pattern_literals_to_core(ptr_vector<expr> & core) {
            ast_manager & m = get_manager();

            obj_map<expr, expr*>::iterator it = m_name2assertion.begin();
            obj_map<expr, expr*>::iterator end = m_name2assertion.end();
            for (unsigned i = 0; it != end; it++, i++) {
                expr_ref name(it->m_key, m);
                expr_ref assrtn(it->m_value, m);

                if (!core.contains(name)) {
                    func_decl_set pattern_fds, body_fds;
                    collect_pattern_fds(assrtn, pattern_fds);
                    collect_body_func_decls(assrtn, body_fds);

                    func_decl_set::iterator pit = pattern_fds.begin();
                    func_decl_set::iterator pend= pattern_fds.end();
                    for (; pit != pend; pit++) {
                        func_decl * fd = *pit;
                        if (!body_fds.contains(fd)) {
                            core.insert(name);
                            break;
                        }
                    }
                }
            }
        }
    };
};

solver * mk_smt_solver(ast_manager & m, params_ref const & p, symbol const & logic) {
    return alloc(smt::solver, m, p, logic);
}

class smt_solver_factory : public solver_factory {
public:
    virtual solver * operator()(ast_manager & m, params_ref const & p, bool proofs_enabled, bool models_enabled, bool unsat_core_enabled, symbol const & logic) {
        return mk_smt_solver(m, p, logic);
    }
};

solver_factory * mk_smt_solver_factory() {
    return alloc(smt_solver_factory);
}

