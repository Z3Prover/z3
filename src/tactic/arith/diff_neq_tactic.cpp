/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    diff_neq_tactic.cpp

Abstract:

    Solver for integer problems that contains literals of the form
       k <= x
       x <= k
       x - y != k
    And all variables are bounded.   

Author:

    Leonardo de Moura (leonardo) 2012-02-07.

Revision History:

--*/
#include "tactic/tactical.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_smt2_pp.h"
#include "model/model.h"

class diff_neq_tactic : public tactic {
    struct imp {
        ast_manager &       m;
        arith_util          u;
        typedef unsigned    var;
        
        expr_ref_vector     m_var2expr;
        obj_map<expr, var>  m_expr2var;
        
        svector<int>        m_lower;
        svector<int>        m_upper;
        struct diseq {
            var m_y;
            int m_k;
            diseq(var y, int k):m_y(y), m_k(k) {}
        };
        typedef svector<diseq> diseqs;
        vector<diseqs>      m_var_diseqs;
        typedef svector<int> decision_stack;
        decision_stack       m_stack;
        
        bool                m_produce_models;
        rational            m_max_k;
        rational            m_max_neg_k;
        
        unsigned            m_num_conflicts;
        
        imp(ast_manager & _m, params_ref const & p):
            m(_m),
            u(m),
            m_var2expr(m) {
            updt_params(p);
        }
        
        void updt_params(params_ref const & p) {
            m_max_k          = rational(p.get_uint("diff_neq_max_k", 1024));
            m_max_neg_k      = -m_max_k;
            if (m_max_k >= rational(INT_MAX/2)) 
                m_max_k = rational(INT_MAX/2);
        }
                
        void throw_not_supported() {
            throw tactic_exception("goal is not diff neq");
        }
        
        unsigned num_vars() const {
            return m_upper.size();
        }
        
        var mk_var(expr * t) {
            SASSERT(is_uninterp_const(t));
            var x;
            if (m_expr2var.find(t, x))
                return x;
            x = m_upper.size();
            m_expr2var.insert(t, x);
            m_var2expr.push_back(t);
            m_lower.push_back(INT_MIN); // unknown
            m_upper.push_back(INT_MAX); // unknown
            m_var_diseqs.push_back(diseqs());
            return x;
        }
        
        void process_le(expr * lhs, expr * rhs) {
            if (!u.is_int(lhs))
                throw_not_supported();
            rational k;
            if (is_uninterp_const(lhs) && u.is_numeral(rhs, k) && m_max_neg_k <= k && k <= m_max_k) {
                var x  = mk_var(lhs);
                int _k = static_cast<int>(k.get_int64());
                m_upper[x] = std::min(m_upper[x], _k);
                
            }
            else if (is_uninterp_const(rhs) && u.is_numeral(lhs, k) && m_max_neg_k <= k && k <= m_max_k) {
                var x  = mk_var(rhs);
                int _k = static_cast<int>(k.get_int64()); 
                m_lower[x] = std::max(m_lower[x], _k);
            }
            else {
                throw_not_supported();
            }
        }
        
        // process t1 - t2 != k
        void process_neq_core(expr * t1, expr * t2, int k) {
            var x1 = mk_var(t1);
            var x2 = mk_var(t2);
            if (x1 == x2)
                throw_not_supported(); // must simplify first
            if (x1 < x2) {
                std::swap(x1, x2);
                k = -k;
            }
            m_var_diseqs[x1].push_back(diseq(x2, k));
        }
        
        void process_neq(expr * lhs, expr * rhs) {
            if (!u.is_int(lhs))
                throw_not_supported();
            if (is_uninterp_const(lhs) && is_uninterp_const(rhs)) {
                process_neq_core(lhs, rhs, 0);
                return;
            }
            if (u.is_numeral(lhs))
                std::swap(lhs, rhs);
            rational k;
            if (!u.is_numeral(rhs, k))
                throw_not_supported();
            if (!(m_max_neg_k <= k && k <= m_max_k))
                throw_not_supported();
            int _k = static_cast<int>(k.get_int64());
            expr * t1, * t2, * mt1, * mt2;
            if (u.is_add(lhs, t1, t2)) {
                if (is_uninterp_const(t1) && u.is_times_minus_one(t2, mt2) && is_uninterp_const(mt2))
                    process_neq_core(t1, mt2, _k);
                else if (is_uninterp_const(t2) && u.is_times_minus_one(t1, mt1) && is_uninterp_const(mt1))
                    process_neq_core(t2, mt1, _k);
                else
                    throw_not_supported();
            }
            else {
                throw_not_supported();
            }
        }
        
        // throws exception if contains unbounded variable
        void check_unbounded() {
            unsigned num = num_vars();
            for (var x = 0; x < num; x++) {
                if (m_lower[x] == INT_MIN || m_upper[x] == INT_MAX)
                    throw_not_supported();
                // possible extension: support bound normalization here
                if (m_lower[x] != 0) 
                    throw_not_supported(); // use bound normalizer
            }
        }
        
        void compile(goal const & g) {
            expr * lhs;
            expr * rhs;
            unsigned sz = g.size();
            for (unsigned i = 0; i < sz; i++) {
                expr * f = g.form(i);
                TRACE("diff_neq_tactic", tout << "processing: " << mk_ismt2_pp(f, m) << "\n";);
                if (u.is_le(f, lhs, rhs))
                    process_le(lhs, rhs);
                else if (u.is_ge(f, lhs, rhs))
                    process_le(rhs, lhs);
                else if (m.is_not(f, f) && m.is_eq(f, lhs, rhs))
                    process_neq(lhs, rhs);
                else
                    throw_not_supported();
            }
            check_unbounded();
        }
        
        void display(std::ostream & out) {
            unsigned num = num_vars();
            for (var x = 0; x < num; x++) {
                out << m_lower[x] << " <= " << mk_ismt2_pp(m_var2expr.get(x), m) << " <= " << m_upper[x] << "\n";
            }
            for (var x = 0; x < num; x++) {
                diseqs::iterator it  = m_var_diseqs[x].begin();
                diseqs::iterator end = m_var_diseqs[x].end();
                for (; it != end; ++it) {
                    out << mk_ismt2_pp(m_var2expr.get(x), m) << " != " << mk_ismt2_pp(m_var2expr.get(it->m_y), m) << " + " << it->m_k << "\n";
                }
            }
        }
        
        void display_model(std::ostream & out) {
            unsigned num = m_stack.size();
            for (var x = 0; x < num; x++) {
                out << mk_ismt2_pp(m_var2expr.get(x), m) << " := " << m_stack[x] << "\n";
            }
        }
        
        svector<bool>  m_forbidden;
        
        // make sure m_forbidden.size() > max upper bound
        void init_forbidden() {
            int max = 0;
            unsigned num = num_vars();
            for (var x = 0; x < num; x++) {
                if (m_upper[x] > max)
                    max = m_upper[x];
            }
            m_forbidden.reset();
            m_forbidden.resize(max+1, false);
        }
        
        // Return a value v s.t. v >= starting_at and v <= m_upper[x] and all diseqs in m_var_diseqs[x] are satisfied.
        // Return -1 if such value does not exist.
        int choose_value(var x, int starting_at) {
            int max = starting_at-1;
            int v   = starting_at;
            int upper = m_upper[x];
            if (starting_at > upper)
                return -1;
            diseqs const & ds = m_var_diseqs[x];
            diseqs::const_iterator it  = ds.begin();
            diseqs::const_iterator end = ds.end();
            for (; it != end; ++it) {
                int bad_v = m_stack[it->m_y] + it->m_k;
                if (bad_v < v)
                    continue;
                if (bad_v > upper)
                    continue;
                if (bad_v == v) {
                    while (true) {
                        v++;
                        if (v > upper)
                            return -1;
                        if (!m_forbidden[v])
                            break;
                        m_forbidden[v] = false;
                    }
                    continue;
                }
                SASSERT(bad_v > v && bad_v <= upper);
                m_forbidden[bad_v] = true;
                if (bad_v > max)
                    max = bad_v;
            }
            // reset forbidden
            for (int i = starting_at + 1; i <= max; i++)
                m_forbidden[i] = false;
            DEBUG_CODE({
                for (unsigned i = 0; i < m_forbidden.size(); i++) {
                    SASSERT(!m_forbidden[i]);
                }
            });
            return v;
        }
        
        bool extend_model(var x) {
            int v = choose_value(x, 0);
            if (v == -1)
                return false;
            m_stack.push_back(v);
            return true;
        }
        
        bool resolve_conflict() {
            m_num_conflicts++;
            while (!m_stack.empty()) {
                int v = m_stack.back();
                m_stack.pop_back();
                var x = m_stack.size();
                v = choose_value(x, v+1);
                if (v != -1) {
                    m_stack.push_back(v);
                    return true;
                }
            }
            return false;
        }
        
        bool search() {
            m_num_conflicts = 0;
            init_forbidden();
            unsigned nvars = num_vars();
            while (m_stack.size() < nvars) {
                if (m.canceled())
                    throw tactic_exception(m.limit().get_cancel_msg());
                TRACE("diff_neq_tactic", display_model(tout););
                var x = m_stack.size();
                if (extend_model(x))
                    continue;
                if (!resolve_conflict())
                    return false;
            }
            TRACE("diff_neq_tactic", display_model(tout););
            return true;
        }

        model * mk_model() {
            model * md = alloc(model, m);
            unsigned num = num_vars();
            SASSERT(m_stack.size() == num);
            for (var x = 0; x < num; x++) {
                func_decl * d = to_app(m_var2expr.get(x))->get_decl();
                md->register_decl(d, u.mk_numeral(rational(m_stack[x]), true));
            }
            return md;
        }

        void operator()(goal_ref const & g, 
                        goal_ref_buffer & result) {
            SASSERT(g->is_well_sorted());
            m_produce_models = g->models_enabled();
            result.reset();
            tactic_report report("diff-neq", *g);
            fail_if_proof_generation("diff-neq", g);
            fail_if_unsat_core_generation("diff-neq", g);
            if (g->inconsistent()) {
                result.push_back(g.get());
                return;
            }
            compile(*g);
            TRACE("diff_neq_tactic", g->display(tout); display(tout););
            bool r = search();
            report_tactic_progress(":conflicts", m_num_conflicts);
            if (r) {
                if (m_produce_models) {
                    g->add(model2model_converter(mk_model()));
                }
                g->reset();
            }
            else {
                g->assert_expr(m.mk_false());
            }
            g->inc_depth();
            result.push_back(g.get());
            TRACE("diff_neq", g->display(tout););
            SASSERT(g->is_well_sorted());
        }
    };

    imp *      m_imp;
    params_ref m_params;
public:
    diff_neq_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(diff_neq_tactic, m, m_params);
    }

    ~diff_neq_tactic() override {
        dealloc(m_imp);
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
        m_imp->updt_params(p);
    }

    void collect_param_descrs(param_descrs & r) override {
        r.insert("diff_neq_max_k", CPK_UINT, "(default: 1024) maximum variable upper bound for diff neq solver.");
    }

    void collect_statistics(statistics & st) const override {
        st.update("conflicts", m_imp->m_num_conflicts);
    }

    void reset_statistics() override {
        m_imp->m_num_conflicts = 0;
    }

    /**
       \brief Fix a DL variable in s to 0.
       If s is not really in the difference logic fragment, then this is a NOOP.
    */
    void operator()(goal_ref const & in, 
                    goal_ref_buffer & result) override {
        (*m_imp)(in, result);
    }
    
    void cleanup() override {
        imp * d = alloc(imp, m_imp->m, m_params);
        d->m_num_conflicts = m_imp->m_num_conflicts;
        std::swap(d, m_imp);        
        dealloc(d);
    }

};

tactic * mk_diff_neq_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(diff_neq_tactic, m, p));
}



