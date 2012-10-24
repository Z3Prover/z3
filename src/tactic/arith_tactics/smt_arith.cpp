/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    smt_arith.cpp

Abstract:

    Arithmetic solver for smt::solver
    
Author:

    Leonardo de Moura (leonardo) 2011-06-25.

Revision History:

--*/
#include"smt_arith.h"
#include"bound_propagator.h"
#include"linear_equation.h"
#include"mpq.h"
#include"mpq_inf.h"
#include"double_manager.h"
#include"small_object_allocator.h"
#include"arith_decl_plugin.h"
#include"ast_smt2_pp.h"
#include"assertion_set_strategy.h"
#include"statistics.h"
#include"lu.h"
#include"cooperate.h"
#include"model.h"

namespace smt {

    typedef unsigned var;

    class var_set {
        unsigned_vector m_var2pos;
        unsigned_vector m_vars;
    public:
        typedef unsigned_vector::const_iterator iterator;
        var_set() {}

        void reset() { 
            if (4 * m_vars.size() < m_var2pos.size()) {
                unsigned_vector::iterator it  = m_vars.begin();
                unsigned_vector::iterator end = m_vars.end();
                for (; it != end; ++it)
                    m_var2pos[*it] = UINT_MAX;
            }
            else {
                m_var2pos.reset(); 
            }
            m_vars.reset(); 
        }

        bool empty() const { return m_vars.empty(); }

        unsigned size() const { return m_vars.size(); }
        
        var operator[](unsigned idx) const { return m_vars[idx]; }
        
        bool contains(var x) const { 
            return x < m_var2pos.size() && m_var2pos[x] != UINT_MAX; 
        }
        
        void insert(var x) { 
            if (contains(x))
                return;
            m_var2pos.reserve(x+1, UINT_MAX);
            m_var2pos[x] = m_vars.size();
            m_vars.push_back(x);
            SASSERT(contains(x));
        }
        
        void erase(var x) {
            if (contains(x)) {
                unsigned pos = m_var2pos[x];
                SASSERT(m_vars[pos] == x);
                if (pos != m_vars.size() - 1) {
                    unsigned last_x = m_vars.back();
                    m_var2pos[last_x] = pos;
                    m_vars[pos] = last_x;
                }
                m_vars.pop_back();
                m_var2pos[x] = UINT_MAX;
            }
            SASSERT(!contains(x));
        }
        
        iterator begin() const { return m_vars.begin(); }

        iterator end() const { return m_vars.end(); }
    };

    struct arith::imp {
        typedef small_object_allocator allocator;
        typedef unsynch_mpq_manager numeral_manager;
        typedef unsynch_mpq_inf_manager numeral_inf_manager;
        typedef svector<mpq_inf> mpq_inf_vector;
        typedef numeral_buffer<mpq, unsynch_mpq_manager> mpq_buffer;
        typedef numeral_buffer<mpq_inf, unsynch_mpq_inf_manager> mpq_inf_buffer;
        typedef numeral_buffer<mpz, unsynch_mpq_manager> mpz_buffer;
        typedef svector<var> var_buffer;                          
        typedef ptr_vector<linear_equation> equations;
        typedef lu<double_manager>      lu_double;
        typedef lu<unsynch_mpq_manager> lu_mpq;
        typedef numeral_inf_manager::inf_kind inf_kind;

        class double_vector : public svector<double> {
        public:
            typedef double         numeral;
            typedef double_manager manager;
        };

#define null_var UINT_MAX

        // "handy" infinitesimals
#define pos_inf   numeral_inf_manager::POS
#define neg_inf   numeral_inf_manager::NEG
#define zero_inf  numeral_inf_manager::ZERO

        struct ineq_cnstr {
            var     m_x;
            mpq     m_k;
            double  m_approx_k;
            bool    m_lower;
            atom_id m_atom;
        };

        typedef svector<ineq_cnstr> ineq_cnstrs;
        typedef unsigned_vector     ineq_cnstr_ids;
        
        // track the position of a variable in a equation
        struct eq_occ {
            unsigned m_idx; // equation index
            unsigned m_pos; // position in the equation
            eq_occ(unsigned idx, unsigned pos):m_idx(idx), m_pos(pos) {}
        };

        typedef svector<eq_occ> eq_occs;

        ast_manager &           m;
        arith_util              m_util;
        expr_ref_vector         m_var2expr;
        obj_map<expr, var>      m_expr2var;

        allocator               m_allocator;
        numeral_manager         m_num_manager;
        numeral_inf_manager     m_num_inf_manager;
        double_manager          m_double_manager;
        equations               m_equations;
        vector<eq_occs>         m_eq_occs;
        lu_mpq                  m_lu_mpq;
        lu_double               m_lu_double;
        char_vector             m_eliminated;
        unsigned_vector         m_basic;  // var -> eq_idx, UINT_MAX if not basic, otherwise it is a value in [0, m_equations.size())
        unsigned_vector         m_inv_basic; // eq_idx -> var inverse of m_basic
        mpq_inf_buffer          m_values;
        mpq_inf_buffer          m_old_values;
        double_vector           m_approx_values;
        double_vector           m_old_approx_values;
        var_set                 m_updated;
        var_set                 m_approx_updated;
        var_set                 m_bad_vars;
        var_set                 m_int_bad_vars;
        linear_equation_manager m_eq_manager;
        bound_propagator        m_asserted_bounds;
        bound_propagator        m_bounds;
        unsigned                m_conflict_eq_idx; // != UINT_MAX if the corresponding get_row(m_conflict_eq_idx) is in conflict.
        ineq_cnstrs             m_ineq_cnstrs;
        ineq_cnstr_ids          m_atom2ineq_cnstr; // atom idx to ineq cnstr idx
        vector<ineq_cnstr_ids>  m_var_occs; // ineq_cnstrs that constain a variable
        mpq_buffer              m_mpq_buffer;
        mpz_buffer              m_mpz_buffer;
        var_buffer              m_var_buffer;
        
        typedef std::pair<var, linear_equation *> elim_var_info;
        typedef svector<elim_var_info> elim_vars;
        
        elim_vars               m_elim_vars;

        volatile bool           m_cancel;

        // Modes of operation for mk_feasible
        bool                    m_use_approx;   // use approximated values
        bool                    m_use_asserted; // consider only asserted bounds

        bool                    m_approx_forbidden; // disable approx mode when approximation gets lost trying to find feasible solution.
        
        // statistics
        unsigned                m_eliminated_vars;
        unsigned                m_lu_factorizations;
        unsigned                m_pivots;
        unsigned                m_approx_pivots;
        unsigned                m_max_l;
        unsigned                m_max_u;
        unsigned                m_branches;
        unsigned                m_cuts;

        // configuration
        unsigned                m_refactor_threshold;
        unsigned                m_blands_rule_factor;
        unsigned                m_approx_threshold_factor; // factor*num_eqs == max pivots to try when using approximated
        bool                    m_elim_vars_enabled;
        bool                    m_elim_int_vars_enabled;
        bool                    m_branch_vars_only; // do not branch on auxiliary variables
        bool                    m_cuts_enabled;

        // backtracking 
        struct scope {
            bool                m_bad_vars_empty;
            unsigned            m_conflict_eq_idx_old;
        };
        
        svector<scope>          m_scopes;

        // Data-structures for branch & bound
        unsigned_vector       m_bb_var;
        char_vector           m_bb_lower;
        char_vector           m_bb_first;
        mpq_buffer            m_bb_k;


        // -----------------------
        //
        // Basic
        //
        // -----------------------
        imp(ast_manager & _m, params_ref const & p):
            m(_m),
            m_util(m),
            m_var2expr(m),
            m_allocator("arith"),
            m_num_inf_manager(m_num_manager),
            m_double_manager(p),
            m_lu_mpq(m_num_manager, p),
            m_lu_double(m_double_manager, p),
            m_values(m_num_inf_manager),
            m_old_values(m_num_inf_manager),
            m_eq_manager(m_num_manager, m_allocator),
            m_asserted_bounds(m_num_manager, m_allocator, p),
            m_bounds(m_num_manager, m_allocator, p),
            m_mpq_buffer(m_num_manager),
            m_mpz_buffer(m_num_manager),
            m_bb_k(m_num_manager) {
            m_approx_forbidden = false;
            m_cancel = false;
            m_conflict_eq_idx = UINT_MAX;
            updt_params_core(p);
            reset_statistics();
            m_use_approx = false;
            set_mode_core(false, false);
        }

        ~imp() {
            del_equations();
            del_ineq_cnstrs();
            del_elim_vars();
        }
        
        void updt_params(params_ref const & p) {
            m_double_manager.updt_params(p);
            m_asserted_bounds.updt_params(p);
            m_bounds.updt_params(p);
            m_lu_mpq.updt_params(p);
            m_lu_double.updt_params(p);
            updt_params_core(p);
        }

        void updt_params_core(params_ref const & p) {
            m_refactor_threshold      = p.get_uint(":lu-refactor", 20);
            m_blands_rule_factor      = p.get_uint(":blands-rule-factor", 4);
            m_elim_vars_enabled       = p.get_bool(":arith-elim-vars", false);
            m_elim_int_vars_enabled   = p.get_bool(":arith-elim-int-vars", true);
            m_approx_threshold_factor = p.get_uint(":approx-max-pivots", 32);
            m_branch_vars_only        = p.get_bool(":arith-branch-vars-only", true);
            m_cuts_enabled            = p.get_bool(":arith-cuts", false);
        }

        void set_cancel(bool f) {
            m_cancel = f;
        }

        void reset_statistics() {
            m_eliminated_vars = 0;
            m_lu_factorizations = 0;
            m_pivots = 0;
            m_approx_pivots = 0;
            m_max_l  = 0;
            m_max_u  = 0;
            m_branches = 0;
            m_cuts = 0;
            m_bounds.reset_statistics();
        }

        void collect_statistics(statistics & st) const {
            st.update("elim tableau vars", m_eliminated_vars);
            st.update("LU factorizations", m_lu_factorizations);
            st.update("pivots", m_pivots);
            st.update("approx pivots", m_approx_pivots);
            st.update("max L", m_max_l);
            st.update("max U", m_max_u);
            st.update("bb decisions", m_branches);
            st.update("cuts", m_cuts);
            m_bounds.collect_statistics(st);
        }

        void checkpoint() {
            if (m_cancel)
                throw strategy_exception(STE_CANCELED_MSG);
            cooperate("arith");
        }

        unsigned scope_lvl() const {
            return m_scopes.size();
        }

        void del_equations() {
            equations::iterator it  = m_equations.begin();
            equations::iterator end = m_equations.end();
            for (; it != end; ++it)
                m_eq_manager.del(*it);
        }

        void del_ineq_cnstrs() {
            ineq_cnstrs::iterator it  = m_ineq_cnstrs.begin();
            ineq_cnstrs::iterator end = m_ineq_cnstrs.end();
            for (; it != end; ++it) {
                m_num_manager.del(it->m_k);
            }
        }

        void del_elim_vars() {
            elim_vars::iterator it  = m_elim_vars.begin();
            elim_vars::iterator end = m_elim_vars.end();
            for (; it != end; ++it) {
                m_eq_manager.del(it->second);
            }
        }

        bool is_int(var x) const { 
            return m_asserted_bounds.is_int(x); 
        }

        bool is_unconstrained(var x) const {
            return 
                !m_asserted_bounds.has_lower(x) && 
                !m_asserted_bounds.has_upper(x) && 
                m_var_occs[x].empty();
        }

        bool was_eliminated(var x) const {
            return m_eliminated[x] != 0;
        }

        bool basic(var x) const { 
            return m_basic[x] != UINT_MAX; 
        }

        bool nonbasic(var x) const {
            return m_basic[x] == UINT_MAX;
        }

        unsigned num_vars() const {
            return m_var2expr.size();
        }

        bound_propagator const & bp() const { return m_use_asserted ? m_asserted_bounds : m_bounds; }

        bound_propagator & bp() { return m_use_asserted ? m_asserted_bounds : m_bounds; }

        bool has_lower(var x) const { return bp().has_lower(x); }

        bool has_upper(var x) const { return bp().has_upper(x); }

#define MK_LOWER_METHOD(NAME, OP, NO_BOUND_RESULT)                                              \
        bool NAME(var x) const {                                                                \
            if (!bp().has_lower(x))                                                             \
                return NO_BOUND_RESULT;                                                         \
            if (m_use_approx) {                                                                 \
                return m_double_manager.OP(m_approx_values[x], bp().approx_lower(x));           \
            }                                                                                   \
            else {                                                                              \
                bool strict;                                                                    \
                mpq const & l = bp().lower(x, strict);                                          \
                return m_num_inf_manager.OP(m_values[x], l, strict ? pos_inf : zero_inf);       \
            }                                                                                   \
        }

#define MK_UPPER_METHOD(NAME, OP, NO_BOUND_RESULT)                                              \
        bool NAME(var x) const {                                                                \
            if (!bp().has_upper(x))                                                             \
                return NO_BOUND_RESULT;                                                         \
            if (m_use_approx) {                                                                 \
                return m_double_manager.OP(m_approx_values[x], bp().approx_upper(x));           \
            }                                                                                   \
            else {                                                                              \
                bool strict;                                                                    \
                mpq const & u = bp().upper(x, strict);                                          \
                return m_num_inf_manager.OP(m_values[x], u, strict ? neg_inf : zero_inf);       \
            }                                                                                   \
        }
       
        MK_LOWER_METHOD(at_lower, eq, false);
        MK_LOWER_METHOD(below_lower, lt, false);
        MK_LOWER_METHOD(above_lower, gt, true);
        MK_UPPER_METHOD(at_upper, eq, false);
        MK_UPPER_METHOD(above_upper, gt, false);
        MK_UPPER_METHOD(below_upper, lt, true);

        void save_value(var x) {
            SASSERT(!m_use_approx);
            if (!m_updated.contains(x)) {
                m_updated.insert(x);
                m_num_inf_manager.set(m_old_values[x], m_values[x]);
            }
        }

        void save_approx_value(var x) {
            SASSERT(m_use_approx);
            if (!m_approx_updated.contains(x)) {
                m_approx_updated.insert(x);
                m_old_approx_values[x] = m_approx_values[x];
            }
        }
        
        bool int_feasible(var x) const {
            return !is_int(x) || m_num_inf_manager.is_int(m_values[x]);
        }

        void check_int(var x) {
            if (!int_feasible(x))
                m_int_bad_vars.insert(x);
        }

        void set_value(var x, mpq_inf const & val) {
            SASSERT(!m_use_approx);
            save_value(x);
            m_num_inf_manager.set(m_values[x], val);
            check_int(x);
        }

        void set_value(var x, mpq const & val, inf_kind k) {
            SASSERT(!m_use_approx);
            save_value(x);
            m_num_inf_manager.set(m_values[x], val, k);
            check_int(x);
        }

        void set_value(var x, double val) {
            SASSERT(m_use_approx);
            save_approx_value(x);
            m_approx_values[x] = val;
        }

        void acc_value(var x, mpq_inf const & delta) {
            SASSERT(!m_use_approx);
            save_value(x);
            m_num_inf_manager.add(m_values[x], delta, m_values[x]);
            check_int(x);
        }

        void acc_value(var x, double val) {
            SASSERT(m_use_approx);
            save_approx_value(x);
            m_approx_values[x] += val;
            if (m_double_manager.is_zero(m_approx_values[x]))
                m_approx_values[x] = 0.0;
        }

        /**
           \brief Assign x to its lower bound
        */
        void lower2value(var x) {
            if (m_use_approx) {
                set_value(x, bp().approx_lower(x));
            }
            else {
                bool strict;
                mpq const & l = bp().lower(x, strict);
                set_value(x, l, strict ? pos_inf : zero_inf);
            }
        }
        
        /**
           \brief Assign x to its upper bound
        */
        void upper2value(var x) {
            if (m_use_approx) {
                set_value(x, bp().approx_upper(x));
            }
            else {
                bool strict;
                mpq const & u = bp().upper(x, strict);
                set_value(x, u, strict ? neg_inf : zero_inf);
            }
        }

        // -----------------------
        //
        // Model Generation
        //
        // -----------------------

        void update_epsilon(mpq_inf const & l, mpq_inf const & u, mpq & epsilon) {
            numeral_manager & nm = m_num_manager;
            if (nm.lt(l.first, u.first) && nm.gt(l.second, u.second)) {
                mpq new_epsilon;
                mpq tmp;
                nm.sub(u.first, l.first, new_epsilon);
                nm.sub(l.second, u.second, tmp);
                nm.div(new_epsilon, tmp, new_epsilon);
                if (nm.lt(new_epsilon, epsilon))
                    nm.swap(new_epsilon, epsilon);
                nm.del(new_epsilon);
                nm.del(tmp);
            }
            SASSERT(nm.is_pos(epsilon));
        }
            
        void compute_epsilon(mpq & epsilon) {
            m_num_manager.set(epsilon, 1);
            mpq_inf v;
            mpq k;
            unsigned num = num_vars();
            for (unsigned x = 0; x < num; x++) {
                bool strict; unsigned ts;
                if (m_bounds.lower(x, k, strict, ts)) {
                    m_num_inf_manager.set(v, k, strict ? pos_inf : zero_inf);
                    update_epsilon(v, m_values[x], epsilon);
                }
                if (m_bounds.upper(x, k, strict, ts)) {
                    m_num_inf_manager.set(v, k, strict ? neg_inf : zero_inf);
                    update_epsilon(m_values[x], v, epsilon);
                }
            }
        }

        void update_elim_vars_assignment() {
            mpq_inf val;
            mpq_inf tmp;
            mpq inv_a;
            unsigned i = m_elim_vars.size();
            while (i > 0) {
                --i;
                elim_var_info & info = m_elim_vars[i];
                m_num_inf_manager.reset(val);
                var x = info.first;
                unsigned x_pos = UINT_MAX;
                linear_equation const & eq = *(info.second);
                unsigned sz = eq.size();
                for (unsigned j = 0; j < sz; j++) {
                    var x_j = eq.x(j);
                    if (x_j == x) {
                        x_pos = j;
                        continue;
                    }
                    m_num_inf_manager.mul(m_values[x_j], eq.a(j), tmp);
                    m_num_inf_manager.add(val, tmp, val);
                }
                SASSERT(x_pos != UINT_MAX);
                m_num_manager.set(inv_a, eq.a(x_pos));
                m_num_manager.inv(inv_a);
                m_num_inf_manager.mul(val, inv_a, val);
                m_num_inf_manager.neg(val);
                m_num_inf_manager.set(m_values[x], val);
            }
            m_num_inf_manager.del(val);
            m_num_inf_manager.del(tmp);
            m_num_manager.del(inv_a);
        }

        void mk_model(model * md) {
            // 
            update_elim_vars_assignment();
            numeral_manager & nm = m_num_manager;
            mpq epsilon;
            mpq val;
            compute_epsilon(epsilon);
            for (unsigned x = 0; x < num_vars(); x++) {
                expr * t = m_var2expr.get(x);
                if (t == 0)
                    continue;
                if (!is_uninterp_const(t))
                    continue;
                nm.set(val, m_values[x].first);
                nm.addmul(val, m_values[x].second, epsilon, val);
                func_decl * d = to_app(t)->get_decl();
                md->register_decl(d, m_util.mk_numeral(rational(val), is_int(x)));
            }
            nm.del(epsilon);
            nm.del(val);
        }

        // -----------------------
        //
        // Backtracking
        //
        // -----------------------

        void push() {
            m_scopes.push_back(scope());
            scope & s = m_scopes.back();
            s.m_bad_vars_empty = m_bad_vars.empty();
            s.m_conflict_eq_idx_old = m_conflict_eq_idx;
            m_bounds.push();
            m_asserted_bounds.push();
            SASSERT(m_bounds.scope_lvl() == scope_lvl());
            SASSERT(m_asserted_bounds.scope_lvl() == scope_lvl());
        }

        void pop(unsigned num_scopes) {
            unsigned lvl     = scope_lvl();
            SASSERT(num_scopes <= lvl);
            unsigned new_lvl = lvl - num_scopes;
            scope & s        = m_scopes[new_lvl];
            bool bad_vars_empty = s.m_bad_vars_empty;
            m_conflict_eq_idx = s.m_conflict_eq_idx_old;
            m_scopes.shrink(new_lvl);
            m_bounds.pop(num_scopes);
            m_asserted_bounds.pop(num_scopes);
            if (!bad_vars_empty)
                reset_bad_vars();
            SASSERT(m_bounds.scope_lvl() == scope_lvl());
            SASSERT(m_asserted_bounds.scope_lvl() == scope_lvl());
        }

        // -----------------------
        //
        // Compilation
        //
        // -----------------------

        var mk_var(expr * t) {
            var x;
            if (t != 0) {
                if (m_util.is_to_real(t))
                    t = to_app(t)->get_arg(0);
                if (m_expr2var.find(t, x))
                    return x;
            }
            x = m_var2expr.size();
            m_var2expr.push_back(t);
            bool is_int = true;
            if (t != 0) {
                m_expr2var.insert(t, x);
                is_int = m_util.is_int(t);
            }
            m_eliminated.push_back(false);
            m_basic.push_back(UINT_MAX);
            m_values.push_back(mpq_inf());
            m_old_values.push_back(mpq_inf());
            m_approx_values.push_back(0.0);
            m_old_approx_values.push_back(0.0);
            m_asserted_bounds.mk_var(x, is_int);
            m_bounds.mk_var(x, is_int);
            m_var_occs.push_back(ineq_cnstr_ids());
            return x;
        }
        
        void expr2lp(expr * t, mpq_buffer & as, var_buffer & xs) {
            mpq c_mpq_val;
            if (m_util.is_add(t)) {
                rational c_val;
                unsigned num = to_app(t)->get_num_args();
                for (unsigned i = 0; i < num; i++) {
                    expr * mon = to_app(t)->get_arg(i);
                    expr * c, * x;
                    if (m_util.is_mul(mon, c, x) && m_util.is_numeral(c, c_val)) {
                        m_num_manager.set(c_mpq_val, c_val.to_mpq());
                        as.push_back(c_mpq_val);
                        xs.push_back(mk_var(x));
                    }
                    else {
                        as.push_back(mpq(1));
                        xs.push_back(mk_var(mon));
                    }
                }
            }
            else {
                as.push_back(mpq(1));
                xs.push_back(mk_var(t));
            }
            m_num_manager.del(c_mpq_val);
        }

        var mk_lp(expr * t) {
            if (m_util.is_to_real(t))
                t = to_app(t)->get_arg(0);
            var x;
            if (m_expr2var.find(t, x))
                return x;

            x = mk_var(t);
            if (m_util.is_add(t)) {
                m_mpq_buffer.reset();
                m_var_buffer.reset();
                expr2lp(t, m_mpq_buffer, m_var_buffer);
                m_mpq_buffer.push_back(mpq(-1));
                m_var_buffer.push_back(x);
                linear_equation * new_eq = m_eq_manager.mk(m_mpq_buffer.size(), m_mpq_buffer.c_ptr(), m_var_buffer.c_ptr(), true);
                SASSERT(new_eq);
                unsigned eq_idx = m_equations.size();
                m_basic[x] = eq_idx;
                m_inv_basic.push_back(x);
                m_equations.push_back(new_eq);
                SASSERT(m_inv_basic.size() == m_equations.size());
                SASSERT(basic(x));
            }
            return x;
        }

        void mk_ineq_cnstr(var x, mpq const & k, bool lower, atom_id p) {
            unsigned cnstr_id = m_ineq_cnstrs.size();
            m_ineq_cnstrs.push_back(ineq_cnstr());
            ineq_cnstr & cnstr = m_ineq_cnstrs.back();
            cnstr.m_x = x;
            m_num_manager.set(cnstr.m_k, k);
            cnstr.m_approx_k = m_num_manager.get_double(k);
            cnstr.m_lower = lower;
            cnstr.m_atom  = p;
            m_atom2ineq_cnstr.reserve(p+1, UINT_MAX);
            m_atom2ineq_cnstr[p] = cnstr_id;
            m_var_occs[x].push_back(cnstr_id);
        }

        void mk_ineq(expr * t, bool neg, atom_id p) {
            TRACE("mk_ineq", tout << "mk_ineq, neg: " << neg << ", p: " << p << "\n" << mk_ismt2_pp(t, m) << "\n";);
            SASSERT(m_util.is_le(t) || m_util.is_ge(t));
            SASSERT(!neg || p == null_atom_id);

            bool strict = false;
            bool le;
            if (m_util.is_le(t)) {
                if (neg) {
                    le = false;
                    strict = true;
                }
                else {
                    le = true;
                }
            }
            else {
                SASSERT(m_util.is_ge(t));
                if (neg) {
                    le = true;
                    strict = true;
                }
                else {
                    le = false;
                }
            }
            expr * lhs = to_app(t)->get_arg(0);
            expr * rhs = to_app(t)->get_arg(1);

            SASSERT(m_util.is_numeral(rhs));
            rational c;
            m_util.is_numeral(rhs, c);
            
            var x = mk_lp(lhs);
            mpq c_prime;
            m_num_manager.set(c_prime, c.to_mpq());
            TRACE("mk_ineq", tout << "le: " << le << ", strict: " << strict << ", c: " << c << ", c_prime: " << 
                  m_num_manager.to_string(c_prime) << "\n";);
            
            if (p == null_atom_id) {
                // inequality is an axiom
                if (le) 
                    assert_upper(x, c_prime, strict);
                else 
                    assert_lower(x, c_prime, strict);
            }
            else {
                SASSERT(!strict);
                mk_ineq_cnstr(x, c_prime, !le, p);
            }
            m_num_manager.del(c_prime);
        }

        void assert_upper(var x, mpq const & k, bool strict) {
            m_bounds.assert_upper(x, k, strict);
            m_asserted_bounds.assert_upper(x, k, strict);
            if (above_upper(x))
                m_bad_vars.insert(x);
        }

        void assert_lower(var x, mpq const & k, bool strict) {
            m_bounds.assert_lower(x, k, strict);
            m_asserted_bounds.assert_lower(x, k, strict);
            if (below_lower(x))
                m_bad_vars.insert(x);
        }

        // -----------------------
        //
        // Approximate <-> Precise
        //
        // -----------------------

        /**
           \brief "Copy" nonbasic m_values to m_approx_values
        */
        void mpq2double_nonbasic_values() {
            unsigned num = num_vars();
            for (unsigned x = 0; x < num; x++) {
                if (nonbasic(x))
                    m_approx_values[x] = m_num_inf_manager.get_double(m_values[x]);
            }
        }

        /**
           \brief "Copy" nonbasic m_approx_values to m_values.
           It actually checks whether m_approx_values[x] is at lower or uppers,
           and copy the corresponding value.
        */
        void double2mpq_nonbasic_values() {
            unsigned num = num_vars();
            for (unsigned x = 0; x < num; x++) {
                if (nonbasic(x)) {
                    if (at_lower(x)) {
                        bool strict;
                        mpq const & l = bp().lower(x, strict);
                        m_num_inf_manager.set(m_values[x], l, strict ? pos_inf : zero_inf);
                    }
                    else if (at_upper(x)) {
                        bool strict;
                        mpq const & u = bp().upper(x, strict);
                        m_num_inf_manager.set(m_values[x], u, strict ? neg_inf : zero_inf);
                    }
                    else {
                        m_num_inf_manager.set(m_values[x], 0);
                    }
                }
            }
        }

        /**
           \brief Set the value of the basic variables using the value of the non-basic ones.
        */
        template<typename LU, typename Values, typename NumInfMng>
        void update_basic_values(LU & _lu, Values & values, NumInfMng & infm) {
            unsigned num = m_equations.size();
            typename LU::dense_vector & row = _lu.get_tmp_row(num_vars());
            typename NumInfMng::numeral val;
            typename NumInfMng::numeral aux;
            typename LU::manager & nm = _lu.m();
            for (unsigned eq_idx = 0; eq_idx < num; eq_idx++) {
                var x_b = m_inv_basic[eq_idx];
                row.reset();
                get_row(_lu, eq_idx, row, true, m_use_asserted, true);
                infm.reset(val);
                typename LU::dense_vector::iterator it  = row.begin_non_zeros();
                typename LU::dense_vector::iterator end = row.end_non_zeros();
                for (; it != end; ++it) {
                    var x_n = *it;
                    if (nm.is_zero(row[x_n])) 
                        continue;
                    infm.mul(values[x_n], row[x_n], aux);
                    infm.add(val, aux, val);
                }
                if (infm.is_zero(val)) {
                    infm.set(values[x_b], 0);
                }
                else {
                    infm.neg(val);
                    infm.swap(values[x_b], val);
                }
            }
            infm.del(val);
            infm.del(aux);
        }

        void update_mpq_basic_values() {
            update_basic_values(m_lu_mpq, m_values, m_num_inf_manager);
        }

        void update_double_basic_values() {
            update_basic_values(m_lu_double, m_approx_values, m_double_manager);
        }

        /**
           \brief Faster version of update_basic_values. Instead of extracting rows,
           I comput the Column C = N*V_n, where N is the matrix containing the coefficient of the non-basic variables,
           and V_n is the assignment of the non_basic variables. Then, I solve Ax = C
           The resultant column x is the assignment for the basic variables.
           
           The assignment is a mpq_inf, so the update is performed in two steps.
           inf == true, the infinitesimal part is updated,
           inf == false, the rational part is updated
        */
        void fast_update_basic_values_mpq(bool inf) {
            lu_mpq::dense_vector & C = m_lu_mpq.get_tmp_col();
            C.reset();
            mpq aux;
            // 1. Compute column C'
            unsigned num = m_equations.size();
            for (unsigned eq_idx = 0; eq_idx < num; eq_idx++) {
                mpq & c_i = C.get(eq_idx);
                linear_equation const & eq = *(m_equations[eq_idx]);
                unsigned sz = eq.size();
                for (unsigned i = 0; i < sz; i++) {
                    var x = eq.x(i);
                    if (basic(x)) 
                        continue;
                    if (inf)
                        m_num_manager.mul(eq.a(i), m_values[x].second, aux);
                    else
                        m_num_manager.mul(eq.a(i), m_values[x].first, aux);
                    m_num_manager.add(c_i, aux, c_i);
                }
            }
            TRACE("update_basic_values", tout << "inf: " << inf << " "; C.display_non_zeros(tout); tout << "\n";);
            // 2. Solve
            m_lu_mpq.solve_Ax_eq_y(C);
            C.elim_zeros();
            // 3. Update basic variable assignment
            for (unsigned eq_idx = 0; eq_idx < num; eq_idx++) {
                var x_b = m_inv_basic[eq_idx];
                mpq & c_i = C.get(eq_idx);
                m_num_manager.neg(c_i);
                TRACE("update_basic_values", tout << "inf: " << inf << " x" << x_b << " " << m_num_manager.to_string(c_i) << "\n";);
                if (inf)
                    m_num_manager.swap(m_values[x_b].second, c_i);
                else
                    m_num_manager.swap(m_values[x_b].first, c_i);
            }
            m_num_manager.del(aux);
        }

        void fast_update_mpq_basic_values() {
            fast_update_basic_values_mpq(false);
            fast_update_basic_values_mpq(true);
            SASSERT(check_eqs_satisfied_core()); // use core to make sure it will be checked even when m_use_approx = false
        }

        void fast_update_double_basic_values() {
            lu_double::dense_vector & C = m_lu_double.get_tmp_col();
            // 1. Compute column C'
            unsigned num = m_equations.size();
            for (unsigned eq_idx = 0; eq_idx < num; eq_idx++) {
                double & c_i = C.get(eq_idx);
                c_i = 0.0;
                linear_equation const & eq = *(m_equations[eq_idx]);
                unsigned sz = eq.size();
                for (unsigned i = 0; i < sz; i++) {
                    var x = eq.x(i);
                    if (basic(x)) 
                        continue;
                    c_i += eq.approx_a(i) * m_approx_values[x];
                }
            }
            TRACE("update_basic_values", C.display_non_zeros(tout); tout << "\n";);
            // 2. Solve
            m_lu_double.solve_Ax_eq_y(C);
            C.elim_zeros();
            // 3. Update basic variable assignment
            for (unsigned eq_idx = 0; eq_idx < num; eq_idx++) {
                var x_b = m_inv_basic[eq_idx];
                m_approx_values[x_b] = -C[eq_idx];
            }
        }
   
        void reset_bad_vars() {
            m_bad_vars.reset();
            unsigned num = num_vars();
            for (var x = 0; x < num; x++) {
                if (below_lower(x) || above_upper(x)) 
                    m_bad_vars.insert(x);
            }
        }

        void reset_int_bad_vars() {
            m_int_bad_vars.reset();
            unsigned num = num_vars();
            for (var x = 0; x < num; x++) {
                check_int(x);
            }
        }

        void set_mode_core(bool use_approx, bool use_asserted) {
            if (m_use_approx != use_approx) {
                if (use_approx) {
                    init_lu_double();
                    mpq2double_nonbasic_values();
                    // update_double_basic_values();                    
                    fast_update_double_basic_values();
                }
                else {
                    init_lu_mpq();
                    double2mpq_nonbasic_values();
                    // update_mpq_basic_values();
                    fast_update_mpq_basic_values();
                }
            }
            m_approx_updated.reset();
            m_updated.reset();
            m_use_approx   = use_approx;
            m_use_asserted = use_asserted;
            reset_bad_vars();
            if (!m_use_approx)
                reset_int_bad_vars();
        }

        void set_mode(bool use_approx, bool use_asserted) {
            if (use_approx == m_use_approx && use_asserted == m_use_asserted)
                return;
            set_mode_core(use_approx, use_asserted);
            TRACE("set_mode", display(tout););
        }

        // -----------------------
        //
        // Simplex & make_feasible
        //
        // -----------------------

        template<typename LU>
        void update_lu_stats(LU const & _lu) {
            unsigned l_sz = _lu.L_size();
            unsigned u_sz = _lu.U_size();
            if (l_sz > m_max_l)
                m_max_l = l_sz;
            if (u_sz > m_max_u)
                m_max_u = u_sz;
        }
        
        template<typename LU>
        void init_lu_core(LU & _lu) {
            m_lu_factorizations++;
            TRACE("arith_lu", display(tout););
            typename LU::numeral a;
            unsigned num_eqs = m_equations.size();
            _lu.init(num_eqs);
            for (unsigned i = 0; i < num_eqs; i++) {
#ifdef Z3DEBUG
                unsigned num_entries_added = 0;
#endif
                linear_equation const & eq = *(m_equations[i]);
                unsigned sz = eq.size();
                for (unsigned j = 0; j < sz; j++) {
                    var x = eq.x(j);
                    if (basic(x)) {
                        eq.get_a(_lu.m(), j, a);
                        _lu.add_entry(a, m_basic[x]);
                        DEBUG_CODE(num_entries_added++;);
                    }
                }
                SASSERT(num_entries_added <= num_eqs);
                _lu.end_row();
            }
            _lu.m().del(a);
            _lu.fact();
            update_lu_stats(_lu);
            TRACE("init_lu", display(tout););
        }

        void init_lu_double() { init_lu_core(m_lu_double);  }
        void init_lu_mpq() { init_lu_core(m_lu_mpq); }
        
        void init_lu() { 
            if (m_use_approx)
                init_lu_double();
            else
                init_lu_mpq();
        }

        // Extract a column from m_equations. The result is stored in c.
        template<typename Vector>
        void get_column(var j, Vector & c) {
            TRACE("get_column", tout << "get_column x" << j << "\n"; display_eqs(tout););
            typename Vector::manager & m = c.m();
            c.reset();
            eq_occs const & occs = m_eq_occs[j];
            for (unsigned i = 0; i < occs.size(); i++) {
                eq_occ const & occ = occs[i];
                unsigned eq_idx = occ.m_idx;
                linear_equation const & eq = *(m_equations[eq_idx]);
                SASSERT(eq.x(occ.m_pos) == j);
                eq.get_a(m, occ.m_pos, c.get(eq_idx));
            }
            TRACE("get_column", tout << "result: "; c.display_non_zeros(tout); tout << "\n";);
        }

        // Extract a non basic column. The result is stored in c.
        template<typename LU>
        void get_nonbasic_column(LU & _lu, var j, typename LU::dense_vector & c) {
            get_column(j, c);
            _lu.solve_Ax_eq_y(c);
        }
            
        void get_nonbasic_column_double(var j, lu_double::dense_vector & c) { get_nonbasic_column(m_lu_double, j, c); }
        void get_nonbasic_column_mpq(var j, lu_mpq::dense_vector & c) { get_nonbasic_column(m_lu_mpq, j, c); }

        // Get the linear combination needed for extracting a row.
        template<typename LU>
        void get_lin_comb_for_row(LU & _lu, unsigned eq_idx, typename LU::dense_vector & r) {
            typename LU::numeral one(1);
            SASSERT(eq_idx < m_equations.size());
            r.reset();
            _lu.m().set(r.get(eq_idx), one);
            _lu.solve_xA_eq_y(r);
        }


        // Apply the given linear combination to the equaltions in m_equations, and store
        // the result in r.
        // If include_fixed = false, then fixed variables are ignored.
        // If only_nonbasic = true, then only non-basic variables are considered.
        // If use_asserted = true, then m_asserted_bounds is used for detecting fixed variables, otherwise m_bounds is used.
        template<typename Vector>
        void extract_row(Vector const & lin_comb, Vector & r, bool only_nonbasic = true, bool use_asserted = false, bool include_fixed = false) const {
            r.reset();
            bound_propagator const & bp = use_asserted ? m_asserted_bounds : m_bounds;
            typename Vector::manager & m = lin_comb.m();
            typename Vector::numeral a;
            typename Vector::iterator it  = lin_comb.begin_non_zeros();
            typename Vector::iterator end = lin_comb.end_non_zeros();
            for (; it != end; ++it) {
                unsigned eq_idx = *it;
                typename Vector::numeral const & b = lin_comb[eq_idx];
                if (m.is_zero(b))
                    continue;
                linear_equation const & eq = *(m_equations[eq_idx]);
                unsigned sz = eq.size();
                for (unsigned i = 0; i < sz; i++) {
                    var x_i = eq.x(i);
                    if (only_nonbasic && basic(x_i))
                        continue;
                    if (!include_fixed && bp.is_fixed(x_i))
                        continue;
                    eq.get_a(m, i, a);
                    typename Vector::numeral & r_i = r.get(x_i);
                    m.addmul(r_i, a, b, r_i); 
                }
            }
            r.elim_zeros();
            m.del(a);
        }

        // Get the non-basic variables occurring in the given row of B^{-1}N.
        template<typename LU>
        void get_row(LU & _lu, unsigned eq_idx, typename LU::dense_vector & r,
                     bool only_nonbasic = true, bool use_asserted = false, bool include_fixed = false) {
            TRACE("get_row", tout << "original: "; m_eq_manager.display(tout, *(m_equations[eq_idx])); tout << "\n";);

            typename LU::dense_vector & lc = _lu.get_tmp_vector();
            get_lin_comb_for_row(_lu, eq_idx, lc);
            extract_row(lc, r, only_nonbasic, use_asserted, include_fixed);

            TRACE("get_row", 
                  tout << "eq " << eq_idx << "\n";
                  tout << "linear combination: "; r.display_non_zeros(tout); tout << "\n";;
                  tout << "result: "; r.display_pol(tout); tout << "\n";);
        }

        void get_row_double(unsigned eq_idx, lu_double::dense_vector & r, 
                            bool only_nonbasic = true, bool use_asserted = false, bool include_fixed = false) { 
            get_row(m_lu_double, eq_idx, r, only_nonbasic, use_asserted, include_fixed); 
        }
        void get_row_mpq(unsigned eq_idx, lu_mpq::dense_vector & r, 
                         bool only_nonbasic = true, bool use_asserted = false, bool include_fixed = false) { 
            get_row(m_lu_mpq, eq_idx, r, only_nonbasic, use_asserted, include_fixed); 
        }
        
        void tst_extract_non_basic_columns(std::ostream & out) {
            unsigned sz = m_lu_double.size();
            lu_double::dense_vector v(m_double_manager, sz);
            out << "columns:\n";
            for (var x = 0; x < num_vars(); x++) {
                if (basic(x) || was_eliminated(x))
                    continue;
                v.reset();
                get_nonbasic_column_double(x, v);
                out << "x" << x << ": "; 
                v.display(out);
                out << "\n";
            }
        }

        void tst_extract_rows(std::ostream & out) {
            lu_double::dense_vector v(m_double_manager, num_vars());
            out << "rows:\n";
            unsigned num_eqs = m_equations.size();
            for (unsigned i = 0; i < num_eqs; i++) {
                get_row_double(i, v);
                out << "eq " << i << ": "; 
                v.display_pol(out);
                out << "\n";
            }
        }

        template<typename LU>
        void pivot(LU & _lu, var x_b, var x_n) {
            if (m_use_approx)
                m_approx_pivots++;
            else
                m_pivots++;
            SASSERT(basic(x_b));
            SASSERT(!basic(x_n));
            unsigned eq_idx = m_basic[x_b];
            SASSERT(m_inv_basic[eq_idx] == x_b);
            unsigned normalized_threshold = std::min((m_equations.size()/10) + 1, m_refactor_threshold);
#if 1
            // TODO: incremental update is producing too much imprecision when using floating point numbers.
            // So: I'm disabling it for now.
            if (!_lu.m().precise()) normalized_threshold = 0;
#endif
            if (_lu.get_num_replacements() < normalized_threshold) {
                try {
                    typename LU::dense_vector & c = _lu.get_tmp_col();
                    get_column(x_n, c);
                    TRACE("pivot", tout << "column x" << m_basic[x_b] << " "; c.display_non_zeros(tout); tout << "\n";);
                    _lu.replace_column(m_basic[x_b], c);
                    update_lu_stats(_lu);
                    m_basic[x_b] = UINT_MAX;
                    m_basic[x_n] = eq_idx;
                    m_inv_basic[eq_idx] = x_n;
                    TRACE("pivot_bug", display(tout););
                    CASSERT("arith", !_lu.m().precise() || check_lu());
                    return;
                }
                catch (lu_exception) {
                    IF_VERBOSE(ST_VERBOSITY_LVL, verbose_stream() << "(arith-approx-failed)\n";);
                }
            }
            // refactor from scratch
            m_basic[x_b] = UINT_MAX;
            m_basic[x_n] = eq_idx;
            m_inv_basic[eq_idx] = x_n;
            init_lu_core(_lu);
            CASSERT("arith", !_lu.m().precise() || check_lu());
        }

        void pivot_double(var x_b, var x_n) { pivot(m_lu_double, x_b, x_n); }
        void pivot_mpq(var x_b, var x_n) { pivot(m_lu_mpq, x_b, x_n); }
        
        template<typename LU>
        void tst_random_pivoting(LU & _lu, unsigned num) {
            TRACE("random_pivoting", display_eqs(tout););
            init_lu_core(_lu);
            random_gen rgen;
            
            typename LU::numeral small(10000);
            _lu.m().inv(small);
            typename LU::numeral neg_small;
            _lu.m().set(neg_small, small);
            _lu.m().neg(neg_small);

            typename LU::dense_vector row(_lu.m(), num_vars());
            unsigned num_eqs = m_equations.size();
            for (unsigned i = 0; i < num; i++) {
                verbose_stream() << "+"; verbose_stream().flush();
                // select random equation/row
                TRACE("random_pivoting", display_basic(tout); display_LU(tout, _lu););
                unsigned eq_idx = rgen() % num_eqs;
                var x_b = m_inv_basic[eq_idx];
                get_row(_lu, eq_idx, row);
                TRACE("random_pivoting", tout << "x" << x_b << " : "; row.display_pol(tout); tout << "\n";);
                TRACE("pivot_row", tout << "x" << x_b << " : "; row.display_pol(tout); tout << "\n";);
                typename LU::dense_vector::iterator it  = row.begin_non_zeros();
                typename LU::dense_vector::iterator end = row.end_non_zeros();
                if (it == end) {
                    // row doesn't have non-basic variable
                    TRACE("random_pivoting", tout << "eq_idx: " << eq_idx << " does not have non-basic variables\n";);
                    continue;
                }
                unsigned num_non_zeros = end - it;
                var x_n = *(it + (rgen() % num_non_zeros));
                if (!LU::manager::precise()) {
                    if (_lu.m().lt(neg_small, row[x_n]) && _lu.m().lt(row[x_n], small)) {
                        verbose_stream() << "*";
                        continue;
                    }
                }
                TRACE("random_pivoting", tout << "pivoting x" << x_b << " with x" << x_n << "\n";);
                pivot(_lu, x_b, x_n);
            }
        }

        /**
           \brief Check LU mpq (this method does not really work for m_lu_double due to floating point imprecision).
        */
        bool check_lu() const {
            if (m_use_approx)
                return true;
            lu_mpq::dense_vector row(const_cast<imp*>(this)->m_num_manager, num_vars());
            unsigned num_eqs = m_equations.size();
            for (unsigned eq_idx = 0; eq_idx < num_eqs; eq_idx++) {
                var x_b = m_inv_basic[eq_idx];
                row.reset();
                const_cast<imp*>(this)->get_row_mpq(eq_idx, row, false /* get basic too */, false, true /* also include fixed vars */);
                TRACE("check_lu", tout << "x" << x_b << ", eq " << eq_idx << ": "; row.display_pol(tout); tout << "\n";);
                // row must contain one and only one basic variable: x_b
                // The coefficient of x_b must be 1
                bool found_x_b = false;
                lu_mpq::dense_vector::iterator it  = row.begin_non_zeros();
                lu_mpq::dense_vector::iterator end = row.end_non_zeros();
                for (; it != end; ++it) {
                    var x = *it;
                    if (m_num_manager.is_zero(row[x]))
                        continue;
                    if (x == x_b) {
                        CTRACE("arith_bug", !m_num_manager.is_one(row[x]), tout << "x" << x_b << ":  "; row.display_pol(tout); tout << "\n";
                               display(tout););
                        SASSERT(m_num_manager.is_one(row[x]));
                        found_x_b = true;
                        continue;
                    }
                    CTRACE("arith_bug", basic(x), tout << "row " << eq_idx << " contains unexpected basic variable x" << x << "\n"; 
                           row.display_pol(tout); tout << "\n"; display(tout););
                    SASSERT(!basic(x));
                }
                SASSERT(found_x_b);
            }
            return true;
        }

        template<typename LU, typename Values, typename NumInfMng, typename Numeral>
        void update_dependents(LU & _lu, Values & values, NumInfMng & infm, var x_n, Numeral const & old_val) {
            Numeral aux;
            Numeral delta;
            infm.sub(values[x_n], old_val, delta);
            typename LU::dense_vector & c = _lu.get_tmp_col();
            typename LU::dense_vector::manager & nm = c.m();
            get_nonbasic_column(_lu, x_n, c);
            TRACE("fix_nonbasic_var", tout << "fixing x" << x_n << ", old_val: " << infm.to_string(old_val) << ", new_val: " << 
                  infm.to_string(values[x_n]) << ", delta: " << infm.to_string(delta) << "\n";
                  tout << "column: "; c.display_non_zeros(tout); tout << "\n";);
            typename LU::dense_vector::iterator it  = c.begin_non_zeros();
            typename LU::dense_vector::iterator end = c.end_non_zeros();
            for (; it != end; ++it) {
                unsigned eq_idx = *it;
                if (nm.is_zero(c[eq_idx]))
                    continue;
                var x_b = m_inv_basic[eq_idx];
                SASSERT(m_basic[x_b] == eq_idx);
                infm.mul(delta, c[eq_idx], aux);
                infm.neg(aux);
                TRACE("fix_nonbasic_var", tout << "adjusting x" << x_b << " of: " << eq_idx << " with " << infm.to_string(aux) << "\n";);
                acc_value(x_b, aux);
                if (below_lower(x_b) || above_upper(x_b))
                    m_bad_vars.insert(x_b);
            }
            infm.del(aux);
            infm.del(delta);
        }

        /**
           \brief Fix a nonbasic variable by moving it to offending bound and propagating the
           update to the basic variables.
        */
        template<typename LU, typename Values, typename NumInfMng>
        void fix_nonbasic_var(LU & _lu, Values & values, NumInfMng & infm, var x_n) {
            SASSERT(below_lower(x_n) || above_upper(x_n));
            SASSERT(nonbasic(x_n));
            typename NumInfMng::numeral old_val;
            infm.set(old_val, values[x_n]);
            if (below_lower(x_n)) {
                lower2value(x_n);
            }
            else {
                SASSERT(above_upper(x_n));
                upper2value(x_n);
            }
            update_dependents(_lu, values, infm, x_n, old_val);
            infm.del(old_val);
        }

        void fix_nonbasic_var(var x) {
            if (!below_lower(x) && !above_upper(x))
                return; // nothing to be done
            SASSERT(nonbasic(x));
            if (m_use_approx)
                fix_nonbasic_var(m_lu_double, m_approx_values, m_double_manager, x);
            else
                fix_nonbasic_var(m_lu_mpq, m_values, m_num_inf_manager, x);
        }

        /**
           \brief Remove the given variables from m_bad_vars.
        */
        void erase_from_bad_vars(var_set & bad_vars, var_buffer const & vars) {
            var_buffer::const_iterator it2  = vars.begin();
            var_buffer::const_iterator end2 = vars.end();
            for (; it2 != end2; ++it2) {
                bad_vars.erase(*it2);
                SASSERT(!bad_vars.contains(*it2));
            }
        }

        var_buffer m_to_delete;

        void fix_nonbasic_vars() {
            TRACE("fix_nonbasic_vars", display_LU(tout););
            m_to_delete.reset();
            unsigned sz = m_bad_vars.size();
            for (unsigned i = 0; i < sz; i++) {
                var x = m_bad_vars[i];
                if (basic(x))
                    continue;
                TRACE("fix_nonbasic_vars", tout << "fixed x" << x << "\n";);
                fix_nonbasic_var(x);
                m_to_delete.push_back(x);
            }
            
            erase_from_bad_vars(m_bad_vars, m_to_delete);
            SASSERT(check_no_nonbasic_bad_var());
        }
        
        /**
           \brief Remove satisfied variables from m_bad_vars
        */
        void cleanup_bad_vars() {
            m_to_delete.reset();
            var_set::iterator it  = m_bad_vars.begin();
            var_set::iterator end = m_bad_vars.end();
            for (; it != end; ++it) {
                var x = *it;
                if (!below_lower(x) && !above_upper(x))
                    m_to_delete.push_back(x);
            }
            erase_from_bad_vars(m_bad_vars, m_to_delete);
        }

        void cleanup_int_bad_vars() {
            m_to_delete.reset();
            var_set::iterator it  = m_int_bad_vars.begin();
            var_set::iterator end = m_int_bad_vars.end();
            for (; it != end; ++it) {
                var x = *it;
                TRACE("int_bad_vars", tout << "x" << x << ", int_feasible: " << int_feasible(x) << ", val: " 
                      << m_num_inf_manager.to_string(m_values[x]) << "\n";);
                if (int_feasible(x))
                    m_to_delete.push_back(x);
            }
            erase_from_bad_vars(m_int_bad_vars, m_to_delete);
        }

        /**
           \brief Return the smallest variable in m_bad_vars.
        */
        var get_smallest_bad_var() const {
            var r = null_var; // NOTE: null_var is the biggest variable
            var_set::iterator it  = m_bad_vars.begin();
            var_set::iterator end = m_bad_vars.end();
            for (; it != end; ++it) {
                var x = *it;
                SASSERT(x < null_var);
                if (x < r)
                    r = x;
            }
            return r;
        }

        /**
           \brief Return the variable in m_bad_vars with the least/greatest error
        */
        template<bool LEAST>
        var get_lg_error_bad_var() {
            var r = null_var;
            if (m_use_approx) {
                double error_r;
                double error_x;
                var_set::iterator it  = m_bad_vars.begin();
                var_set::iterator end = m_bad_vars.end();
                for (; it != end; ++it) {
                    var x = *it;
                    if (below_lower(x))
                        error_x = bp().approx_lower(x) - m_approx_values[x];
                    else if (above_upper(x))
                        error_x = m_approx_values[x] - bp().approx_upper(x);
                    else
                        continue;
                    if (r == null_var || (LEAST && error_x < error_r) || (!LEAST && error_x > error_r)) {
                        r = x;
                        error_r = error_x;
                    }
                }
                TRACE("get_bad_var", tout << "x" << r << " error: " << error_r << "\n";);
                return r;
            }
            else {
                mpq error_r; // ignore infinitesimals
                mpq error_x;
                var_set::iterator it  = m_bad_vars.begin();
                var_set::iterator end = m_bad_vars.end();
                for (; it != end; ++it) {
                    var x = *it;
                    if (below_lower(x))
                        m_num_manager.sub(bp().lower(x), m_values[x].first, error_x); 
                    else if (above_upper(x))
                        m_num_manager.sub(m_values[x].first, bp().upper(x), error_x);
                    else
                        continue;
                    SASSERT(m_num_manager.is_nonneg(error_x));
                    if (r == null_var || (LEAST && m_num_manager.lt(error_x, error_r)) || (!LEAST && m_num_manager.gt(error_x, error_r))) {
                        r = x;
                        m_num_manager.swap(error_x, error_r);
                    }
                }
                m_num_manager.del(error_r);
                m_num_manager.del(error_x);
                TRACE("get_bad_var", tout << "x" << r << " error: " << m_num_manager.to_string(error_r) << "\n";);
                return r;
            }
        }

        /**
           \brief Return the variable in m_bad_vars with the greatest error
        */
        var get_least_error_bad_var() { return get_lg_error_bad_var<true>(); }

        /**
           \brief Return the variable in m_bad_vars with the least error
        */
        var get_greatest_error_bad_var() { return get_lg_error_bad_var<false>(); }
        
        unsigned get_num_bounds(var x) const {
            unsigned r = 0;
            if (has_lower(x)) r++;
            if (has_upper(x)) r++;
            return r;
        }

        // Return true if x1 is a better pivot than x2
        template<typename Vector>
        bool better_pivot(var x_1, var x_2, Vector const & row) const {
            SASSERT(x_1 != null_var);
            if (x_2 == null_var)
                return true;
            typename Vector::manager & nm = row.m();
            unsigned num_bounds1 = get_num_bounds(x_1);
            unsigned num_bounds2 = get_num_bounds(x_2);
            if (num_bounds1 == 0 && num_bounds2 > 0)
                return true;
            if (num_bounds1 > 0 && num_bounds2 == 0)
                return false;
            if (nm.gt(row[x_1], row[x_2]))
                return true;
            if (nm.lt(row[x_1], row[x_2]))
                return false;
            unsigned num_occs1  = m_eq_occs[x_1].size();
            unsigned num_occs2  = m_eq_occs[x_2].size();
            return num_occs1 < num_occs2;
        }

        template<typename LU, typename Values, typename NumInfMng>
        var select_pivot(LU & _lu, Values & values, NumInfMng & infm, var x_b, bool is_below, bool blands_rule) {
            SASSERT(basic(x_b));
            typename LU::dense_vector & row = _lu.get_tmp_row(num_vars());
            typename LU::dense_vector::manager & nm = row.m();
            unsigned eq_idx = m_basic[x_b];
            get_row(_lu, eq_idx, row, true, m_use_asserted, false /* there is not point in collecting fixed variables */);
            TRACE("select_pivot", tout << "select_pivot x_b: x" << x_b << ", is_below: " << is_below << "\n";
                  bp().display_var_bounds(tout, x_b, true, true); tout << "\nval: " << infm.to_string(values[x_b]) << "\n";
                  row.display_pol(tout); tout << "\n";
                  tout << "below_lower(x_b): " << below_lower(x_b) << "\n";
                  tout << "above_upper(x_b): " << above_upper(x_b) << "\n";);
            var r = null_var;
            typename LU::dense_vector::iterator it  = row.begin_non_zeros();
            typename LU::dense_vector::iterator end = row.end_non_zeros();
            for (; it != end; ++it) {
                var x_n = *it;
                if (nm.is_zero(row[x_n]))
                    continue; // leftover
                bool is_neg = is_below ? nm.is_neg(row[x_n]) : nm.is_pos(row[x_n]);
                bool is_pos = !is_neg;
                if ((is_pos && above_lower(x_n)) || (is_neg && below_upper(x_n))) {
                    // x_n is a candidate for pivoting
                    if (blands_rule) {
                        if (x_n < r) {
                            r = x_n;
                            TRACE("select_pivot", tout << "new-candidate: x" << r << "\n";);
                        }
                    }
                    else if (better_pivot(x_n, r, row)) {
                        r = x_n;
                        TRACE("select_pivot", tout << "new-candidate: x" << r << ", num-bounds: " << get_num_bounds(r) 
                              << " num-occs: " << m_eq_occs[r].size() << "\n";);
                    }
                }
            }
            return r;
        }
        
        /**
           \brief Fix a basic variable.
        */
        template<typename LU, typename Values, typename NumInfMng>
        bool fix_basic_var(LU & _lu, Values & values, NumInfMng & infm, var x_b, bool blands_rule) {
            bool is_below;
            if (below_lower(x_b)) {
                is_below = true;
            }
            else if (above_upper(x_b)) {
                is_below = false;
            }
            else {
                return true; // nothing to be done
            }
            var x_n = select_pivot(_lu, values, infm, x_b, is_below, blands_rule);
            if (x_n == null_var)
                return false;
            SASSERT(basic(x_b));
            SASSERT(nonbasic(x_n));
            TRACE("fix_basic_var", tout << "pivoting x" << x_b << " x" << x_n << "\n";);
            pivot(_lu, x_b, x_n);
            SASSERT(nonbasic(x_b));
            fix_nonbasic_var(_lu, values, infm, x_b);
            TRACE("fix_basic_var", tout << "x" << x_b << " -> " << infm.to_string(values[x_b]) << "\n";
                  bp().display_var_bounds(tout, x_b); tout << "\n";);
            SASSERT(!below_lower(x_b));
            SASSERT(!above_upper(x_b));
            return true;
        }

        bool fix_basic_var(var x_b, bool blands_rule) {
            if (m_use_approx)
                return fix_basic_var(m_lu_double, m_approx_values, m_double_manager, x_b, blands_rule);
            else
                return fix_basic_var(m_lu_mpq, m_values, m_num_inf_manager, x_b, blands_rule);
        }
        
        // Debugging: make sure m_bad_vars does not contain nonbasic variables.
        bool check_no_nonbasic_bad_var() const {
            var_set::iterator it  = m_bad_vars.begin();
            var_set::iterator end = m_bad_vars.end();
            for (; it != end; ++it) {
                CTRACE("arith_bug", nonbasic(*it), tout << "nonbasic var at bad_vars x" << *it << "\n";);
                SASSERT(!nonbasic(*it));
            }
            return true;
        }

        void set_conflict(var x_b) {
            m_conflict_eq_idx = m_basic[x_b];
        }

        bool inconsistent() const {
            return m_conflict_eq_idx != UINT_MAX || m_bounds.inconsistent() || m_asserted_bounds.inconsistent();
        }

        void reset_updated() {
            if (m_use_approx)
                m_approx_updated.reset();
            else
                m_updated.reset();
        }

#define DISPLAY_STAT(NAME, VAL) if (VAL > 0) out << " " << NAME << " " << VAL;
        
        void display_progress(std::ostream & out) const {
            out << "(arith";
            DISPLAY_STAT(":pivots", m_pivots);
            DISPLAY_STAT(":approx-pivots", m_approx_pivots);
            DISPLAY_STAT(":branches", m_branches);
            DISPLAY_STAT(":cuts", m_cuts);
            out << ")\n";
        }

        /**
           \brief Try to satisfy all bounds.
           Result:
             l_true:   succeeded
             l_false:  problem is unsat
             l_undef:  gave up
        */
        lbool make_feasible_core(unsigned max_pivots = UINT_MAX) {
            if (inconsistent()) 
                return l_false;
            TRACE("make_feasible_detail", display(tout););
            if (m_bad_vars.empty())
                return l_true;

            reset_updated();
            TRACE("make_feasible_begin", display(tout););

            CASSERT("arith", check_eqs_satisfied());
            CASSERT("arith", check_bad_vars());
            fix_nonbasic_vars();
            
            // limit for switching to blands rule
            unsigned limit   = num_vars() * m_blands_rule_factor; 
            unsigned counter = 0;

            while (true) {
                CASSERT("arith", check_bad_vars());
                CASSERT("arith", check_eqs_satisfied());
                CASSERT("arith", check_basic_assignment());
                CASSERT("arith", check_no_nonbasic_bad_var());
                TRACE("make_feasible_step", display(tout););
                checkpoint();
                counter++;
                cleanup_bad_vars();
                if (m_bad_vars.empty()) {
                    TRACE("make_feasible", tout << "satisfied:\n"; display(tout););
                    return l_true;
                }
                // var x_b = counter >= limit ? get_smallest_bad_var() : get_least_error_bad_var();
                var x_b = counter >= limit ? get_smallest_bad_var() : get_greatest_error_bad_var();
                // verbose_stream() << "x" << x_b << " "; verbose_stream().flush();
                TRACE("make_feasible", tout << "next var to be fixed: x" << x_b << "\n";);
                SASSERT(basic(x_b));
                if (!fix_basic_var(x_b, counter >= limit)) {
                    TRACE("make_feasible", tout << "inconsistent:\n"; display(tout););
                    SASSERT(basic(x_b));
                    set_conflict(x_b);
                    return l_false;
                }
                m_bad_vars.erase(x_b);
#ifndef _EXTERNAL_RELEASE
                IF_VERBOSE(ST_VERBOSITY_LVL, if (counter % 100 == 0) display_progress(verbose_stream()););
#endif
                if (counter > max_pivots)
                    return l_undef;
            }
        }

        void reset_conflict() {
            m_conflict_eq_idx = UINT_MAX;
        }

        unsigned_vector m_cached_basic;
        
        /**
           \brief When using floating point numbers, we may reach an "invalid" basis.
           We say a basis is invalid the corresponding matrix is singular. 
           To avoid this problem, we cache the last "valid" basis.
        */
        void cache_basis() {
            m_cached_basic.reset();
            unsigned_vector::iterator it  = m_basic.begin();
            unsigned_vector::iterator end = m_basic.end();
            for (; it != end; ++it)
                m_cached_basic.push_back(*it);
        }

        /**
           \brief Restore last cached basis.
        */
        void restore_basis() {
            SASSERT(m_basic.size() == m_cached_basic.size());
            unsigned sz = m_basic.size();
            for (var x = 0; x < sz; x++) {
                if (m_cached_basic[x] != UINT_MAX) {
                    // variables was on the basis
                    m_basic[x] = m_cached_basic[x];
                    m_inv_basic[m_basic[x]] = x;
                } 
                else {
                    // variable was not on the basis
                    m_basic[x] = UINT_MAX;
                }
            }
        }

        lbool make_feasible_approx_then_precise() {
            // find "promising" basis using approx.
            cache_basis();
            try {
                set_mode(true, m_use_asserted);
                unsigned limit = m_equations.size() * m_approx_threshold_factor;
                lbool r = make_feasible_core(limit);
                if (r == l_undef) {
                    // approximation failed to satisfy all constraints.
                    // so, disable it.
                    m_approx_forbidden = true;
                }
            }
            catch (lu_exception) {
                IF_VERBOSE(ST_VERBOSITY_LVL, verbose_stream() << "(arith-approx-failed)\n";);
                restore_basis();
            }
            reset_conflict(); // do not trust approx solver
            // try again using precise
            set_mode(false, m_use_asserted);
            TRACE("make_feasible_approx", tout << "second round m_use_approx: " << m_use_approx << "\n";);
            try {
                // may fail because the basis computed by the approximation is not valid.
                return make_feasible_core();
            }
            catch (lu_exception) {
                restore_basis();
                init_lu_mpq();
                return make_feasible_core();
            }
        }

        lbool make_feasible() {
            if (inconsistent())
                return l_false;
            if (m_bad_vars.empty())
                return l_true;
            SASSERT(check_basic_assignment());
            CASSERT("arith", check_bad_vars());
            
            lbool r;
            if (m_approx_threshold_factor == 0 || m_approx_forbidden)
                r = make_feasible_core();
            else
                r = make_feasible_approx_then_precise();

            CASSERT("arith", check_bad_vars());
            SASSERT(r != l_true || check_bounds_satisfied());
            SASSERT(check_basic_assignment());

            if (r != l_true)
                restore_assignment();
            
            cleanup_int_bad_vars();
            
            TRACE("make_feasible_result", tout << "r: " << r << "\n"; display(tout););
            return r;
        }

        void restore_assignment() {
            CASSERT("arith", check_eqs_satisfied());
            CASSERT("arith", check_bad_vars());
            TRACE("restore_assignment", tout << "restore_assignment:\n"; display_assignment(tout););
            var_set::iterator it1  = m_approx_updated.begin();
            var_set::iterator end1 = m_approx_updated.end();
            for (; it1 != end1; ++it1) {
                var x = *it1;
                m_approx_values[x] = m_old_approx_values[x];
            }
            m_approx_updated.reset();

            var_set::iterator it2  = m_updated.begin();
            var_set::iterator end2 = m_updated.end();
            for (; it2 != end2; ++it2) {
                var x = *it2;
                m_num_inf_manager.swap(m_values[x], m_old_values[x]);
                check_int(x);
            }
            m_updated.reset();
            
            SASSERT(m_approx_updated.empty());
            SASSERT(m_updated.empty());
            TRACE("restore_assignment", tout << "restore_assignment:\n"; display_assignment(tout););
            CASSERT("arith", check_eqs_satisfied());
            CASSERT("arith", check_bad_vars());
        }

        // -----------------------
        //
        // make_int_feasible
        //
        // -----------------------

        random_gen  m_rand;

        void init_make_int_feasible() {
            set_mode(false, false); // use derived bounds
            if (m_cuts_enabled) {
                move_nonbasic_to_bounds();
                make_feasible();
                add_cuts();
                // if (make_feasible() != l_false && !m_int_bad_vars.empty())
                //     add_cuts();
                make_feasible();
            }
        }

        // Buffer for storing cuts that will be added.
        struct new_cut_buffer {
            var_buffer                  m_ys;
            ptr_vector<linear_equation> m_eqs;
            mpq_buffer                  m_cs;
            svector<bool>               m_is_lower;

            new_cut_buffer(numeral_manager & m):m_cs(m) {}
            
            void save(var y, linear_equation * eq, mpq const & c, bool is_lower) {
                m_ys.push_back(y);
                m_eqs.push_back(eq);
                m_cs.push_back(c);
                m_is_lower.push_back(is_lower);
            }

            unsigned size() const { return m_ys.size(); }
            
            bool empty() const { return m_ys.empty(); }
        };

        void insert_cuts(new_cut_buffer & new_cuts) {
            for (unsigned i = 0; i < new_cuts.size(); i++) {
                m_cuts++;
                unsigned eq_idx = m_equations.size();
                var y = new_cuts.m_ys[i];
                m_basic[y] = eq_idx;
                m_inv_basic.push_back(y);
                m_equations.push_back(new_cuts.m_eqs[i]);
                m_eq_occs.push_back(eq_occs()); // for y
                init_eq_occs(eq_idx);
                mpq const & c = new_cuts.m_cs[i];
                if (new_cuts.m_is_lower[i])
                    assert_lower(y, c, false);
                else
                    assert_upper(y, c, false);
                // register_propagation_eq(*(new_cuts.m_eqs[i]));
            }
        }
        
        // dual == false ==> as*xs >= c
        // dual == true  ==> as*xs <= c
        void add_cut(mpq_buffer & as, var_buffer & xs, mpq const & c, bool dual, new_cut_buffer & new_cuts) {
            mpq val;
            var y = mk_var(0);
            // compute initial value of y
            for (unsigned i = 0; i < xs.size(); i++) {
                m_num_manager.addmul(val, as[i], m_values[xs[i]].first, val);
            }
            m_num_inf_manager.set(m_values[y], val);
            xs.push_back(y);
            as.push_back(mpq(-1));
            m_num_manager.del(val);
            linear_equation * new_eq = m_eq_manager.mk(as.size(), as.c_ptr(), xs.c_ptr());
            TRACE("cut", tout << "new cut y" << y << " val: " << m_num_manager.to_string(val) << "\n";
                  m_eq_manager.display(tout, *new_eq); tout << "\n";);
            new_cuts.save(y, new_eq, c, !dual);
        }
        
        void add_cuts() {
            mpq k(1);
            mpq c;
            new_cut_buffer new_cuts(m_num_manager);
            lu_mpq::dense_vector & row = m_lu_mpq.get_tmp_row(num_vars());
            for (var x = 0; x < num_vars(); x++) {
                if (!basic(x) || was_eliminated(x) || int_feasible(x))
                    continue;
                row.reset();
                get_row_mpq(m_basic[x], row, true, m_use_asserted, true);
                
                if (mk_jdm_cut(k, x, row, m_mpq_buffer, m_var_buffer, c))
                    add_cut(m_mpq_buffer, m_var_buffer, c, false, new_cuts);
            }
            if (!new_cuts.empty()) {
                insert_cuts(new_cuts);
                init_lu();
                TRACE("add_cuts", display(tout););
                make_feasible();
            }
            m_num_manager.del(c);
        }

        bool is_cut_var(var x) const {
            // TODO: refine... I'm using the fact that a variable introduced by a cut is not associated with an expr
            return m_var2expr.get(x) == 0;
        }

        /**
           \brief A cut variable is not "useful" if it is on the basis.
           So, we garbage collect any cut that is 
        */
        void gc_cuts() {
        }
        
        bool is_nonslact_var(var x) const {
            // TODO: refine...
            expr * t = m_var2expr.get(x);
            return t != 0 && is_uninterp_const(t);
        }
        
        var bb_select_rand_var() {
#if 0
            // Give preference to non cut vars
#define BB_MAX_TRIES 8
            unsigned counter = 0;
            while (!m_int_bad_vars.empty()) {
                var_set::iterator it    = m_int_bad_vars.begin();
                var_set::iterator end   = m_int_bad_vars.end();
                unsigned num_candidates = end - it;
                unsigned idx            = m_rand() % num_candidates;
                var x = it[idx];
                if (int_feasible(x))
                    m_int_bad_vars.erase(x);
                if (!is_cut_var(x))
                    return x;
                counter++;
                if (counter >= BB_MAX_TRIES)
                    break;
            }

            if (m_int_bad_vars.empty())
                return null_var;
            
            // search for non-cut var
            var x = null_var;
            unsigned num = 1;
            var_set::iterator it    = m_int_bad_vars.begin();
            var_set::iterator end   = m_int_bad_vars.end();
            for (; it != end; ++it) {
                if (int_feasible(x))
                    continue;
                if (is_cut_var(*it))
                    continue;
                if (x == null_var || m_rand() % num == 0)
                    x = *it;
                num++;
            }
#endif
            // pick a random variable
            while (!m_int_bad_vars.empty()) {
                var_set::iterator it    = m_int_bad_vars.begin();
                unsigned num_candidates = m_int_bad_vars.size();
                unsigned idx            = m_rand() % num_candidates;
                var x = it[idx];
                if (!int_feasible(x))
                    return x;
                    m_int_bad_vars.erase(x);
            }

            return null_var;
        }

        var_buffer m_bb_var_buffer;

        var bb_select_rand_nonslack_var() {
            m_bb_var_buffer.reset();
            var_set::iterator it    = m_int_bad_vars.begin();
            var_set::iterator end   = m_int_bad_vars.end();
            for (; it != end; ++it) {
                var x = *it;
                if (int_feasible(x))
                    continue;
                if (is_nonslact_var(x))
                    m_bb_var_buffer.push_back(x);
            }
            if (m_bb_var_buffer.empty())
                return bb_select_rand_var();
            
            unsigned idx = rand() % m_bb_var_buffer.size();
            return m_bb_var_buffer[idx];
        }
        
        /**
           \brief Select a variable x >= k (or x <= k) s.t. |k| <= threshold, and |k| is maximal.
        */
        var bb_select_largest_smaller_than(mpz const & threshold) {
            var best = null_var;
            mpz k_best;
            mpz aux;
            var_set::iterator it    = m_int_bad_vars.begin();
            var_set::iterator end   = m_int_bad_vars.end();
            for (; it != end; ++it) {
                var x = *it;
                if (int_feasible(x))
                    continue;
                if (has_lower(x) || has_upper(x))
                    continue;
                if (m_num_manager.is_neg(m_values[x].first))
                    m_num_manager.ceil(m_values[x].first, aux);
                else
                    m_num_manager.floor(m_values[x].first, aux);
                m_num_manager.abs(aux);
                if (m_num_manager.le(aux, threshold) && (best == null_var || m_num_manager.gt(aux, k_best))) {
                    best = x;
                    m_num_manager.swap(aux, k_best);
                }
            }
            m_num_manager.del(k_best);
            m_num_manager.del(aux);
            return best;
        }

        var bb_select_var() {
            if (m_branch_vars_only)
                return bb_select_rand_nonslack_var();
            else 
                return bb_select_rand_var();
#if 0
            mpz limit1, limit2;
            var x;
            m_num_manager.set(limit1, 128);
            x = bb_select_largest_smaller_than(limit1);
            if (x != null_var)
                return x;
            m_num_manager.set(limit2, 1024);
            x = bb_select_largest_smaller_than(limit2);
            if (x != null_var)
                return x;
            return bb_select_rand_var();
#endif
        }

        bool bb_plunging(var x) {
            SASSERT(!int_feasible(x));
            mpq k;
            m_num_inf_manager.ceil(m_values[x], k);
            push();
            bb_assert_decision(x, true, k);
            if (make_feasible() == l_false) {
                pop(1);
                m_num_inf_manager.floor(m_values[x], k);
                bb_assert_decision(x, false, k);
                return true;
            }
            pop(1);
            push();
            m_num_inf_manager.floor(m_values[x], k);
            bb_assert_decision(x, false, k);
            if (make_feasible() == l_false) {
                pop(1);
                m_num_inf_manager.ceil(m_values[x], k);
                bb_assert_decision(x, true, k);
                return true;
            }
            pop(1);
            return false;
        }

        var_buffer m_todo_plunging;

        void bb_plunging() {
            if (inconsistent())
                return;
            m_todo_plunging.reset();
            var_set::iterator it    = m_int_bad_vars.begin();
            var_set::iterator end   = m_int_bad_vars.end();
            for (; it != end; ++it) {
                var x = *it;
                if (!int_feasible(x))
                    m_todo_plunging.push_back(x);
            }
            
            while (!m_todo_plunging.empty()) {
                if (inconsistent()) 
                    return;
                if (bb_plunging(m_todo_plunging.back())) {
                    // verbose_stream() << "plunging worked: x" << m_todo_plunging.back() << "\n";
                }
                m_todo_plunging.pop_back();
            }
        }

        /**
           \brief Propagation procedure for branch&bound
        */
        bool bb_propagate() {
            CASSERT("arith", check_eqs_satisfied() && check_bad_vars());
            propagate_bounds(); // propagate_bounds 
            CASSERT("arith", check_eqs_satisfied() && check_bad_vars());
            make_feasible();    // make sure the problem is real feasible
            // bb_plunging();
            return !inconsistent();
        }

        void bb_push(var x, bool lower, mpq const & k) {
            push();
            m_bb_var.push_back(x);
            m_bb_lower.push_back(lower);
            m_bb_first.push_back(true);
            m_bb_k.push_back(mpq());
            m_num_manager.set(m_bb_k.back(), k);
            SASSERT(m_bb_var.size()   == m_bb_lower.size());
            SASSERT(m_bb_k.size()     == m_bb_lower.size());
            SASSERT(m_bb_first.size() == m_bb_lower.size());
        }
        
        void bb_pop() {
            pop(1);
            m_bb_var.pop_back();
            m_bb_lower.pop_back();
            m_bb_first.pop_back();
            m_bb_k.pop_back();
            SASSERT(m_bb_var.size()   == m_bb_lower.size());
            SASSERT(m_bb_k.size()     == m_bb_lower.size());
            SASSERT(m_bb_first.size() == m_bb_lower.size());
        }

        void bb_assert_decision(var x, bool lower, mpq const & k) { 
            if (lower) {
                m_bounds.assert_decided_lower(x, k);
            }
            else {
                m_bounds.assert_decided_upper(x, k);
            }
            if (above_upper(x) || below_lower(x))
                m_bad_vars.insert(x);
        }

        void bb_branch(var x) {
            m_branches++;
            SASSERT(m_bad_vars.empty());
            SASSERT(!m_num_inf_manager.is_int(m_values[x]));
            TRACE("make_int_feasible", tout << "x" << x << " -> " << m_num_inf_manager.to_string(m_values[x]) << "\n";);
            bool lower;
#if 1
            if (has_lower(x) && has_upper(x)) 
                lower = (m_rand() % 2) == 0;
            else if (has_upper(x))
                lower = true;
            else if (has_lower(x))
                lower = false;
            else
                lower = (m_rand() % 2) == 0;
#else
            lower = (m_rand() % 2) == 0;
#endif
            mpq k;
            if (lower) 
                m_num_inf_manager.ceil(m_values[x], k);
            else
                m_num_inf_manager.floor(m_values[x], k);
            bb_push(x, lower, k);
            bb_assert_decision(x, lower, k);
            TRACE("bb_branch", tout << "branching on x" << x << " " << (lower ? ">=" : "<=") << " " << m_num_manager.to_string(k) << "\n";
                  tout << "new-lvl: " << m_bb_var.size() << "\n";);
            m_num_manager.del(k);
        }

        bool bb_resolve_conflict() {
            SASSERT(inconsistent());
            while (!m_bb_var.empty()) {
                if (m_bb_first.back() == false) {
                    // tried both branches...
                    TRACE("make_int_feasible", tout << "backtracking lvl: " << m_bb_var.size() << "\n";);
                    bb_pop();
                    continue;
                }
                pop(1); // pop just the bounds
                push();
                var x = m_bb_var.back();
                m_bb_first.back() = false;
                SASSERT(m_bb_first.back() == false);
                bool lower = m_bb_lower.back() != 0;
                if (lower) {
                    // k <= x is inconsistent, then flip to x <= k-1
                    m_num_manager.dec(m_bb_k.back());
                }
                else {
                    // x <= k is inconsistent, then flip to k+1 <= x
                    m_num_manager.inc(m_bb_k.back());
                }
                lower = !lower;
                m_bb_lower.back() = lower;
                // assert new decision
                bb_assert_decision(x, lower, m_bb_k.back());
                TRACE("bb_branch", tout << "[flip] branching on x" << x << " " << (lower ? ">=" : "<=")
                      << " " << m_num_manager.to_string(m_bb_k.back()) << "\n"; tout << "lvl: " << m_bb_var.size() << "\n";);
                return true;
            }
            return false;
        }

        void bb_restart() {
            while (!m_bb_var.empty()) {
                bb_pop();
            }
        }
        
        lbool bb_bounded_search(unsigned limit) {
            if (inconsistent())
                return l_false;
            unsigned counter = 0;
            while (true) {
                while (!bb_propagate()) {
                    if (!bb_resolve_conflict())
                        return l_false;
                }
                TRACE("make_int_feasible_step", display_bounds(tout); display_assignment(tout); display_bad_vars(tout);); 
                SASSERT(!inconsistent());
                var x = bb_select_var();
                // verbose_stream() << "lvl: " << m_bb_var.size() << " x" << x << "\n";
                if (x == null_var)
                    return l_true;
                bb_branch(x);
                counter++;
                if (counter >= limit)
                    break;
                TRACE("make_int_feasible", tout << "selected: x" << x << "\n";);
#ifndef _EXTERNAL_RELEASE
                IF_VERBOSE(ST_VERBOSITY_LVL, if (counter % 100 == 0) display_progress(verbose_stream()););
#endif
            }
            return l_undef;
        }

        /**
           \brief Add bounds to all integer variables that are unbounded
        */
        void bb_add_bounds(mpq const & limit) {
            mpq neg_limit;
            m_num_manager.set(neg_limit, limit);
            m_num_manager.neg(neg_limit);
            unsigned num = num_vars();
            for (var x = 0; x < num; x++) {
                if (is_int(x) && !was_eliminated(x)) {
                    if (!has_lower(x))
                        bb_assert_decision(x, true, neg_limit);
                    if (!has_upper(x))
                        bb_assert_decision(x, false, limit);
                }
            }
            m_num_manager.del(neg_limit);
        }

        lbool make_int_feasible_core() {
            lbool r = bb_bounded_search(1024*16);
            bb_restart();
            return r;
        }

        lbool bb_model_finder(unsigned range, unsigned num_branches) {
            mpq limit;
            m_num_manager.set(limit, range);
            push(); // protect state
            bb_add_bounds(limit);
            lbool r = bb_bounded_search(num_branches);
            if (r == l_false)
                r = l_undef;
            m_num_manager.del(limit);
            pop(1); // restore state
            return r;
        }

        lbool make_int_feasible() {
            if (inconsistent())
                return l_false;
            init_make_int_feasible();

            TRACE("make_int_feasible_begin", display(tout););
            TRACE("make_int_feasible_begin", display_int_infeasible_rows(tout););
            
            unsigned num_branches = m_int_bad_vars.size() * 2;
            bool find_model = true;
            unsigned range = 32;

            lbool r;
            while (true) {
                SASSERT(scope_lvl() == 0);
                if (find_model)
                    r = bb_model_finder(range, num_branches);
                else
                    r = bb_bounded_search(num_branches);
                if (r != l_undef)
                    break;
                find_model = !find_model;
                bb_restart();
                // init_make_int_feasible();
                num_branches += (m_equations.size() / 10) + 1;
            }

            // lbool r = bb_model_finder(128);
            TRACE("make_int_feasible_result", tout << "r: " << r << "\n"; display(tout););
#if 0
            switch (r) {
            case l_true: verbose_stream() << "sat\n"; break;
            case l_undef: verbose_stream() << "unknown\n"; break;
            case l_false: verbose_stream() << "unsat\n"; break;
            }
#endif
            return r;
        }

        // -----------------------
        //
        // Preprocessing
        //
        // -----------------------

        void register_propagation_eq(linear_equation const & eq) {
            // copy coeffs and vars to temporary buffers just to be safe
            m_var_buffer.reset();
            m_mpz_buffer.reset();
            unsigned sz = eq.size();
            for (unsigned j = 0; j < sz; j++) {
                m_mpz_buffer.push_back(eq.a(j));
                m_var_buffer.push_back(eq.x(j));
            }
            m_bounds.mk_eq(m_mpz_buffer.size(), m_mpz_buffer.c_ptr(), m_var_buffer.c_ptr());
        }

        // Copy constraints (only linear_equations at this point) to m_bounds.
        void init_bound_propagation_cnstrs() {
            SASSERT(scope_lvl() == 0);
            m_bounds.del_constraints(); 
            unsigned num_eqs = m_equations.size();
            for (unsigned i = 0; i < num_eqs; i++) {
                linear_equation const & eq = *(m_equations[i]);
                register_propagation_eq(eq);
            }
        }
        
        /**
           \brief Select a (unconstrained) variable in eq for elimination.
           If there is more than one option, then select the one with the fewest number of occurrences.
           If eq does not contain an unconstrained variable then return null_var.
           An integer variable is selected only if it has unary coefficient, and eq does not contain real variables.
        */
        var choose_elim_var(linear_equation const & eq, vector<unsigned_vector> const & use_list) const {
            bool has_real = false;
            unsigned sz = eq.size();
            for (unsigned i = 0; i < sz; i++) {
                if (!is_int(eq.x(i))) {
                    has_real = true;
                    break;
                }
            }
            var best_x = null_var;
            for (unsigned i = 0; i < sz; i++) {
                var x = eq.x(i);
                if (!is_unconstrained(x))
                    continue;
                if (is_int(x)) {
                    if (has_real)
                        continue;
                    if (!m_num_manager.is_one(eq.a(i)) && !m_num_manager.is_minus_one(eq.a(i)))
                        continue;
                }
                if (best_x == null_var || use_list[x].size() < use_list[best_x].size())
                    best_x = x;
            }
            return best_x;
        }

        /**
           \brief Update use list for replacing eq with new_eq, the use list of var except is not touched.
        */
        void update_use_list(unsigned eq_idx, linear_equation const & eq, linear_equation const & new_eq, vector<unsigned_vector> & use_list,
                             var except) {
            unsigned sz = eq.size();
            unsigned new_sz = new_eq.size();
            unsigned j = 0;
            unsigned new_j = 0;
            while (true) {
                if (j == sz) {
                    // add remaining variables in new_eq to use list
                    for (; new_j < new_sz; new_j++) 
                        use_list[new_eq.x(new_j)].push_back(eq_idx);
                    break;
                }
                if (new_j == new_sz) {
                    // remove remaining variables in eq from use list
                    for (; j < sz; j++) {
                        var x = eq.x(j);
                        if (x != except)
                            use_list[x].erase(eq_idx);
                    }
                    break;
                }
                var x     = eq.x(j);
                var new_x = new_eq.x(new_j);
                if (x < new_x) {
                    // variable x was removed
                    if (x != except)
                        use_list[x].erase(eq_idx);
                    j++;
                }
                else if (x > new_x) {
                    // variable new_x was added
                    use_list[new_x].push_back(eq_idx);
                    new_j++;
                }
                else {
                    // keep variable
                    j++;
                    new_j++;
                }
            }
        }

        /**
           \brief Eliminate x from all equations but eq_idx.
        */
        void eliminate_var_from_other_eqs(var x, unsigned eq_idx, vector<unsigned_vector> & use_list) {
            linear_equation * eq1 = m_equations[eq_idx];
            unsigned i1 = eq1->pos(x);
            SASSERT(i1 != UINT_MAX);
            mpz b1;
            m_num_manager.set(b1, eq1->a(i1));
            m_num_manager.neg(b1);
            unsigned_vector & occs = use_list[x];
            unsigned_vector::iterator it  = occs.begin();
            unsigned_vector::iterator end = occs.end();
            for (; it != end; ++it) {
                unsigned eq2_idx = *it;
                if (eq_idx == eq2_idx)
                    continue;
                linear_equation * eq2 = m_equations[eq2_idx];
                unsigned i2 = eq2->pos(x);
                SASSERT(i2 != UINT_MAX);
                mpz const & b2 = eq2->a(i2);
                linear_equation * new_eq2 = m_eq_manager.mk(b2, *eq1, b1, *eq2);
                CTRACE("arith_preprocess_new_bug", new_eq2->pos(x) != UINT_MAX,
                       tout << "x" << x << "\n";
                       tout << m_num_manager.to_string(b2) << " * "; m_eq_manager.display(tout, *eq1); tout << "\n";
                       tout << m_num_manager.to_string(b1) << " * "; m_eq_manager.display(tout, *eq2); tout << "\n";
                       tout << "----->\n";
                       m_eq_manager.display(tout, *new_eq2);
                       tout << "\n";);
                SASSERT(new_eq2 != 0);
                SASSERT(new_eq2->pos(x) == UINT_MAX);
                // update use list
                update_use_list(eq2_idx, *eq2, *new_eq2, use_list, x);
                m_eq_manager.del(eq2);
                m_equations[eq2_idx] = new_eq2;
            }
            // 
            m_num_manager.del(b1);
            occs.reset();
            occs.push_back(eq_idx); // x occurs only in eq_idx
        }
        
        void eliminate_var(var x, unsigned eq_idx, vector<unsigned_vector> & use_list) {
            eliminate_var_from_other_eqs(x, eq_idx, use_list);
            linear_equation * eq1 = m_equations[eq_idx];
            // remove x and eq_idx from use list
            unsigned_vector & occs = use_list[x];
            occs.reset();
            unsigned sz = eq1->size();
            for (unsigned i = 0; i < sz; i++) {
                var x_i = eq1->x(i); 
                use_list[x_i].erase(eq_idx);
            }
            // mark x as eliminated.
            m_eliminated[x] = true;
            m_elim_vars.push_back(elim_var_info(x, eq1));
        }

        void mk_tmp_use_list(vector<unsigned_vector> & use_list) {
            use_list.resize(num_vars());
            unsigned num_eqs = m_equations.size();
            for (unsigned eq_idx = 0; eq_idx < num_eqs; ++eq_idx) {
                linear_equation const & eq = *(m_equations[eq_idx]);
                unsigned sz = eq.size();
                for (unsigned i = 0; i < sz; i++) 
                    use_list[eq.x(i)].push_back(eq_idx);
            }
        }

        void remove_equations(svector<bool> const & to_remove) {
            unsigned num_eqs = m_equations.size();
            unsigned j = 0;
            for (unsigned i = 0; i < num_eqs; i++) {
                if (to_remove[i])
                    continue;
                linear_equation * eq = m_equations[i];
                var x_b = m_inv_basic[i];
                SASSERT(m_basic[x_b] == i);
                m_basic[x_b]   = j;
                m_equations[j] = eq;
                m_inv_basic[j] = x_b;
                j++;
            }

            TRACE("arith_preprocess_bug", for (unsigned i = 0; i < j; i++) display_eq_basics(tout, i););
            m_equations.shrink(j);
            m_inv_basic.shrink(j);
        }
        
        void elim_unconstrained_vars() {
            SASSERT(elim_var_applicable());
            // build temporary use list
            vector<unsigned_vector> use_list; 
            mk_tmp_use_list(use_list);

            // eliminate
            unsigned old_eliminated_vars = m_eliminated_vars;
            unsigned num_eqs = m_equations.size();
            svector<bool> to_remove;
            to_remove.resize(num_eqs, false);
            for (unsigned eq_idx = 0; eq_idx < num_eqs; ++eq_idx) {
                linear_equation * eq = m_equations[eq_idx];
                var x = choose_elim_var(*eq, use_list);
                if (x == null_var)
                    continue;
                var x_b = m_inv_basic[eq_idx];
                SASSERT(m_basic[x_b] == eq_idx);
                m_basic[x_b] = UINT_MAX; // x_b is not basic anymore.
                m_eliminated_vars++;
                TRACE("arith_preprocess", tout << "eliminating: x" << x << " using "; m_eq_manager.display(tout, *eq); tout << "\n";);
                SASSERT(!was_eliminated(x));
                SASSERT(!basic(x));
                eliminate_var(x, eq_idx, use_list);
                to_remove[eq_idx] = true;
            }

            report_st_progress(":elim-tableau-vars", m_eliminated_vars - old_eliminated_vars);

            remove_equations(to_remove);
        }

        // Compress basic variables ids after rows have been eliminated.
        void compress_basic_ids() {
            unsigned_vector id2var;
            unsigned num = num_vars();
            for (var x = 0; x < num; x++) {
                if (basic(x)) {
                    unsigned id = m_basic[x];
                    id2var.reserve(id+1, null_var);
                    id2var[id] = x;
                }
            }
            unsigned next_id = 0;
            unsigned sz = id2var.size();
            for (unsigned i = 0; i < sz; i++) {
                var x = id2var[i];
                if (x != null_var) {
                    m_basic[x] = next_id;
                    m_inv_basic[next_id] = x;
                    next_id++;
                }
            }
        }
        
        /**
           Make int_eqs[eq_idx] == true if eq_idx constains only integer variables.
        */
        void mark_int_eqs(svector<bool> & int_eqs) {
            unsigned num_eqs = m_equations.size();
            int_eqs.reset();
            for (unsigned i = 0; i < num_eqs; i++) {
                linear_equation const & eq = *(m_equations[i]);
                unsigned sz = eq.size();
                unsigned j;
                for (j = 0; j < sz; j++) {
                    if (!is_int(eq.x(j))) 
                        break;
                }
                int_eqs.push_back(j == sz);
            }
        }

        /**
           \brief Eliminate integer variable x by producing the equation  c * eq_idx1 + d * eq_idx2. 
           The coefficient of x in this equation is 1.
           This function replaces eq_idx1 with c * eq_idx1 + d * eq_idx2, and invokes eliminate_var(x, eq_idx1, use_list)
        */
        void eliminate_int_var(var x, unsigned eq_idx1, unsigned eq_idx2, mpz const & c, mpz const & d, vector<unsigned_vector> & use_list) {
            linear_equation * eq1         = m_equations[eq_idx1];
            linear_equation * new_eq1 = m_eq_manager.mk(c, *eq1, d, *(m_equations[eq_idx2]));
            SASSERT(new_eq1->pos(x) != UINT_MAX);
            SASSERT(m_num_manager.is_one(new_eq1->a(new_eq1->pos(x)))); // coefficient of x in the new equation is one.
            update_use_list(eq_idx1, *eq1, *new_eq1, use_list, null_var);
            m_eq_manager.del(eq1);
            m_equations[eq_idx1] = new_eq1;
            eliminate_var(x, eq_idx1, use_list);
        }

        void elim_int_unconstrained_vars() {
            SASSERT(elim_var_applicable());

            vector<unsigned_vector> use_list; 
            mk_tmp_use_list(use_list);

            unsigned old_eliminated_vars = m_eliminated_vars;
            
            svector<bool> int_eqs;
            mark_int_eqs(int_eqs);
            mpz c, d, g;

            numeral_manager & nm = m_num_manager;
            
            unsigned num_eqs = m_equations.size();
            svector<bool> to_remove;
            to_remove.resize(num_eqs, false);

            for (var x = 0; x < num_vars(); x++) {
                if (was_eliminated(x) || !is_int(x) || !is_unconstrained(x))
                    continue;
                TRACE("elim_int", tout << "visiting x" << x << "\n";);
                unsigned_vector & occs = use_list[x];
                unsigned_vector::iterator it  = occs.begin();
                unsigned_vector::iterator end = occs.end();
                for (; it != end; ++it) {
                    unsigned eq_idx1 = *it;
                    if (!int_eqs[eq_idx1])
                        continue; // skip: contains real variables...
                    linear_equation const & eq1 = *(m_equations[eq_idx1]);
                    SASSERT(elim_var_applicable(eq_idx1));
                    unsigned pos1 = eq1.pos(x);
                    if (pos1 == UINT_MAX)
                        continue;
                    mpz const & a1   = eq1.a(pos1);
                    if (nm.is_one(a1) || nm.is_minus_one(a1)) {
                        // easy case
                        m_eliminated_vars++;
                        var x_b = m_inv_basic[eq_idx1];
                        SASSERT(m_basic[x_b] == eq_idx1);
                        m_basic[x_b] = UINT_MAX; // x_b is not basic anymore.
                        eliminate_var(x, eq_idx1, use_list);
                        to_remove[eq_idx1] = true;
                        break;
                    }
                    unsigned_vector::iterator it2 = it+1;
                    for (; it2 != end; ++it2) {
                        unsigned eq_idx2 = *it2;
                        if (!int_eqs[eq_idx2])
                            continue;
                        linear_equation const & eq2 = *(m_equations[eq_idx2]);
                        SASSERT(elim_var_applicable(eq_idx2));
                        unsigned pos2 = eq2.pos(x);
                        if (pos2 == UINT_MAX)
                            continue;
                        mpz const & a2 = eq2.a(pos2);
                        if (nm.is_one(a2) || nm.is_minus_one(a2)) {
                            // easy case
                            m_eliminated_vars++;
                            var x_b = m_inv_basic[eq_idx2];
                            SASSERT(m_basic[x_b] == eq_idx2);
                            m_basic[x_b] = UINT_MAX; // x_b is not basic anymore.
                            eliminate_var(x, eq_idx2, use_list);
                            to_remove[eq_idx2] = true;
                            goto elim_int_var_processed;
                        }
                        nm.gcd(a1, a2, c, d, g);
                        if (nm.is_one(g)) {
                            TRACE("elim_int", tout << "found candidate eqs for eliminating x" << x << "\n";
                                  tout << "a1: " << nm.to_string(a1) << ", a2: " << nm.to_string(a2) << "\n";
                                  tout << "c: " << nm.to_string(c) << ", d: " << nm.to_string(d) << ", g: " << nm.to_string(g) << "\n";
                                  m_eq_manager.display(tout, eq1); tout << "\n";
                                  m_eq_manager.display(tout, eq2); tout << "\n";);
                            var x_b2 = m_inv_basic[eq_idx2];
                            // c * eq1 + d * eq2 --> generates an equation where x has coefficient 1.
                            // So, we can eliminate x, delete eq1 (or eq2), and replace x everywhere with c*eq1 + d*eq2.
                            eliminate_int_var(x, eq_idx1, eq_idx2, c, d, use_list);
                            var x_b = m_inv_basic[eq_idx1];
                            SASSERT(m_basic[x_b] == eq_idx1);
                            m_basic[x_b] = UINT_MAX; // x_b is not basic anymore.
                            to_remove[eq_idx1] = true;
                            m_eliminated_vars++;
                            // the basic variable of eq_idx2 may occur in many equations... eliminate it from all but eq_idx2
                            // the idea is to make sure that elim_var_applicable is true for all equations.
                            linear_equation const & new_eq2 = *(m_equations[eq_idx2]);
                            SASSERT(new_eq2.pos(x_b2) != UINT_MAX); // eq2 still contains its basic variable
                            SASSERT(elim_var_applicable(eq_idx2)); // the only basic variable in eq2 is still x_b2
                            eliminate_var_from_other_eqs(x_b2, eq_idx2, use_list);
                            goto elim_int_var_processed;
                        }
                    }
                }
            elim_int_var_processed:
                ;
            }
            nm.del(c);
            nm.del(d);
            nm.del(g);

            report_st_progress(":elim-int-tableau-vars", m_eliminated_vars - old_eliminated_vars);
            remove_equations(to_remove);
        }

        // assert axiom x == 0
        void assert_eq_zero_axiom(var x) {
            mpq zero(0);
            assert_upper(x, zero, false);
            assert_lower(x, zero, false);
        }

        // Eliminate variables fixed at zero from equations.
        bool elim_zero_vars() {
            bool eliminated = false;
            SASSERT(scope_lvl() == 0);
            unsigned num_eqs = m_equations.size();
            svector<bool> to_remove;
            to_remove.resize(num_eqs, false);
            for (unsigned eq_idx = 0; eq_idx < num_eqs; eq_idx++) {
                linear_equation * eq = m_equations[eq_idx];
                unsigned sz = eq->size();
                unsigned k;
                for (k = 0; k < sz; k++) {
                    var x_k = eq->x(k);
                    // To eliminate a basic variable, we have to
                    // create the LU factorization, and extract the actual row, and then select 
                    // a variable to enter the basis. Perhaps, it is not worth to do that at this point.
                    // It is better to wait the variable to leave the basis.
                    if (!basic(x_k) && m_bounds.is_zero(x_k))
                        break;
                }
                if (k == sz)
                    continue;
                // equation has zero variables
                m_var_buffer.reset();
                m_mpz_buffer.reset();
                for (k = 0; k < sz; k++) {
                    var x_k = eq->x(k);
                    if (!basic(x_k) && m_bounds.is_zero(x_k))
                        continue;
                    // keep non-zero vars and the basic variable
                    m_var_buffer.push_back(x_k);
                    m_mpz_buffer.push_back(eq->a(k));
                }
                
                SASSERT(m_var_buffer.size() < sz);
                eliminated = true;
                unsigned new_sz = m_var_buffer.size();
                SASSERT(new_sz != 0);
                linear_equation * new_eq = m_eq_manager.mk(new_sz, m_mpz_buffer.c_ptr(), m_var_buffer.c_ptr());
                if (new_eq != 0) {
                    m_equations[eq_idx] = new_eq;
                }
                else {
                    assert_eq_zero_axiom(m_var_buffer[0]);
                    SASSERT(new_sz == 1);
                    to_remove[eq_idx] = true;
                    var x_b = m_inv_basic[eq_idx];
                    m_basic[x_b] = UINT_MAX;
                    m_eliminated_vars++;
                }
                m_eq_manager.del(eq);
            }
            remove_equations(to_remove);
            return eliminated;
        }

        bool propagate_bounds() {
            unsigned qhead = m_bounds.qhead();
            m_bounds.propagate();
            if (m_bounds.inconsistent())
                return false;
            TRACE("propagate_bounds", tout << "propagate_bounds, m_use_asserted: " << m_use_asserted << "\n";);
            if (!m_use_asserted) {
                // update bad vars using new bounds
                bound_propagator::trail_iterator it  = m_bounds.begin_trail() + qhead;
                bound_propagator::trail_iterator end = m_bounds.end_trail();
                for (; it != end; ++it) {
                    var x         = it->x();
                    bool is_lower = it->is_lower();
                    TRACE("propagate_bounds", tout << "propagated x" << x << " is_lower: " << is_lower << "\n";);
                    if (is_lower) {
                        if (below_lower(x))
                            m_bad_vars.insert(x);
                    }
                    else {
                        if (above_upper(x))
                            m_bad_vars.insert(x);
                    }
                }
            }
            return true;
        }

        void init_eq_occs(unsigned eq_idx) {
            linear_equation const & eq = *(m_equations[eq_idx]);
            unsigned sz = eq.size();
            for (unsigned i = 0; i < sz; i++) 
                m_eq_occs[eq.x(i)].push_back(eq_occ(eq_idx, i));
        }

        void init_eq_occs() {
            m_eq_occs.reset();
            m_eq_occs.resize(num_vars());
            unsigned num_eqs = m_equations.size();
            for (unsigned eq_idx = 0; eq_idx < num_eqs; ++eq_idx) {
                init_eq_occs(eq_idx);
            }
        }

        /**
           \brief We apply variable elimination only if 
           For all equation eq, the only and only one basic variable x_b in eq is m_inv_basic[eq].
           
           This condition prevents us from ending up with a basis that corresponds to a
           singular matrix.
           
           After compilation, the set of equations always satisfies this condition, since
           the basic variable "owning" each equation is the slack introduced during compilation.
        */
        bool elim_var_applicable(unsigned eq_idx) const {
            linear_equation const & eq = *(m_equations[eq_idx]);
            unsigned sz = eq.size();
            for (unsigned i = 0; i < sz; i++) {
                var x = eq.x(i);
                if (basic(x) && m_basic[x] != eq_idx)
                    return false;
            }
            return true;
        }
        
        bool elim_var_applicable() const {
            unsigned num_eqs = m_equations.size();
            for (unsigned eq_idx = 0; eq_idx < num_eqs; eq_idx++) {
                if (!elim_var_applicable(eq_idx))
                    return false;
            }
            return true;
        }

        void preprocess() {
            CASSERT("arith", check_invariant());
            IF_VERBOSE(ST_VERBOSITY_LVL, display_status(verbose_stream()););

            TRACE("arith_preprocess", tout << "eqs before elimination\n"; display_eqs(tout););
            
            if (m_elim_vars_enabled && elim_var_applicable()) {
                elim_unconstrained_vars();
                // TODO: the following transformation is producing a singular basis
                if (m_elim_int_vars_enabled)
                    elim_int_unconstrained_vars();
            }

            init_bound_propagation_cnstrs();
            if (!propagate_bounds())
                return; // inconsistency detected.

            IF_VERBOSE(ST_VERBOSITY_LVL, display_status(verbose_stream()););

            TRACE("arith_preprocess", tout << "eqs after elimination\n"; display_eqs(tout); display_eliminated_vars(tout););

#if 1
            if (elim_zero_vars()) {
                init_bound_propagation_cnstrs();
                propagate_bounds();
                IF_VERBOSE(ST_VERBOSITY_LVL, display_status(verbose_stream()););
            }
#endif

            init_eq_occs();

            CASSERT("arith", check_invariant());
            TRACE("arith_preprocess_bug", for (unsigned i = 0; i < m_equations.size(); i++) display_eq_basics(tout, i););

            init_lu();

            TRACE("arith_int_preprocess", display_unconstrained_vars(tout); display_eqs(tout););

            CASSERT("arith", check_invariant());
            TRACE("arith_preprocess", display(tout););

            //  tst_random_pivoting(m_lu_double, 2000);
            //  tst_random_pivoting(m_lu_mpq, 2000);
        }

        // -----------------------
        //
        // Cuts
        //
        // -----------------------
        
        /**
           \brief Move non-basic variables to bounds.
        */
        void move_nonbasic_to_bounds() {
            mpq_inf old_val;
            unsigned num = num_vars();
            for (var x = 0; x < num; x++) {
                if (basic(x))
                    continue;
                if (at_lower(x) || at_upper(x))
                    continue;
                m_num_inf_manager.set(old_val, m_values[x]);
                if (has_lower(x)) 
                    lower2value(x);
                else if (has_upper(x))
                    upper2value(x);
                else 
                    continue;
                update_dependents(m_lu_mpq, m_values, m_num_inf_manager, x, old_val);
            }
            m_num_inf_manager.del(old_val);
        }

        bool is_jdm_cut_applicable(mpq const & k, var x_i, lu_mpq::dense_vector const & row) {
            if (!m_num_inf_manager.is_rational(m_values[x_i]))
                return false;
            numeral_manager & nm = m_num_manager;
            mpq a;
            nm.mul(m_values[x_i].first, k, a);
            if (nm.is_int(a)) {
                nm.del(a);
                return false;
            }
            // check if cut is applicable
            lu_mpq::dense_vector::iterator it  = row.begin_non_zeros();
            lu_mpq::dense_vector::iterator end = row.end_non_zeros();
            for (; it != end; ++it) {
                var x_j = *it;
                if (!is_int(x_j)) {
                    TRACE("cut", tout << "failed: row constains non int var\n";);
                    return false;
                }
                m_num_manager.mul(k, row[x_j], a);
                if (nm.is_int(a)) {
                    // integer coeffs can be ignored when x_j is assigned to an integer
                    if (!m_num_inf_manager.is_int(m_values[x_j]))
                        return false;
                    continue; 
                }
                if (!at_lower(x_j) && !at_upper(x_j)) {
                    TRACE("cut", tout << "failed: variable is not at bound x" << x_j << "\n";);
                    return false;
                }
            }
            nm.del(a);
            return true;
        }

        bool mk_jdm_cut(mpq const & k, var x_i, lu_mpq::dense_vector const & row, mpq_buffer & as, var_buffer & xs, mpq & c) {
            if (!is_jdm_cut_applicable(k, x_i, row))
                return false;
            numeral_manager & nm = m_num_manager;
            SASSERT(nm.is_pos(k));
            as.reset();
            xs.reset();
            nm.reset(c);
            mpq a, a_prime;
            nm.mul(m_values[x_i].first, k, c);
            nm.ceil(c, c);
            lu_mpq::dense_vector::iterator it  = row.begin_non_zeros();
            lu_mpq::dense_vector::iterator end = row.end_non_zeros();
            for (; it != end; ++it) {
                var x_j = *it;
                nm.mul(row[x_j], k, a);
                if (nm.is_int(a)) {
                    // I
                    nm.addmul(c, a, m_values[x_j].first, c);
                    // ignore monomial
                }
                else {
                    if (nm.is_neg(a)) {
                        if (at_lower(x_j)) {
                            // L-
                            // doesn't contribute to c.
                            // add -a*x_j
                            nm.neg(a);
                            as.push_back(a);
                        }
                        else {
                            // U-
                            nm.floor(a, a_prime);
                            nm.addmul(c, a_prime, m_values[x_j].first, c);
                            // new coeff floor(a_ij) - a_ij
                            nm.sub(a_prime, a, a_prime);
                            as.push_back(a_prime);
                        }
                    }
                    else {
                        if (at_lower(x_j)) {
                            // L+
                            nm.ceil(a, a_prime);
                            nm.addmul(c, a_prime, m_values[x_j].first, c);
                            // new coeff ceil(a_ij) - a_ij
                            nm.sub(a_prime, a, a_prime);
                            as.push_back(a_prime);
                        }
                        else {
                            // U+
                            // doesn't contribute to c
                            // add -a*x_j
                            nm.neg(a);
                            as.push_back(a);
                        }
                    }
                    xs.push_back(x_j);
                }
            }
            TRACE("cut",
                  tout << "new cut:\n"; 
                  for (unsigned i = 0; i < xs.size(); i++) {
                      if (i > 0) tout << " + ";
                      tout << nm.to_string(as[i]) << "*x" << xs[i];
                  }
                  tout << " >= " << nm.to_string(c) << "\n";
                  tout << "\n";);
            nm.del(a);
            nm.del(a_prime);
            return true;
        }

        bool mk_jdm_dual_cut(mpq const & k, var x_i, lu_mpq::dense_vector const & row, mpq_buffer & as, var_buffer & xs, mpq & c) {
            if (!is_jdm_cut_applicable(k, x_i, row))
                return false;
            numeral_manager & nm = m_num_manager;
            SASSERT(nm.is_pos(k));
            as.reset();
            xs.reset();
            nm.reset(c);
            mpq a, a_prime;
            nm.mul(m_values[x_i].first, k, c);
            nm.floor(c, c);
            lu_mpq::dense_vector::iterator it  = row.begin_non_zeros();
            lu_mpq::dense_vector::iterator end = row.end_non_zeros();
            for (; it != end; ++it) {
                var x_j = *it;
                nm.mul(row[x_j], k, a);
                if (nm.is_int(a)) {
                    // I
                    nm.addmul(c, a, m_values[x_j].first, c);
                    // ignore monomial
                }
                else {
                    if (nm.is_neg(a)) {
                        if (at_lower(x_j)) {
                            // L-
                            nm.floor(a, a_prime);
                            nm.addmul(c, a_prime, m_values[x_j].first, c);
                            // new coeff floor(a_ij) - a_ij
                            nm.sub(a_prime, a, a_prime);
                            as.push_back(a_prime);
                        }
                        else {
                            // U-
                            // doesn't contribute to c.
                            // add -a*x_j
                            nm.neg(a);
                            as.push_back(a);
                        }
                    }
                    else {
                        if (at_lower(x_j)) {
                            // L+
                            // doesn't contribute to c
                            // add -a*x_j
                            nm.neg(a);
                            as.push_back(a);
                        }
                        else {
                            // U+
                            nm.ceil(a, a_prime);
                            nm.addmul(c, a_prime, m_values[x_j].first, c);
                            // new coeff ceil(a_ij) - a_ij
                            nm.sub(a_prime, a, a_prime);
                            as.push_back(a_prime);
                        }
                    }
                    xs.push_back(x_j);
                }
            }
            TRACE("cut",
                  tout << "new cut:\n"; 
                  for (unsigned i = 0; i < xs.size(); i++) {
                      if (i > 0) tout << " + ";
                      tout << nm.to_string(as[i]) << "*x" << xs[i];
                  }
                  tout << " <= " << nm.to_string(c) << "\n";
                  tout << "\n";);
            nm.del(a);
            nm.del(a_prime);
            return true;
        }
        
        // -----------------------
        //
        // Status
        //
        // -----------------------

        unsigned matrix_size() const {
            unsigned r = 0;
            equations::const_iterator it  = m_equations.begin();
            equations::const_iterator end = m_equations.end();
            for (; it != end; ++it)
                r += (*it)->size();
            return r;
        }

        void display_status(std::ostream & out) {
            out << "(arith :vars " << num_vars() << " :eliminated " << m_elim_vars.size() << " :eqs " << m_equations.size() 
                << " :matrix-size " << matrix_size() << ")\n";
        }

        // -----------------------
        //
        // Pretty printing
        //
        // -----------------------

        void display_int_infeasible_rows(std::ostream & out) {
            mpq c;
            out << "rows of int infeasible vars:\n";
            lu_mpq::dense_vector & row = m_lu_mpq.get_tmp_row(num_vars());
            for (var x = 0; x < num_vars(); x++) {
                if (!basic(x) || was_eliminated(x) || int_feasible(x))
                    continue;
                row.reset();
                get_row_mpq(m_basic[x], row, true, m_use_asserted, true);
                out << "x" << x << " -> " << m_num_inf_manager.to_string(m_values[x]) << " : "; row.display_pol(out); out << "\n";
                mk_jdm_cut(mpq(1), x, row, m_mpq_buffer, m_var_buffer, c);
                mk_jdm_dual_cut(mpq(1), x, row, m_mpq_buffer, m_var_buffer, c);
            }
            m_num_manager.del(c);
        }

        /**
           \brief Display unbounded variables that were not eliminated.
        */
        void display_unconstrained_vars(std::ostream & out) const {
            for (var x = 0; x < num_vars(); x++) {
                if (!was_eliminated(x) && is_unconstrained(x)) {
                    out << "x" << x << " ";
                }
            }
            out << "\n";
        }
        
        void display_ineq_cnstr(std::ostream & out, ineq_cnstr const & c) const {
            out << "p" << c.m_atom << " := x" << c.m_x << " " << (c.m_lower ? ">=" : "<=") << " " << m_num_manager.to_string(c.m_k) << "\n";
        }

        void display_ineq_cnstrs(std::ostream & out) const {
            out << "ineq-constraints:\n";
            for (unsigned i = 0; i < m_ineq_cnstrs.size(); i++) {
                display_ineq_cnstr(out, m_ineq_cnstrs[i]);
            }
        }

        void display_eliminated_vars(std::ostream & out) const {
            out << "eliminated variables:\n";
            elim_vars::const_iterator it  = m_elim_vars.begin();
            elim_vars::const_iterator end = m_elim_vars.end();
            for (; it != end; ++it) {
                out << "x" << it->first << " --> ";
                m_eq_manager.display(out, *(it->second));
                out << "\n";
            }
        }
        
        void display_eq_basics(std::ostream & out, unsigned eq_idx) const {
            out << "eq " << eq_idx << ":";
            linear_equation const & eq = *(m_equations[eq_idx]);
            unsigned sz = eq.size();
            for (unsigned i = 0; i < sz; i++) {
                if (basic(eq.x(i)))
                    out << " x" << eq.x(i) << "|" << m_basic[eq.x(i)];
            }
            out << "\n";
        }

        void display_eqs(std::ostream & out) const {
            out << "equations:\n";
            for (unsigned i = 0; i < m_equations.size(); i++) {
                linear_equation const & eq = *(m_equations[i]);
                out << "eq " << i << ": ";
                m_eq_manager.display(out, eq);
                out << "\n";
            }
        }

        void display_basic(std::ostream & out) const {
            out << "basic:";
            for (unsigned x = 0; x < num_vars(); x++) {
                if (basic(x))
                    out << " (x" << x << " -> " << m_basic[x] << ")";
            }
            out << "\n";
        }

        void display_definitions(std::ostream & out) const {
            out << "definitions:\n";
            for (unsigned i = 0; i < num_vars(); i++) {
                out << "x" << std::left << std::setw(6) << i << " : ";
                if (m_var2expr.get(i) == 0)
                    out << "<internal>";
                else
                    out << mk_ismt2_pp(m_var2expr.get(i), m, 10);
                out << "\n";
            }
        }
        
        template<typename LU>
        void display_LU(std::ostream & out, LU const & _lu) const {
            _lu.display(out);
            _lu.display(out, &m_inv_basic);
        }

        void display_bad_vars(std::ostream & out) const {
            if (m_bad_vars.empty()) {
                out << "all constraints are satisfied\n";
                return;
            }
            out << "bad vars: ";
            var_set::iterator it  = m_bad_vars.begin();
            var_set::iterator end = m_bad_vars.end();
            for (; it != end; ++it) {
                out << "x" << *it << " ";
            }
            out << "\n";
        }

        void display_int_bad_vars(std::ostream & out) const {
            if (m_int_bad_vars.empty()) {
                out << "integrality constraints are satisfied\n";
                return;
            }
            out << "int bad vars: ";
            var_set::iterator it  = m_int_bad_vars.begin();
            var_set::iterator end = m_int_bad_vars.end();
            for (; it != end; ++it) {
                out << "x" << *it << " ";
            }
            out << "\n";
        }
        
        void display_assignment(std::ostream & out) const {
            out << "assignment:\n";
            for (var x = 0; x < num_vars(); x++) {
                if (was_eliminated(x))
                    continue;
                if (m_use_approx) {
                    out << "x" << x << " -> " << m_approx_values[x];
                }
                else {
                    out << "x" << x << " -> " << m_num_inf_manager.to_string(m_values[x]);
                }
                if (is_int(x))
                    out << " *";
                out << "\n";
            }
        }

        void display_LU(std::ostream & out) const {
            if (m_use_approx)
                m_lu_double.display(out);
            else 
                m_lu_mpq.display(out);
        }

        void display_bounds(std::ostream & out) const {
            // display only bounds of variables that were not eliminated.
            out << "bounds:\n";
            for (var x = 0; x < num_vars(); x++) {
                if (was_eliminated(x))
                    continue;
                if (m_use_approx)
                    bp().display_var_bounds(out, x, true, false);
                else
                    bp().display_var_bounds(out, x, false, true);
                out << "\n";
            }
        }
        
        void display(std::ostream & out) const {
            display_definitions(out);
            display_basic(out);
            display_eqs(out);
            display_bounds(out);
            display_LU(out);
            display_assignment(out);
            display_bad_vars(out);
            display_int_bad_vars(out);
            display_ineq_cnstrs(out);
            display_eliminated_vars(out);
        }

        // -----------------------
        //
        // Invariants
        //
        // -----------------------

        bool check_bounds_satisfied() const {
            for (var x = 0; x < num_vars(); x++) {
                CTRACE("arith_bug", above_upper(x) || below_lower(x), tout << "bad var: x" << x << "\n"; display(tout););
                SASSERT(!above_upper(x));
                SASSERT(!below_lower(x));
            }
            return true;
        }

        /**
           \brief Check if m_bad_vars contains all variables not satisfying their bounds.
        */
        bool check_bad_vars() const {
            if (!inconsistent()) {
                for (var x = 0; x < num_vars(); x++) {
                    if (above_upper(x) || below_lower(x)) {
                        CTRACE("arith_bug", !m_bad_vars.contains(x), tout << "missing bad var: x" << x << "\n"; display(tout););
                        SASSERT(m_bad_vars.contains(x));
                    }
                }
            }
            return true;
        }

        /**
           \brief When precise mode is on, this method checks if the assignment of the basic 
           variables is consistent with the non-basic ones.
        */
        bool check_basic_assignment_core() {
            if (m_use_approx)
                return true;
            unsigned num = m_equations.size();
            lu_mpq::dense_vector & row = m_lu_mpq.get_tmp_row(num_vars());
            mpq_inf val;
            mpq_inf aux;
            for (unsigned eq_idx = 0; eq_idx < num; eq_idx++) {
                var x_b = m_inv_basic[eq_idx];
                SASSERT(m_basic[x_b] == eq_idx);
                row.reset();
                get_row_mpq(eq_idx, row, true, m_use_asserted, true);
                m_num_inf_manager.reset(val);
                lu_mpq::dense_vector::iterator it  = row.begin_non_zeros();
                lu_mpq::dense_vector::iterator end = row.end_non_zeros();
                for (; it != end; ++it) {
                    var x_n = *it;
                    SASSERT(nonbasic(x_n));
                    if (m_num_manager.is_zero(row[x_n])) 
                        continue;
                    m_num_inf_manager.mul(m_values[x_n], row[x_n], aux);
                    m_num_inf_manager.add(val, aux, val);
                }
                m_num_inf_manager.neg(val);
                CTRACE("arith_bug", !m_num_inf_manager.eq(m_values[x_b], val), 
                       tout << "x_b: " << x_b << " val: " << m_num_inf_manager.to_string(m_values[x_b]) 
                       << ", computed val: " << m_num_inf_manager.to_string(val) << "\n";
                       tout << "row: "; row.display_pol(tout); tout << "\n";
                       display(tout););
                SASSERT(m_num_inf_manager.eq(m_values[x_b], val));
            }
            m_num_inf_manager.del(val);
            m_num_inf_manager.del(aux);
            return true;
        }

        bool check_basic_assignment() const {
            return const_cast<imp*>(this)->check_basic_assignment_core();
        }

        bool check_eqs_satisfied_core() {
            mpq_inf val;
            mpq_inf aux;
            unsigned num = m_equations.size();
            for (unsigned eq_idx = 0; eq_idx < num; eq_idx++) {
                linear_equation const & eq = *(m_equations[eq_idx]);
                m_num_inf_manager.reset(val);
                unsigned sz = eq.size();
                for (unsigned i = 0; i < sz; i++) {
                    var x = eq.x(i);
                    mpz const & a = eq.a(i);
                    m_num_inf_manager.mul(m_values[x], a, aux);
                    m_num_inf_manager.add(val, aux, val);
                }
                CTRACE("arith_bug", !m_num_inf_manager.is_zero(val), 
                       m_eq_manager.display(tout, eq); tout << "\nval: " << m_num_inf_manager.to_string(val) << "\n";
                       display(tout););
                SASSERT(m_num_inf_manager.is_zero(val));
            }
            m_num_inf_manager.del(val);
            m_num_inf_manager.del(aux);
            return true;
        }

        bool check_eqs_satisfied() const {
            if (m_use_approx)
                return true;
            return const_cast<imp*>(this)->check_eqs_satisfied_core();
        }
            
        // Debugging: check eq contains at least one basic variable. 
        bool check_has_basic(unsigned eq_idx) const {
            linear_equation const & eq = *(m_equations[eq_idx]);
            for (unsigned i = 0; i < eq.size(); i++) {
                if (basic(eq.x(i)))
                    return true;
            }
            TRACE("arith_bug", m_eq_manager.display(tout, eq); tout << "\n";);
            UNREACHABLE();
            return false;
        }
        
        // Debugging: check eq does not contain eliminated variables
        bool check_no_elim_var(linear_equation const & eq) const {
            for (unsigned i = 0; i < eq.size(); i++) {
                SASSERT(!was_eliminated(eq.x(i)));
            }
            return true;
        }

        svector<bool> m_visited;

        bool check_invariant() const {
            SASSERT(m_inv_basic.size() == m_equations.size());
            svector<bool> & visited = const_cast<imp*>(this)->m_visited;

            visited.reserve(m_equations.size(), false);
            
            unsigned num_basic = 0;
            // check basic variables
            for (unsigned x = 0; x < num_vars(); x++) {
                if (basic(x)) {
                    SASSERT(m_inv_basic[m_basic[x]] == x);
                    num_basic++;
                    SASSERT(!was_eliminated(x));
                    SASSERT(m_basic[x] < m_equations.size());
                    SASSERT(!visited[m_basic[x]]);
                    visited[m_basic[x]] = true;
                }
            }
            SASSERT(num_basic == m_equations.size());
            for (unsigned x = 0; x < num_vars(); x++) {
                if (basic(x)) {
                    SASSERT(visited[m_basic[x]]);
                    visited[m_basic[x]] = false;
                }
            }
            
            // check all eqs contain at least one basic variable and no eliminated variable
            for (unsigned i = 0; i < m_equations.size(); i++) {
                SASSERT(m_basic[m_inv_basic[i]] == i);
                linear_equation const & eq = *(m_equations[i]);
                SASSERT(check_no_elim_var(eq));
                SASSERT(check_has_basic(i));
            }

            // check ineq_cnstrs
            for (unsigned i = 0; i < m_ineq_cnstrs.size(); i++) {
                SASSERT(m_atom2ineq_cnstr[m_ineq_cnstrs[i].m_atom] == i);
                SASSERT(!was_eliminated(m_ineq_cnstrs[i].m_x));
            }
            
            // check m_atom2ineq_cnstr
            for (unsigned i = 0; i < m_atom2ineq_cnstr.size(); i++) {
                if (m_atom2ineq_cnstr[i] != UINT_MAX) {
                    SASSERT(m_ineq_cnstrs[m_atom2ineq_cnstr[i]].m_atom == i);
                }
            }
            
            return true;
        }

    };
    
    arith::arith(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    arith::~arith() {
        imp * d = m_imp;
        #pragma omp critical (smt_arith)
        {
            m_imp = 0;
        }
        dealloc(d);
    }

    void arith::updt_params(params_ref const & p) {
        m_params = p;
        m_imp->updt_params(p);
    }

    void arith::assert_axiom(expr * t, bool neg) {
        TRACE("arith", tout << "asserting neg: " << neg << "\n" << mk_ismt2_pp(t, m_imp->m) << "\n";);
        m_imp->mk_ineq(t, neg, null_atom_id);
    }

    void arith::mk_atom(expr * t, atom_id p) {
        TRACE("arith", tout << "mk_atom p: " << p << "\n" << mk_ismt2_pp(t, m_imp->m) << "\n";);
        m_imp->mk_ineq(t, false, p);
    }
    
    void arith::asserted(atom_id id, bool is_true) {
    }
    
    bool arith::inconsistent() const {
        // TODO
        return false;
    }

    void arith::push() {
    }
    
    void arith::pop(unsigned num_scopes) {
    }
    
    void arith::set_cancel(bool f) {
        #pragma omp critical (smt_arith) 
        {
            if (m_imp)
                m_imp->set_cancel(f);
        }
    }

    void arith::reset() {
        ast_manager & m = m_imp->m;
        #pragma omp critical (smt_arith) 
        {
            dealloc(m_imp);
            m_imp = alloc(imp, m, m_params);
        }
    }

    void arith::preprocess() {
        m_imp->preprocess();
    }
    
    void arith::simplify() {
    }
    
    void arith::display(std::ostream & out) const {
        m_imp->display(out);
    }

    void arith::collect_statistics(statistics & st) const {
        m_imp->collect_statistics(st);
    }

    void arith::reset_statistics() {
        m_imp->reset_statistics();
    }

    lbool arith::check() {
        m_imp->make_feasible();
        return m_imp->make_int_feasible();
    }

    void arith::mk_model(model * md) {
        m_imp->mk_model(md);
    }

};   

