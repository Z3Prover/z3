/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    pb2bv_tactic.cpp

Abstract:

    Tactic for converting Pseudo-Boolean constraints to BV

Author:

    Christoph (cwinter) 2012-02-15

Notes:

--*/
#include"tactical.h"
#include"cooperate.h"
#include"bound_manager.h"
#include"bool_rewriter.h"
#include"rewriter_def.h"
#include"ref_util.h"
#include"arith_decl_plugin.h"
#include"trace.h"
#include"ast_smt2_pp.h"
#include"expr_substitution.h"
#include"filter_model_converter.h"
#include"pb2bv_model_converter.h"
#include"pb2bv_tactic.h"

class pb2bv_tactic : public tactic {
public:
    struct non_pb {};

    struct only_01_visitor {
        typedef rational numeral;
        ast_manager   & m;
        arith_util    & m_util;
        bound_manager & m_bm;
    
        only_01_visitor(arith_util & u, bound_manager & bm):
            m(u.get_manager()),
            m_util(u),
            m_bm(bm) {
        }
    
        void throw_non_pb(expr * n) {
            TRACE("pb2bv", tout << "Not pseudo-Boolean: " << mk_ismt2_pp(n, m) << "\n";);
            throw non_pb();
        }
    
        void operator()(var * n) { 
            throw_non_pb(n);
        }
    
        void operator()(app * n) {            
            family_id fid = n->get_family_id();
            if (fid == m.get_basic_family_id()) {
                // all basic family ops (but term-ite and distinct) are OK
                if (m.is_term_ite(n) || m.is_distinct(n))
                    throw_non_pb(n);
                return;
            }
        
            if (fid == m_util.get_family_id()) {
                // check if linear
                switch (n->get_decl_kind()) {
                case OP_LE:  case OP_GE: case OP_LT: case OP_GT:
                case OP_ADD: case OP_NUM:
                    return;
                case OP_MUL:
                    if (n->get_num_args() != 2)
                        throw_non_pb(n);
                    if (!m_util.is_numeral(n->get_arg(0)))
                        throw_non_pb(n);
                    return;
                default:
                    throw_non_pb(n);
                }
            }
        
            if (is_uninterp_const(n)) {
                if (m.is_bool(n))
                    return; // boolean variables are ok
                if (m_util.is_int(n)) {
                    numeral l, u; bool s;
                    if (m_bm.has_lower(n, l, s) &&
                        m_bm.has_upper(n, u, s) && 
                        (l.is_zero() || l.is_one()) &&
                        (u.is_zero() || u.is_one()))
                        return;
                }
            }
        
            throw_non_pb(n);
        }
    
        void operator()(quantifier * n) { 
            throw_non_pb(n);
        }
    };
private:

    struct imp {
        typedef rational numeral;

        ast_manager &              m;
        bound_manager              m_bm;        
        bool_rewriter              m_b_rw;
        arith_util                 m_arith_util;
        bv_util                    m_bv_util;
        expr_dependency_ref_vector m_new_deps;
        
        bool                       m_produce_models;
        bool                       m_produce_unsat_cores;
        
        unsigned                   m_all_clauses_limit;
        unsigned                   m_cardinality_limit;
        unsigned long long         m_max_memory;
        // m_const2bit should be a map, since we want constant time access to it, and avoid quadratic behavior.
        // It is ok to use a vector at the model converter because we don't need to search that vector.
        obj_map<func_decl, expr*>  m_const2bit;
        obj_map<func_decl, expr*>  m_not_const2bit;
        expr_ref_vector            m_temporary_ints;

        expr_dependency_ref        m_used_dependencies; 
    
        struct lit {
            expr * m_v;
        public:
            lit(expr * v, bool sign = false):m_v(TAG(expr*, v, sign)) {}
            bool sign() const { return GET_TAG(m_v) == 1; }
            expr * var() const { return UNTAG(expr*, m_v); }
            void neg() { 
    #ifdef Z3DEBUG
                bool s = sign();
    #endif
                m_v = TAG(expr*, UNTAG(expr*, m_v), !sign()); 
                SASSERT(s == !sign());
            }
        };

        struct monomial {
            numeral m_a;
            lit     m_lit;
            monomial(lit l):m_a(1), m_lit(l) {}
            monomial(numeral const & a, lit l):m_a(a), m_lit(l) {}        
        };

        typedef vector<monomial> polynomial;

        struct monomial_lt {
            bool operator()(monomial const & m1, monomial const & m2) const { return m1.m_a > m2.m_a; }
        };

        enum constraint_kind { EQ, GE, LE };

        struct failed {};

        struct visitor {
            imp & m_owner;
            
            visitor(imp & o):m_owner(o) {}
            
            void throw_failed(expr * n) {
                throw failed();
            }
            
            void operator()(var * n) { 
                throw_failed(n);
            }
            
            void operator()(app * n) { 
            }
            
            void operator()(quantifier * n) { 
                throw_failed(n);
            }
        };

        void checkpoint() {
            cooperate("pb2bv");
            if (memory::get_allocation_size() > m_max_memory)
                throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
        }

        void quick_pb_check(goal_ref const & g) {
            expr_fast_mark1 visited;
            only_01_visitor proc(m_arith_util, m_bm);
            unsigned sz = g->size();
            for (unsigned i = 0; i < sz; i++) {
                expr * f = g->form(i);
                for_each_expr_core<only_01_visitor, expr_fast_mark1, true, true>(proc, visited, f);
            }
        }

        struct rw_cfg : public default_rewriter_cfg {
            ast_manager & m;
            imp &         owner;
            expr_ref      m_saved_res;

            rw_cfg(imp & o):
                m(o.m),
                owner(o),
                m_saved_res(m) {
            }

            bool max_steps_exceeded(unsigned num_steps) const { 
                cooperate("pb2bv");
                if (memory::get_allocation_size() > owner.m_max_memory)
                    throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
                return false;
            }

            bool get_subst(expr * s, expr * & t, proof * & t_pr) { 
                t_pr = 0;
                if (owner.is_constraint_core(s)) {
                    owner.convert(to_app(s), m_saved_res, true, false);
                    t = m_saved_res;
                    TRACE("pb2bv_convert", tout << mk_ismt2_pp(s, m) << "\n-->\n" << mk_ismt2_pp(t, m) << "\n";);
                    return true;
                }
                return false;
            }
        };

        struct rw : public rewriter_tpl<rw_cfg> {
            rw_cfg m_cfg;
        
            rw(imp & o):
                rewriter_tpl<rw_cfg>(o.m, false, m_cfg),
                m_cfg(o) {
            }
        };

        rw m_rw;

        struct pb2bv_all_clauses {
            imp &              m_owner;
            ast_manager &      m;
            unsigned           m_size;
            vector<numeral>    m_sums; 
            expr_ref_vector    m_lits;
            ptr_vector<expr>   m_cls;
            polynomial const * m_pol;
            expr_ref_vector    m_result;
        
            pb2bv_all_clauses(imp & owner):
                m_owner(owner),
                m(m_owner.m),
                m_lits(m),
                m_result(m) {
            }

            void init_lits(polynomial const & p) {
                polynomial::const_iterator it  = p.begin();
                polynomial::const_iterator end = p.end();
                for (; it != end; ++it)
                    m_lits.push_back(m_owner.mon_lit2lit(it->m_lit));
            }

            void init_sums(polynomial const & p) {
                SASSERT(m_sums.empty());
                m_size = p.size();
                m_sums.resize(m_size);
                unsigned i  = m_size;
                while (i > 0) {
                    --i;
                    if (i == m_size - 1)
                        m_sums[i] = p[i].m_a;
                    else
                        m_sums[i] = p[i].m_a + m_sums[i+1];
                }
            }

            void process(unsigned idx, numeral c) {
                if (c.is_nonpos())
                    return;

                if (idx == m_size || m_sums[idx] < c) {
                    SASSERT(c.is_pos());
                    // conflict 0 >= c > 0
                    switch (m_cls.size()) {
                    case 0:  m_result.push_back(m.mk_false()); break;
                    case 1:  m_result.push_back(m_cls[0]); break;
                    default: m_result.push_back(m.mk_or(m_cls.size(), m_cls.c_ptr()));
                    }
                    return;
                }

                m_owner.checkpoint();

                m_cls.push_back(m_lits.get(idx));
                process(idx+1, c);
                m_cls.pop_back();
                process(idx+1, c - (*m_pol)[idx].m_a);
            }
        
            void operator()(polynomial const & m_p, numeral const & m_c, expr_ref & r) {
                m_pol     = &(m_p);
                init_sums(m_p);
                init_lits(m_p);
                process(0, m_c);
                m_owner.m_b_rw.mk_and(m_result.size(), m_result.c_ptr(), r);
            }
        };

        void display(std::ostream & out, polynomial const & m_p, numeral const & m_c) const {
            polynomial::const_iterator it  = m_p.begin();
            polynomial::const_iterator end = m_p.end();
            for (bool first = true; it != end; ++it) {
                if (!first)
                    out << " + ";
                first = false;
                if (!it->m_a.is_one())
                    out << it->m_a << "*";
                if (it->m_lit.sign())
                    out << "~";
                out << mk_ismt2_pp(it->m_lit.var(), m);
            }
            out << " >= " << m_c << "\n";
        }

        expr * int2lit(app * x, bool sign = false) {
            func_decl * fd = x->get_decl();
            obj_map<func_decl, expr*> & const2lit = sign ? m_not_const2bit : m_const2bit;

            expr * r = 0;
            const2lit.find(fd, r);
            if (r != 0)
                return r;

            r = m.mk_fresh_const(0, m.mk_bool_sort());
            expr * not_r = m.mk_not(r);
            m_const2bit.insert(fd, r);
            m_not_const2bit.insert(fd, not_r);
            m.inc_ref(fd);
            m.inc_ref(r);
            m.inc_ref(not_r);
         
            return sign ? not_r : r;
        }

        expr * mon_lit2lit(monomial const & mo) {
            return int2lit(to_app(mo.m_lit.var()), mo.m_lit.sign());
        }

        expr * mk_unit(expr * t, bool sign) {
            return mon_lit2lit(lit(t, sign));
        }

        static bool is_cardinality(polynomial const & m_p, numeral const & m_c) {
            for (unsigned i = 0; i < m_p.size(); i++) {
                if (!m_p[i].m_a.is_one())
                    return false;
            }
            return true;
        }

        void bitblast_pbc(polynomial & m_p, numeral const & m_c, expr_ref & r) {
            bool is_card = is_cardinality(m_p, m_c);
        
            if (is_card && numeral(m_p.size()) < m_c) {
                r = m.mk_false();
                return;
            }

            if (is_card && m_c.is_one()) {
                ptr_buffer<expr> args;
                for (unsigned i = 0; i < m_p.size(); i++) {
                    args.push_back(mon_lit2lit(m_p[i]));
                }             
                r = m.mk_or(args.size(), args.c_ptr());
                return;
            }
        
            if (is_card && m_c == numeral(m_p.size())) {
                ptr_buffer<expr> args;
                for (unsigned i = 0; i < m_p.size(); i++) {
                    args.push_back(mon_lit2lit(m_p[i]));
                }
                m_b_rw.mk_and(args.size(), args.c_ptr(), r);
                return;
            }
        
            if (m_p.size() <= m_all_clauses_limit) {
                pb2bv_all_clauses proc(*this);
                proc(m_p, m_c, r);
                return;
            }
        
            if (is_card) {
                SASSERT(m_c < numeral(m_p.size())); // After normalization, this should be true.
                SASSERT(m_c.is_unsigned()); // Otherwise this is not going to fit into memory...

                unsigned n = m_p.size();
                unsigned k = m_c.get_unsigned();
                unsigned rowsz = n - k + 1;

                unsigned long long cost = k * rowsz;
                if (cost <= static_cast<unsigned long long>(m_cardinality_limit)) {
                    SASSERT(rowsz > 0);
                
                    expr_ref_vector tmp(m);
                    tmp.resize(rowsz, m.mk_true());
                
                    for (unsigned i = 0; i < k; i++) {
                        for (unsigned j = 0; j < rowsz; j++) {
                            expr_ref new_ite(m);
                            m_b_rw.mk_ite(mon_lit2lit(m_p[i + j]),
                                        tmp.get(j),
                                        j == 0 ? m.mk_false() : tmp.get(j-1),
                                        new_ite);
                            tmp.set(j, new_ite.get());
                        }
                    }
                
                    TRACE("pb2bv_bv", tout << "BV Cardinality: " << mk_ismt2_pp(tmp.back(), m) << std::endl;);
                    r = tmp.back();
                    return;
                }
            }

            TRACE("pb2bv_bv_detail", tout << "encoding:\n"; display(tout, m_p, m_c);); 
            // [Leo] improving number of bits needed.
            // using (sum-of-coeffs).get_num_bits()
            numeral sum;
            for (unsigned i = 0; i < m_p.size(); i++) {
                monomial const & mo = m_p[i];            
                SASSERT(mo.m_a.is_pos());
                sum += mo.m_a;
            }
        
            if (sum < m_c) {
                // trivially false.
                r = m.mk_false();
                return;
            }
        
            unsigned bits = sum.get_num_bits();
        
            TRACE("num_bits_bug", tout << "bits: " << bits << " sum: " << sum << " size: " << m_p.size() << "\n";);
        
            // [Leo]: The following assertion should hold, right? 
            // I mean, the constraints are normalized, then mo.m_a <= m_c for every monomial in cnstr.
            // [Christoph]: I agree and never saw it violated so far!
            SASSERT(m_c.get_num_bits() <= bits);

            ptr_buffer<expr> lhs_args;
        
            for (unsigned i = 0; i < m_p.size(); i++) {
                monomial const & mo = m_p[i];
                // encode using if-then-else
                expr * bv_monom =
                    m.mk_ite(mon_lit2lit(mo.m_lit),
                             m_bv_util.mk_numeral(mo.m_a, bits),
                             m_bv_util.mk_numeral(numeral(0), bits));
                lhs_args.push_back(bv_monom);
            }
        
            expr * lhs = m.mk_app(m_bv_util.get_family_id(), OP_BADD, lhs_args.size(), lhs_args.c_ptr());                
            expr * rhs = m_bv_util.mk_numeral(m_c, bits);
        
            r = m_bv_util.mk_ule(rhs, lhs);
        }

        void split(polynomial & m_p, numeral & m_c, polynomial & m_clause) {
            if (m_p.size() <= 2 || m_c.is_one())
                return;

            if (m_p[0].m_a != m_c || m_p[1].m_a != m_c)
                return; // nothing to do.

            unsigned sz = m_p.size();
            unsigned i;
            for (i = 2; i < sz; i++) {
                if (m_p[i].m_a != m_c)
                    break;
            }
        
            if (i >= sz) {
                // [Christoph]: In this case, all the m_a are equal to m_c.
                return;
            }

            // copy lits [0, i) to m_clause
            for (unsigned j = 0; j < i; j++)
                m_clause.push_back(monomial(numeral(1), m_p[j].m_lit));
        
            app * new_var = m.mk_fresh_const(0, m_arith_util.mk_int());
            m_temporary_ints.push_back(new_var);
        
            m_clause.push_back(monomial(numeral(1), lit(new_var,  true)));        
        
            // remove monomials [0, i) from m_p and add new_var in the beginning
            for (unsigned j = i; j < sz; j++) {
                m_p[j - i + 1] = m_p[j];
            }
            m_p.shrink(sz - i + 1);
            m_p[0] = monomial(m_c, lit(new_var, false));
        }

        void mk_pbc(polynomial & m_p, numeral & m_c, expr_ref & r, bool enable_split) {
            TRACE("mk_pbc", display(tout, m_p, m_c); );
            if (m_c.is_nonpos()) {
                // constraint is equivalent to true.
                r = m.mk_true();
                return;
            }
            polynomial::iterator it  = m_p.begin();
            polynomial::iterator end = m_p.end();
            numeral a_gcd = (it->m_a > m_c) ? m_c : it->m_a;
            for (; it != end; ++it) {
                if (it->m_a > m_c)
                    it->m_a = m_c; // trimming coefficients
                a_gcd = gcd(a_gcd, it->m_a);
            }
            SASSERT(a_gcd.is_pos());
            if (!a_gcd.is_one()) {
                it = m_p.begin();
                for (; it != end; ++it)
                    it->m_a /= a_gcd;
                m_c = ceil(m_c/a_gcd);
            }
            TRACE("mk_pbc", tout << "GCD = " << a_gcd << "; Normalized: "; display(tout, m_p, m_c); tout << "\n"; );
            it  = m_p.begin();
            numeral a_sum;
            for (; it != end; ++it) {
                a_sum += m_c;
                if (a_sum >= m_c)
                    break;
            }
            if (a_sum < m_c) {
                // constraint is equivalent to false.
                r = m.mk_false();
                return;
            }
            polynomial clause;
            TRACE("split_bug", display(tout, m_p, m_c););
            if (enable_split)
                split(m_p, m_c, clause);
            TRACE("split_bug", display(tout, m_p, m_c); display(tout, clause, rational(1)););
            if (clause.empty()) {
                bitblast_pbc(m_p, m_c, r);
            }
            else {
                expr_ref r1(m);
                expr_ref r2(m);
                bitblast_pbc(m_p, m_c, r1);
                bitblast_pbc(clause, numeral(1), r2);
                TRACE("split_bug", tout << mk_ismt2_pp(r1, m) << "\nAND\n" << mk_ismt2_pp(r2, m) << "\n";);
                m_b_rw.mk_and(r1, r2, r);
            }
        }

        void adjust(bool & pos, constraint_kind & k, numeral & c) {
            if (!pos) {
                if (k == LE) {
                    // not (lhs <= c)  --> lhs > c --> lhs >= c+1
                    pos = true;
                    k   = GE;
                    c++;
                }
                else if (k == GE) {
                    // not (lhs >= c) --> lhs < c --> lhs <= c-1
                    pos = true;
                    k   = LE;
                    c--;
                }
            }
            SASSERT(pos || k == EQ);
        }
    
        void throw_non_pb(expr * n) {        
            TRACE("pb2bv", tout << "Not pseudo-Boolean: " << mk_ismt2_pp(n, m) << "\n";);
            throw non_pb();
        }

        // check if polynomial is encoding 
        // a_0*x_0 + a_0*~y_0 + ... + a_{n-1}*x_{n - 1} + a_{n - 1}*~y_{n - 1} = c
        // x_0 = y_0, ..., x_{n - 1} = y_{n - 1}
        bool is_eq_vector(polynomial const & p, numeral const & c) {
            TRACE("is_eq_vector", display(tout, p, c););
            unsigned sz = p.size();
            if (sz % 2 == 1)
                return false; // size must be even
            // I implemented only the easy (and very common) case, where a_i = 2^{n-i-1} and c = 2^n - 1
            unsigned n = sz/2;
            if (c != rational::power_of_two(n) - numeral(1))
                return false;
            for (unsigned i = 0; i < n; i++) {
                monomial const & m1 = p[i*2];
                monomial const & m2 = p[i*2+1];
                if (m1.m_lit.sign() == m2.m_lit.sign())
                    return false;
                if (m1.m_a != m2.m_a)
                    return false;
                if (m1.m_a != rational::power_of_two(n - i - 1))
                    return false;
            }
            return true;
        }

        void add_bounds_dependencies(expr * a) {
            m_used_dependencies = m.mk_join(m_used_dependencies, m_bm.lower_dep(a));
            m_used_dependencies = m.mk_join(m_used_dependencies, m_bm.upper_dep(a));
        }

        void convert(app * t, expr_ref & r, bool pos, bool root) {            
            constraint_kind k;
            expr * lhs, * rhs;
            if (m.is_eq(t, lhs, rhs)) {
                if (is_uninterp_const(lhs) && is_uninterp_const(rhs)) {
                    add_bounds_dependencies(lhs);
                    add_bounds_dependencies(rhs);
                    r = m.mk_iff(mon_lit2lit(lit(lhs, false)),
                                 mon_lit2lit(lit(rhs, !pos)));
                    return;
                }
                k = EQ;
            }
            else if (m_arith_util.is_le(t, lhs, rhs)) {
                k = LE;
            }
            else if (m_arith_util.is_ge(t, lhs, rhs)) {
                k = GE;
            }
            else {
                throw_non_pb(t);
            }            

            numeral c; bool is_int;
            if (m_arith_util.is_numeral(lhs, c)) {
                adjust(pos, k, c);
                if (is_uninterp_const(rhs)) {
                    add_bounds_dependencies(rhs);

                    if (k == EQ) {
                        bool sign = c.is_zero();
                        if (!pos) sign = !sign;                        
                        r = mk_unit(rhs, sign);
                    }
                    else if ((c.is_zero() && k == LE) ||
                             (c.is_one() && k == GE)) {
                        // redundant 0 <= x, 1 >= x
                        TRACE("pb2bv", tout << "discarding:\n" << mk_ismt2_pp(t, m) << "\n";);
                        SASSERT(pos);                        
                        r = m.mk_true();
                    }
                    else {
                        SASSERT((c.is_zero() && k == GE) ||
                                (c.is_one() && k == LE));
                        // unit 0 >= x, 1 <= x
                        SASSERT(pos);
                        r = mk_unit(rhs, k == GE);
                    }
                    return;
                }
                throw_non_pb(t);
            }
            if (!m_arith_util.is_numeral(rhs, c, is_int) || !is_int)
                throw_non_pb(t);
        
            adjust(pos, k, c);
        
            if (is_uninterp_const(lhs)) {
                add_bounds_dependencies(lhs);

                if (k == EQ) {
                    TRACE("pb2bv_bug", tout << "c: " << c << "\n";);
                    if (!c.is_zero() && !c.is_one()) {
                        // x = k --> true  where k is not 0 or 1
                        r = pos ? m.mk_false() : m.mk_true();
                    }
                    else {
                        bool sign = c.is_zero();
                        if (!pos) sign = !sign;
                        r = mk_unit(lhs, sign);
                    }
                    return;
                }
                else {
                    // Our atom is of the form: (<= lhs c) or (>= lhs c)
                    // c may be different from 0,1.
                    if (k == LE) {
                        // x <= c >= 1
                        if (c >= numeral(1)) {
                            TRACE("pb2bv", tout << "discarding:\n" << mk_ismt2_pp(t, m) << "\n";);
                            r = m.mk_true();
                            return;
                        }
                        else if (c.is_neg()) {
                            // x <= c < 0
                            r = m.mk_false();
                            return;
                        }
                        SASSERT(c.is_zero());
                    }
                    else if (k == GE) {
                        if (c.is_nonpos()) {
                            TRACE("pb2bv", tout << "discarding:\n" << mk_ismt2_pp(t, m) << "\n";);
                            // x >= a <= 0
                            r = m.mk_true();
                            return;
                        }
                        else if (c > numeral(1)) {
                            // x >= a > 1
                            r = m.mk_false();
                            return;
                        }
                        SASSERT(c.is_one());
                    }
                    CTRACE("pb2bv", !(c.is_zero() || c.is_one()),
                           tout << "BUG: " << mk_ismt2_pp(t, m) << "\nk: " << k << " " << c << "\n";);
                    SASSERT(c.is_zero() || c.is_one());
                    SASSERT(!((c.is_zero() && k == GE) ||
                              (c.is_one() && k == LE)));

                    CTRACE("pb2bv_bug", !((c.is_zero() && k == LE) || (c.is_one() && k == GE)),
                           tout << "c: " << c << ", k: " << k << "\n";
                           tout << "t: " << mk_ismt2_pp(t, m) << "\n";);
                    SASSERT((c.is_zero() && k == LE) ||
                            (c.is_one() && k == GE));
                    // x <= 0, x >= 1
                    SASSERT(pos);
                    r = mk_unit(lhs, k == LE);
                    return;
                }
            }
            
            if (!m_arith_util.is_add(lhs))
                throw_non_pb(t);

            unsigned sz = to_app(lhs)->get_num_args();
            expr * const * ms = to_app(lhs)->get_args();
            expr * a, * x;
            for (unsigned i = 0; i < sz; i++) {
                expr * m = ms[i];
                if (is_uninterp_const(m))
                    continue;
                if (m_arith_util.is_mul(m, a, x) && m_arith_util.is_numeral(a) && is_uninterp_const(x))
                    continue;
                throw_non_pb(t);
            }            

            // is pb constraint.
            numeral    a_val;
            polynomial m_p;
            numeral    m_c;
            m_c = c;
            for (unsigned i = 0; i < sz; i++) {
                expr * m = ms[i];                
                if (is_uninterp_const(m)) {
                    add_bounds_dependencies(m);
                    m_p.push_back(monomial(lit(m)));
                }
                else if (m_arith_util.is_mul(m, a, x) && m_arith_util.is_numeral(a, a_val)) {
                    add_bounds_dependencies(x);
                    if (a_val.is_neg()) {
                        a_val.neg(); 
                        // -a x --> -a(1-!x) ==> -a + a!x,
                        m_c += a_val;
                        m_p.push_back(monomial(a_val, lit(x, true)));
                    }
                    else {
                        m_p.push_back(monomial(a_val, lit(x)));
                    }
                }
                else {
                    UNREACHABLE();
                }
            }

            std::stable_sort(m_p.begin(), m_p.end(), monomial_lt());

            if (k == GE) {
                mk_pbc(m_p, m_c, r, root);
            }
            else if (k == LE) {
                m_c.neg();
                for (unsigned i = 0; i < sz; i++) {
                    monomial & m = m_p[i];
                    SASSERT(m.m_a.is_nonneg());
                    m_c += m.m_a;
                    m.m_lit.neg();
                }
                mk_pbc(m_p, m_c, r, root);
            }
            else {
                SASSERT(k == EQ);

                if (is_eq_vector(m_p, m_c)) {
                    TRACE("is_eq_vector", tout << "found eq vector\n";);
                    unsigned sz = m_p.size();
                    expr_ref_vector eqs(m);
                    for (unsigned i = 0; i < sz; i += 2) {
                        app * x_i = to_app(m_p[i].m_lit.var());
                        app * y_i = to_app(m_p[i+1].m_lit.var());
                        eqs.push_back(m.mk_eq(int2lit(x_i), int2lit(y_i)));
                    }
                    m_b_rw.mk_and(eqs.size(), eqs.c_ptr(), r);
                    if (!pos)
                        m_b_rw.mk_not(r, r);
                    return;
                }

                polynomial m_p2;
                numeral    m_c2 = m_c;
                m_c2.neg();
                for (unsigned i = 0; i < sz; i++) {
                    monomial m = m_p[i];
                    SASSERT(m.m_a.is_nonneg());
                    m_c2 += m.m_a;
                    m.m_lit.neg();
                    m_p2.push_back(m);
                }
                expr_ref r1(m);
                expr_ref r2(m);
                mk_pbc(m_p, m_c, r1, false);
                mk_pbc(m_p2, m_c2, r2, false);
                TRACE("pb2bv_convert", tout << mk_ismt2_pp(t, m) << "\n";
                      display(tout, m_p, m_c);
                      display(tout, m_p2, m_c2);
                      tout << "--->\n" << mk_ismt2_pp(r1, m) << "\nAND\n" << mk_ismt2_pp(r2, m) << "\n";);
                m_b_rw.mk_and(r1, r2, r);
                if (!pos)
                    m_b_rw.mk_not(r, r);
            }
        }

        bool is_constraint_core(expr * n) {
            return (m.is_eq(n) && m_arith_util.is_int(to_app(n)->get_arg(0))) || m_arith_util.is_le(n) || m_arith_util.is_ge(n);
        }

        bool is_constraint(expr * n, expr * & atom, bool & pos) {
            pos = true;
            while (m.is_not(n)) {
                n = to_app(n)->get_arg(0);
                pos = !pos;
            }
            atom = n;
            return is_constraint_core(n);
        }        
       
        imp(ast_manager & _m, params_ref const & p):
            m(_m),
            m_bm(m),
            m_b_rw(m, p),
            m_arith_util(m),
            m_bv_util(m),
            m_new_deps(m),            
            m_temporary_ints(m),
            m_used_dependencies(m),
            m_rw(*this) {
            updt_params(p);            
            m_b_rw.set_flat(false); // no flattening otherwise will blowup the memory
            m_b_rw.set_elim_and(true);
        }

        ~imp() {
            dec_ref_map_key_values(m, m_const2bit);
            dec_ref_map_values(m, m_not_const2bit);
            m_rw.reset();
            m_bm.reset();
            m_temporary_ints.reset();
        }

        void updt_params(params_ref const & p) {
            m_max_memory   = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
            m_all_clauses_limit = p.get_uint("pb2bv_all_clauses_limit", 8);
            m_cardinality_limit = p.get_uint("pb2bv_cardinality_limit", UINT_MAX);
            m_b_rw.updt_params(p);
        }

        void collect_param_descrs(param_descrs & r) {
            insert_max_memory(r);            
            r.insert("pb2bv_all_clauses_limit", CPK_UINT, "(default: 8) maximum number of literals for using equivalent CNF encoding of PB constraint.");
            r.insert("pb2bv_cardinality_limit", CPK_UINT, "(default: inf) limit for using arc-consistent cardinality constraint encoding.");

            m_b_rw.get_param_descrs(r);        
            r.erase("flat"); 
            r.erase("elim_and");            
        }
        
        virtual void operator()(goal_ref const & g, 
                                goal_ref_buffer & result, 
                                model_converter_ref & mc, 
                                proof_converter_ref & pc,
                                expr_dependency_ref & core) {
            TRACE("pb2bv", g->display(tout););
            SASSERT(g->is_well_sorted());
            fail_if_proof_generation("pb2bv", g);
            m_produce_models      = g->models_enabled();
            m_produce_unsat_cores = g->unsat_core_enabled();
            mc = 0; pc = 0; core = 0; result.reset();
            tactic_report report("pb2bv", *g);
            m_bm.reset(); m_rw.reset(); m_new_deps.reset();

            if (g->inconsistent()) {
                result.push_back(g.get());
                return;
            }

            m_bm(*g);
            
            TRACE("pb2bv", m_bm.display(tout););

            try {
                quick_pb_check(g);
            }
            catch (non_pb) {
                throw tactic_exception("goal is in a fragment unsupported by pb2bv");
            }
                        
            unsigned size = g->size();
            expr_ref_vector new_exprs(m);
            expr_dependency_ref_vector new_deps(m);

            try {
                expr_ref  new_curr(m);
                proof_ref new_pr(m);                
                expr_ref new_f(m);
                for (unsigned idx = 0; idx < size; idx++) {
                    expr * curr = g->form(idx);
                    expr * atom;
                    bool pos;
                    if (is_constraint(curr, atom, pos)) {
                        convert(to_app(atom), new_f, pos, true);
                        TRACE("pb2bv_convert", tout << "pos: " << pos << "\n" << mk_ismt2_pp(atom, m) << "\n--->\n" << mk_ismt2_pp(new_f, m) << "\n";); 
                    }
                    else {
                        m_rw(curr, new_f);
                    }
                    if (m_produce_unsat_cores) {
                        new_deps.push_back(m.mk_join(m_used_dependencies, g->dep(idx)));
                        m_used_dependencies.reset();
                    }
                    new_exprs.push_back(new_f);
                }                
            }
            catch (non_pb) {
                throw tactic_exception("goal is in a fragment unsupported by pb2bv");
            }

            for (unsigned idx = 0; idx < size; idx++)
                g->update(idx, new_exprs[idx].get(), 0, (m_produce_unsat_cores) ? new_deps[idx].get() : g->dep(idx));

            if (m_produce_models) {
                filter_model_converter * mc1 = alloc(filter_model_converter, m);
                obj_map<func_decl, expr*>::iterator it  = m_const2bit.begin();
                obj_map<func_decl, expr*>::iterator end = m_const2bit.end();
                for (; it != end; ++it)
                    mc1->insert(to_app(it->m_value)->get_decl());
                // store temp int constants in the filter
                unsigned num_temps = m_temporary_ints.size();
                for (unsigned i = 0; i < num_temps; i++)
                    mc1->insert(to_app(m_temporary_ints.get(i))->get_decl());
                pb2bv_model_converter * mc2 = alloc(pb2bv_model_converter, m, m_const2bit, m_bm);
                mc = concat(mc1, mc2);                
            }

            g->inc_depth();
            result.push_back(g.get());
            TRACE("pb2bv", g->display(tout););
            SASSERT(g->is_well_sorted());
        }
    };

    imp *      m_imp;
    params_ref m_params;
public:
    pb2bv_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(pb2bv_tactic, m, m_params);
    }

    virtual ~pb2bv_tactic() {
        dealloc(m_imp);
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
        m_imp->updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) {  
        m_imp->collect_param_descrs(r);
    }

    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        (*m_imp)(in, result, mc, pc, core);
    }
    
    virtual void cleanup() {
        ast_manager & m = m_imp->m;
        imp * d = alloc(imp, m, m_params);
        std::swap(d, m_imp);        
        dealloc(d);
    }


};

tactic * mk_pb2bv_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(pb2bv_tactic, m, p));
}

struct is_pb_probe : public probe {
    virtual result operator()(goal const & g) {
        try {
            ast_manager & m = g.m();
            bound_manager bm(m);
            bm(g);
            arith_util a_util(m);
            expr_fast_mark1 visited;
            pb2bv_tactic::only_01_visitor proc(a_util, bm);
            
            unsigned sz = g.size();
            for (unsigned i = 0; i < sz; i++) {
                expr * f = g.form(i);
                for_each_expr_core<pb2bv_tactic::only_01_visitor, expr_fast_mark1, true, true>(proc, visited, f);
            }
            
            return true;
        }
        catch (pb2bv_tactic::non_pb) {
            return false;
        }
    }
};


probe * mk_is_pb_probe() {
    return alloc(is_pb_probe);
}
