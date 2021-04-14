/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    fm_tactic.cpp

Abstract:

    Use Fourier-Motzkin to eliminate variables.
    This strategy can handle conditional bounds 
    (i.e., clauses with at most one constraint).
    
    The strategy mk_occf can be used to put the
    formula in OCC form.

Author:

    Leonardo de Moura (leonardo) 2012-02-04.

Revision History:

--*/
#include "tactic/arith/fm_tactic.h"
#include "tactic/tactical.h"
#include "ast/arith_decl_plugin.h"
#include "ast/for_each_expr.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_pp.h"
#include "util/id_gen.h"
#include "model/model_evaluator.h"
#include "model/model_v2_pp.h"
#include "tactic/core/simplify_tactic.h"

class fm_tactic : public tactic {
    typedef ptr_vector<app> clauses;
    typedef unsigned        var;
    typedef int             bvar;
    typedef int             literal;
    typedef svector<var>    var_vector;

    struct fm_model_converter : public model_converter {
        ast_manager &         m;
        ptr_vector<func_decl> m_xs;
        vector<clauses>       m_clauses;

        enum r_kind {
            NONE,
            LOWER,
            UPPER 
        };

        bool is_false(model_ref & md, app * p) {
            SASSERT(is_uninterp_const(p));
            expr * val = md->get_const_interp(p->get_decl());
            if (val == nullptr) {
                // if it is don't care, then set to false
                md->register_decl(p->get_decl(), m.mk_false());
                return true;
            }
            return m.is_false(val);
        }

        r_kind process(func_decl * x, expr * cls, arith_util & u, model& ev, rational & r) {
            unsigned num_lits;
            expr * const * lits;
            if (m.is_or(cls)) {
                num_lits = to_app(cls)->get_num_args();
                lits     = to_app(cls)->get_args();
            }
            else {
                num_lits = 1;
                lits     = &cls;
            }

            bool is_lower = false;
            bool found = false;
            for (unsigned i = 0; i < num_lits; i++) {
                expr * l = lits[i];
                expr * atom;
                if (is_uninterp_const(l) || (m.is_not(l, atom) && is_uninterp_const(atom))) {
                    if (ev.is_true(l)) 
                        return NONE; // clause was satisfied
                }
                else {
                    found = true;
                    bool neg    = m.is_not(l, l);
                    SASSERT(u.is_le(l) || u.is_ge(l));
                    bool strict = neg;
                    rational a_val;
                    if (u.is_ge(l))
                        neg = !neg;
                    expr * lhs = to_app(l)->get_arg(0);
                    expr * rhs = to_app(l)->get_arg(1);
                    rational c;
                    u.is_numeral(rhs, c);
                    if (neg)
                        c.neg();
                    unsigned num_mons;
                    expr * const * mons;
                    if (u.is_add(lhs)) {
                        num_mons = to_app(lhs)->get_num_args();
                        mons     = to_app(lhs)->get_args();
                    }
                    else {
                        num_mons = 1;
                        mons     = &lhs;
                    }
                    for (unsigned j = 0; j < num_mons; j++) {
                        expr * monomial = mons[j];
                        expr * ai;
                        expr * xi;
                        rational ai_val;
                        if (u.is_mul(monomial, ai, xi)) {
                            u.is_numeral(ai, ai_val);
                        }
                        else {
                            xi     = monomial;
                            ai_val = rational(1);
                        }
                        if (u.is_to_real(xi))
                            xi = to_app(xi)->get_arg(0);
                        SASSERT(is_uninterp_const(xi));
                        if (x == to_app(xi)->get_decl()) {
                            a_val = ai_val;
                            if (neg)
                                a_val.neg();
                        }
                        else {
                            expr_ref val(m);
                            val = ev(monomial);
                            SASSERT(u.is_numeral(val));
                            rational tmp;
                            u.is_numeral(val, tmp);
                            if (neg)
                                tmp.neg();
                            c -= tmp;
                        }
                    }
                    if (u.is_int(x->get_range()) && strict) {
                        // a*x < c --> a*x <= c-1
                        SASSERT(c.is_int());
                        c--;
                    }
                    is_lower = a_val.is_neg();
                    c /= a_val;
                    if (u.is_int(x->get_range())) {
                        if (is_lower)
                            c = ceil(c);
                        else
                            c = floor(c);
                    }
                    r = c;
                }
            }
            (void)found;
            SASSERT(found);
            return is_lower ? LOWER : UPPER;
        }
        
    public:
        fm_model_converter(ast_manager & _m):m(_m) {}

        ~fm_model_converter() override {
            m.dec_array_ref(m_xs.size(), m_xs.data());
            vector<clauses>::iterator it  = m_clauses.begin();
            vector<clauses>::iterator end = m_clauses.end();
            for (; it != end; ++it)
                m.dec_array_ref(it->size(), it->data());
        }
        
        void insert(func_decl * x, clauses & c) {
            m.inc_ref(x);
            m.inc_array_ref(c.size(), c.data());
            m_xs.push_back(x);
            m_clauses.push_back(clauses());
            m_clauses.back().swap(c);
        }

        void get_units(obj_map<expr, bool>& units) override { units.reset(); }

        void operator()(model_ref & md) override {
            TRACE("fm_mc", model_v2_pp(tout, *md); display(tout););
            model::scoped_model_completion _sc(*md, true);
            //model_evaluator ev(*(md.get()));
            //ev.set_model_completion(true);
            arith_util u(m);
            unsigned i = m_xs.size();
            while (i > 0) {
                --i;
                func_decl * x = m_xs[i];
                rational lower;
                rational upper;
                rational val;
                bool has_lower = false;
                bool has_upper = false;
                TRACE("fm_mc", tout << "processing " << x->get_name() << "\n";);
                clauses::iterator it  = m_clauses[i].begin();
                clauses::iterator end = m_clauses[i].end();
                for (; it != end; ++it) {
                    if (!m.inc()) 
                        throw tactic_exception(m.limit().get_cancel_msg());
                    switch (process(x, *it, u, *md, val)) {
                    case NONE: 
                        TRACE("fm_mc", tout << "no bound for:\n" << mk_ismt2_pp(*it, m) << "\n";);
                        break;
                    case LOWER: 
                        TRACE("fm_mc", tout << "lower bound: " << val << " for:\n" << mk_ismt2_pp(*it, m) << "\n";);
                        if (!has_lower || val > lower) 
                            lower = val; 
                        has_lower = true;
                        break;
                    case UPPER: 
                        TRACE("fm_mc", tout << "upper bound: " << val << " for:\n" << mk_ismt2_pp(*it, m) << "\n";);
                        if (!has_upper || val < upper) 
                            upper = val; 
                        has_upper = true;
                        break;
                    }
                }

                expr * x_val;
                if (u.is_int(x->get_range())) {
                    if (has_lower)
                        x_val = u.mk_numeral(lower, true);
                    else if (has_upper)
                        x_val = u.mk_numeral(upper, true);
                    else
                        x_val = u.mk_numeral(rational(0), true);
                }
                else {
                    if (has_lower && has_upper)
                        x_val = u.mk_numeral((upper + lower)/rational(2), false);
                    else if (has_lower)
                        x_val = u.mk_numeral(lower + rational(1), false);
                    else if (has_upper)
                        x_val = u.mk_numeral(upper - rational(1), false);
                    else
                        x_val = u.mk_numeral(rational(0), false);
                }
                TRACE("fm_mc", tout << x->get_name() << " --> " << mk_ismt2_pp(x_val, m) << "\n";);
                md->register_decl(x, x_val);
            }
            TRACE("fm_mc", model_v2_pp(tout, *md););
        }


        void display(std::ostream & out) override {
            out << "(fm-model-converter";
            SASSERT(m_xs.size() == m_clauses.size());
            unsigned sz = m_xs.size();
            for (unsigned i = 0; i < sz; i++) {
                out << "\n(" << m_xs[i]->get_name();
                clauses const & cs = m_clauses[i];
                clauses::const_iterator it  = cs.begin();
                clauses::const_iterator end = cs.end();
                for (; it != end; ++it) {
                    out << "\n  " << mk_ismt2_pp(*it, m, 2);
                }
                out << ")";
            }
            out << ")\n";
        }

        model_converter * translate(ast_translation & translator) override {
            ast_manager & to_m = translator.to();
            fm_model_converter * res = alloc(fm_model_converter, to_m);
            unsigned sz = m_xs.size();
            for (unsigned i = 0; i < sz; i++) {
                func_decl * new_x = translator(m_xs[i]);
                to_m.inc_ref(new_x);
                res->m_xs.push_back(new_x);

                clauses const & cs = m_clauses[i];
                res->m_clauses.push_back(clauses());
                clauses & new_cs = res->m_clauses.back();
                clauses::const_iterator it  = cs.begin();
                clauses::const_iterator end = cs.end();
                for (; it != end; ++it) {
                    app * new_c = translator(*it);
                    to_m.inc_ref(new_c);
                    new_cs.push_back(new_c);
                }
            }
            return res;
        }
    };

    // Encode the constraint
    // lits \/ ( as[0]*xs[0] + ... + as[num_vars-1]*xs[num_vars-1] <= c
    // if strict is true, then <= is <.
    struct constraint {
        static unsigned get_obj_size(unsigned num_lits, unsigned num_vars) {
            return sizeof(constraint) + num_lits*sizeof(literal) + num_vars*(sizeof(var) + sizeof(rational));
        }
        unsigned           m_id;
        unsigned           m_num_lits:29;
        unsigned           m_strict:1;
        unsigned           m_dead:1;
        unsigned           m_mark:1;
        unsigned           m_num_vars;
        literal *          m_lits;
        var *              m_xs;
        rational  *        m_as;
        rational           m_c;
        expr_dependency *  m_dep;
        ~constraint() {
            rational * it  = m_as;
            rational * end = it + m_num_vars;
            for (; it != end; ++it)
                it->~rational();
        }
        
        unsigned hash() const { return hash_u(m_id); }
    };
    
    typedef ptr_vector<constraint> constraints;

    class constraint_set {
        unsigned_vector m_id2pos; 
        constraints     m_set;
    public:
        typedef constraints::const_iterator iterator;

        bool contains(constraint const & c) const { 
            if (c.m_id >= m_id2pos.size()) 
                return false; 
            return m_id2pos[c.m_id] != UINT_MAX; 
        }
        
        bool empty() const { return m_set.empty(); }
        unsigned size() const { return m_set.size(); }
        
        void insert(constraint & c) {
            unsigned id  = c.m_id;
            m_id2pos.reserve(id+1, UINT_MAX);
            if (m_id2pos[id] != UINT_MAX)
                return; // already in the set
            unsigned pos = m_set.size();
            m_id2pos[id] = pos;
            m_set.push_back(&c);
        }
        
        void erase(constraint & c) {
            unsigned id = c.m_id;
            if (id >= m_id2pos.size())
                return;
            unsigned pos = m_id2pos[id];
            if (pos == UINT_MAX)
                return;
            m_id2pos[id] = UINT_MAX;
            unsigned last_pos = m_set.size() - 1;
            if (pos != last_pos) {
                constraint * last_c = m_set[last_pos];
                m_set[pos] = last_c; 
                m_id2pos[last_c->m_id] = pos;
            }
            m_set.pop_back();
        }
        
        constraint & erase() {
            SASSERT(!empty());
            constraint & c = *m_set.back(); 
            m_id2pos[c.m_id] = UINT_MAX;
            m_set.pop_back();
            return c;
        }
        
        void reset() { m_id2pos.reset(); m_set.reset(); }
        void finalize() { m_id2pos.finalize(); m_set.finalize(); }
        
        iterator begin() const { return m_set.begin(); }
        iterator end() const { return m_set.end(); }
    };
    
    struct imp {
        ast_manager &            m;
        small_object_allocator   m_allocator;
        arith_util               m_util;
        constraints              m_constraints;
        expr_ref_vector          m_bvar2expr;
        signed_char_vector       m_bvar2sign;
        obj_map<expr, bvar>      m_expr2bvar;
        char_vector              m_is_int;
        char_vector              m_forbidden;
        expr_ref_vector          m_var2expr;
        obj_map<expr, var>       m_expr2var;
        unsigned_vector          m_var2pos;
        vector<constraints>      m_lowers;
        vector<constraints>      m_uppers;
        obj_hashtable<func_decl> m_forbidden_set; // variables that cannot be eliminated because occur in non OCC ineq part
        goal_ref                 m_new_goal;
        ref<fm_model_converter>  m_mc;
        id_gen                   m_id_gen;
        bool                     m_produce_models;
        bool                     m_fm_real_only;
        unsigned                 m_fm_limit;
        unsigned                 m_fm_cutoff1;
        unsigned                 m_fm_cutoff2;
        unsigned                 m_fm_extra;
        bool                     m_fm_occ;
        unsigned long long       m_max_memory;
        unsigned                 m_counter;
        bool                     m_inconsistent;
        expr_dependency_ref      m_inconsistent_core;
        constraint_set           m_sub_todo;
        
        // ---------------------------
        //
        // OCC clause recognizer
        //
        // ---------------------------
        
        bool is_literal(expr * t) const {
            expr * atom;
            return is_uninterp_const(t) || (m.is_not(t, atom) && is_uninterp_const(atom));
        }
        
        bool is_constraint(expr * t) const {
            return !is_literal(t);
        }
        
        bool is_var(expr * t, expr * & x) const {
            if (is_uninterp_const(t)) {
                x = t;
                return true;
            }
            else if (m_util.is_to_real(t) && is_uninterp_const(to_app(t)->get_arg(0))) {
                x = to_app(t)->get_arg(0);
                return true;
            }
            return false;
        }
        
        bool is_var(expr * t) const {
            expr * x;
            return is_var(t, x);
        }
        
        bool is_linear_mon_core(expr * t, expr * & x) const {
            expr * c;
            if (m_util.is_mul(t, c, x) && m_util.is_numeral(c) && is_var(x, x))
                return true;
            return is_var(t, x);
        }
        
        bool is_linear_mon(expr * t) const {
            expr * x;
            return is_linear_mon_core(t, x);
        }
        
        bool is_linear_pol(expr * t) const {
            unsigned       num_mons;
            expr * const * mons;
            if (m_util.is_add(t)) {
                num_mons = to_app(t)->get_num_args();
                mons     = to_app(t)->get_args();
            }
            else {
                num_mons = 1;
                mons     = &t;
            }
            
            expr_fast_mark2 visited;
            bool all_forbidden = true;
            for (unsigned i = 0; i < num_mons; i++) {
                expr * x;
                if (!is_linear_mon_core(mons[i], x))
                    return false;
                if (visited.is_marked(x))
                    return false; // duplicates are not supported... must simplify first
                visited.mark(x);
                if (!m_forbidden_set.contains(to_app(x)->get_decl()) && (!m_fm_real_only || !m_util.is_int(x)))
                    all_forbidden = false;
            }
            return !all_forbidden;
        }
        
        bool is_linear_ineq(expr * t) const {
            m.is_not(t, t);
            expr * lhs, * rhs;
            TRACE("is_occ_bug", tout << mk_pp(t, m) << "\n";);
            if (m_util.is_le(t, lhs, rhs) || m_util.is_ge(t, lhs, rhs)) {
                if (!m_util.is_numeral(rhs))
                    return false;
                return is_linear_pol(lhs);
            }
            return false;
        }
        
        bool is_occ(expr * t) {
            if (m_fm_occ && m.is_or(t)) {
                unsigned num = to_app(t)->get_num_args();
                bool found = false;
                for (unsigned i = 0; i < num; i++) {
                    expr * l = to_app(t)->get_arg(i);
                    if (is_literal(l)) {
                        continue;
                    }
                    else if (is_linear_ineq(l)) {
                        if (found)
                            return false;
                        found = true;
                    }
                    else {
                        return false;
                    }
                }
                return found;
            }
            return is_linear_ineq(t);
        }
        
        // ---------------------------
        //
        // Memory mng
        //
        // ---------------------------
        void del_constraint(constraint * c) {
            m.dec_ref(c->m_dep);
            m_sub_todo.erase(*c);
            m_id_gen.recycle(c->m_id);
            c->~constraint();
            unsigned sz = constraint::get_obj_size(c->m_num_lits, c->m_num_vars);
            m_allocator.deallocate(sz, c);
        }

        void del_constraints(unsigned sz, constraint * const * cs) {
            for (unsigned i = 0; i < sz; i++)
                del_constraint(cs[i]);
        }
        
        void reset_constraints() {
            del_constraints(m_constraints.size(), m_constraints.data());
            m_constraints.reset();
        }
        
        constraint * mk_constraint(unsigned num_lits, literal * lits, unsigned num_vars, var * xs, rational * as, rational & c, bool strict,
                                   expr_dependency * dep) {
            unsigned sz         = constraint::get_obj_size(num_lits, num_vars);
            char * mem          = static_cast<char*>(m_allocator.allocate(sz));
            char * mem_as       = mem + sizeof(constraint);
            char * mem_lits     = mem_as + sizeof(rational)*num_vars;
            char * mem_xs       = mem_lits + sizeof(literal)*num_lits;
            constraint * cnstr  = new (mem) constraint();
            cnstr->m_id         = m_id_gen.mk();
            cnstr->m_num_lits   = num_lits;
            cnstr->m_dead       = false;
            cnstr->m_mark       = false;
            cnstr->m_strict     = strict;
            cnstr->m_num_vars   = num_vars;
            cnstr->m_lits       = reinterpret_cast<literal*>(mem_lits);
            for (unsigned i = 0; i < num_lits; i++)
                cnstr->m_lits[i] = lits[i];
            cnstr->m_xs         = reinterpret_cast<var*>(mem_xs);
            cnstr->m_as         = reinterpret_cast<rational*>(mem_as);
            for (unsigned i = 0; i < num_vars; i++) {
                TRACE("mk_constraint_bug", tout << "xs[" << i << "]: " << xs[i] << "\n";);
                cnstr->m_xs[i] = xs[i];
                new (cnstr->m_as + i) rational(as[i]);
            }
            cnstr->m_c = c;
            DEBUG_CODE({
                for (unsigned i = 0; i < num_vars; i++) {
                    SASSERT(cnstr->m_xs[i] == xs[i]);
                    SASSERT(cnstr->m_as[i] == as[i]);
                }
            });
            cnstr->m_dep = dep;
            m.inc_ref(dep);
            return cnstr;
        }
        
        // ---------------------------
        //
        // Util
        //
        // ---------------------------
        
        unsigned num_vars() const { return m_is_int.size(); }
        
        // multiply as and c, by the lcm of their denominators
        void mk_int(unsigned num, rational * as, rational & c) {
            rational l = denominator(c);
            for (unsigned i = 0; i < num; i++)
                l = lcm(l, denominator(as[i]));
            if (l.is_one())
                return;
            c *= l;
            SASSERT(c.is_int());
            for (unsigned i = 0; i < num; i++) {
                as[i] *= l;
                SASSERT(as[i].is_int());
            }
        }
        
        void normalize_coeffs(constraint & c) {
            if (c.m_num_vars == 0)
                return;
            // compute gcd of all coefficients
            rational g = c.m_c;
            if (g.is_neg())
                g.neg();
            for (unsigned i = 0; i < c.m_num_vars; i++) {
                if (g.is_one())
                    break;
                if (c.m_as[i].is_pos())
                    g = gcd(c.m_as[i], g);
                else
                    g = gcd(-c.m_as[i], g);
            }
            if (g.is_one())
                return;
            c.m_c /= g;
            for (unsigned i = 0; i < c.m_num_vars; i++)
                c.m_as[i] /= g;
        }
        
        void display(std::ostream & out, constraint const & c) const {
            for (unsigned i = 0; i < c.m_num_lits; i++) {
                literal l = c.m_lits[i];
                if (sign(l))
                    out << "~";
                bvar p    = lit2bvar(l);
                out << mk_ismt2_pp(m_bvar2expr[p], m);
                out << " ";
            }
            out << "(";
            if (c.m_num_vars == 0)
                out << "0";
            for (unsigned i = 0; i < c.m_num_vars; i++) {
                if (i > 0)
                    out << " + ";
                if (!c.m_as[i].is_one())
                    out << c.m_as[i] << "*";
                out << mk_ismt2_pp(m_var2expr.get(c.m_xs[i]), m);
            }
            if (c.m_strict)
                out << " < ";
            else
                out << " <= ";
            out << c.m_c;
            out << ")";
        }
        
        /**
           \brief Return true if c1 subsumes c2
       
           c1 subsumes c2 If
           1) All literals of c1 are literals of c2
           2) polynomial of c1 == polynomial of c2
           3) c1.m_c <= c2.m_c
        */
        bool subsumes(constraint const & c1, constraint const & c2) {
            if (&c1 == &c2)
                return false;
            // quick checks first
            if (c1.m_num_lits > c2.m_num_lits)
                return false;
            if (c1.m_num_vars != c2.m_num_vars)
                return false;
            if (c1.m_c > c2.m_c)
                return false;
            if (!c1.m_strict && c2.m_strict && c1.m_c == c2.m_c)
                return false;
            
            m_counter += c1.m_num_lits + c2.m_num_lits;
            
            for (unsigned i = 0; i < c1.m_num_vars; i++) {
                m_var2pos[c1.m_xs[i]] = i;
            }
            
            bool failed = false;
            for (unsigned i = 0; i < c2.m_num_vars; i++) {
                unsigned pos1 = m_var2pos[c2.m_xs[i]];
                if (pos1 == UINT_MAX || c1.m_as[pos1] != c2.m_as[i]) {
                    failed = true;
                    break;
                }
            }
            
            for (unsigned i = 0; i < c1.m_num_vars; i++) {
                m_var2pos[c1.m_xs[i]] = UINT_MAX;
            }
            
            if (failed)
                return false;
            
            for (unsigned i = 0; i < c2.m_num_lits; i++) {
                literal l = c2.m_lits[i];
                bvar b    = lit2bvar(l);
                SASSERT(m_bvar2sign[b] == 0);
                m_bvar2sign[b] = sign(l) ? -1 : 1;
            }
            
            for (unsigned i = 0; i < c1.m_num_lits; i++) {
                literal l = c1.m_lits[i];
                bvar b    = lit2bvar(l);
                char s    = sign(l) ? -1 : 1;
                if (m_bvar2sign[b] != s) {
                    failed = true;
                    break;
                }
            }
            
            for (unsigned i = 0; i < c2.m_num_lits; i++) {
                literal l = c2.m_lits[i];
                bvar b    = lit2bvar(l);
                m_bvar2sign[b] = 0;
            }
            
            if (failed)
                return false;
            
            return true;
        }
        
        void backward_subsumption(constraint const & c) {
            if (c.m_num_vars == 0)
                return;
            var      best       = UINT_MAX;
            unsigned best_sz    = UINT_MAX;
            bool     best_lower = false;
            for (unsigned i = 0; i < c.m_num_vars; i++) {
                var xi     = c.m_xs[i];
                if (is_forbidden(xi))
                    continue; // variable is not in the index
                bool neg_a = c.m_as[i].is_neg();
                constraints & cs = neg_a ? m_lowers[xi] : m_uppers[xi];
                if (cs.size() < best_sz) {
                    best       = xi;
                    best_sz    = cs.size();
                    best_lower = neg_a;
                }
            }
            if (best_sz == 0)
                return;
            if (best == UINT_MAX)
                return; // none of the c variables are in the index.
            constraints & cs = best_lower ? m_lowers[best] : m_uppers[best];
            m_counter += cs.size();
            constraints::iterator it  = cs.begin();
            constraints::iterator it2 = it;
            constraints::iterator end = cs.end();
            for (; it != end; ++it) {
                constraint * c2 = *it;
                if (c2->m_dead)
                    continue;
                if (subsumes(c, *c2)) {
                    TRACE("fm_subsumption", display(tout, c); tout << "\nsubsumed:\n"; display(tout, *c2); tout << "\n";);
                    c2->m_dead = true;
                    continue;
                }
                *it2 = *it;
                ++it2;
            }
            cs.set_end(it2);
        }
        
        void subsume() {
            while (!m_sub_todo.empty()) {
                constraint & c = m_sub_todo.erase();
                if (c.m_dead)
                    continue;
                backward_subsumption(c);
            }
        }
        
        // ---------------------------
        //
        // Initialization
        //
        // ---------------------------
        
        imp(ast_manager & _m, params_ref const & p):
            m(_m),
            m_allocator("fm-tactic"),
            m_util(m),
            m_bvar2expr(m),
            m_var2expr(m),
            m_inconsistent_core(m) {
            updt_params(p);
        }
        
        ~imp() {
            reset_constraints();
        }
        
        void updt_params(params_ref const & p) {
            m_max_memory     = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
            m_fm_real_only   = p.get_bool("fm_real_only", true);
            m_fm_limit       = p.get_uint("fm_limit", 5000000);
            m_fm_cutoff1     = p.get_uint("fm_cutoff1", 8);
            m_fm_cutoff2     = p.get_uint("fm_cutoff2", 256);
            m_fm_extra       = p.get_uint("fm_extra", 0);
            m_fm_occ         = p.get_bool("fm_occ", false);
        }
        
        
        struct forbidden_proc {
            imp & m_owner;
            forbidden_proc(imp & o):m_owner(o) {}
            void operator()(::var * n) {}
            void operator()(app * n) {
                if (is_uninterp_const(n) && n->get_sort()->get_family_id() == m_owner.m_util.get_family_id()) {
                    m_owner.m_forbidden_set.insert(n->get_decl());
                }
            }
            void operator()(quantifier * n) {}
        };
        
        void init_forbidden_set(goal const & g) {
            m_forbidden_set.reset();
            expr_fast_mark1 visited;
            forbidden_proc  proc(*this);
            unsigned sz = g.size();
            for (unsigned i = 0; i < sz; i++) {
                expr * f = g.form(i);
                if (is_occ(f))
                    continue;
                TRACE("is_occ_bug", tout << "not OCC:\n" << mk_ismt2_pp(f, m) << "\n";);
                quick_for_each_expr(proc, visited, f);
            }
        }
        
        void init(goal const & g) {
            m_sub_todo.reset();
            m_id_gen.reset();
            reset_constraints();
            m_bvar2expr.reset();
            m_bvar2sign.reset();
            m_bvar2expr.push_back(nullptr); // bvar 0 is not used
            m_bvar2sign.push_back(0);
            m_expr2var.reset();
            m_is_int.reset();
            m_var2pos.reset();
            m_forbidden.reset();
            m_var2expr.reset();
            m_expr2var.reset();
            m_lowers.reset();
            m_uppers.reset();
            m_new_goal = nullptr;
            m_mc = nullptr;
            m_counter = 0;
            m_inconsistent = false;
            m_inconsistent_core = nullptr;
            init_forbidden_set(g);
        }
        
        // ---------------------------
        //
        // Internal data-structures
        //
        // ---------------------------
        
        static bool sign(literal l) { return l < 0; }
        static bvar lit2bvar(literal l) { return l < 0 ? -l : l; }
        
        bool is_int(var x) const { 
            return m_is_int[x] != 0;
        }
        
        bool is_forbidden(var x) const {
            return m_forbidden[x] != 0;
        }
        
        bool all_int(constraint const & c) const {
            for (unsigned i = 0; i < c.m_num_vars; i++) {
                if (!is_int(c.m_xs[i]))
                    return false;
            }
            return true;
        }
        
        app * to_expr(constraint const & c) {
            expr * ineq;
            if (c.m_num_vars == 0) {
                // 0 <  k (for k > 0)  --> true
                // 0 <= 0 -- > true
                if (c.m_c.is_pos() || (!c.m_strict && c.m_c.is_zero()))
                    return m.mk_true();
                ineq = nullptr;
            }
            else {
                bool int_cnstr = all_int(c);
                ptr_buffer<expr> ms;
                for (unsigned i = 0; i < c.m_num_vars; i++) {
                    expr * x = m_var2expr.get(c.m_xs[i]);
                    if (!int_cnstr && is_int(c.m_xs[i]))
                        x = m_util.mk_to_real(x);
                    if (c.m_as[i].is_one())
                        ms.push_back(x);
                    else
                        ms.push_back(m_util.mk_mul(m_util.mk_numeral(c.m_as[i], int_cnstr), x));
                }
                expr * lhs;
                if (c.m_num_vars == 1)
                    lhs = ms[0];
                else
                    lhs = m_util.mk_add(ms.size(), ms.data());
                expr * rhs = m_util.mk_numeral(c.m_c, int_cnstr);
                if (c.m_strict) {
                    ineq = m.mk_not(m_util.mk_ge(lhs, rhs));
                }
                else {
                    ineq = m_util.mk_le(lhs, rhs);
                }
            }
            
            if (c.m_num_lits == 0) {
                if (ineq)
                    return to_app(ineq);
                else
                    return m.mk_false();
            }
            
            ptr_buffer<expr> lits;
            for (unsigned i = 0; i < c.m_num_lits; i++) {
                literal l = c.m_lits[i];
                if (sign(l))
                    lits.push_back(m.mk_not(m_bvar2expr.get(lit2bvar(l))));
                else 
                    lits.push_back(m_bvar2expr.get(lit2bvar(l)));
            }
            if (ineq)
                lits.push_back(ineq);
            if (lits.size() == 1)
                return to_app(lits[0]);
            else
                return m.mk_or(lits.size(), lits.data());
        }
        
        var mk_var(expr * t) {
            SASSERT(is_uninterp_const(t));
            SASSERT(m_util.is_int(t) || m_util.is_real(t));
            var x = m_var2expr.size();
            m_var2expr.push_back(t);
            bool is_int = m_util.is_int(t);
            m_is_int.push_back(is_int);
            m_var2pos.push_back(UINT_MAX);
            m_expr2var.insert(t, x);
            m_lowers.push_back(constraints());
            m_uppers.push_back(constraints());
            bool forbidden = m_forbidden_set.contains(to_app(t)->get_decl()) || (m_fm_real_only && is_int);
            m_forbidden.push_back(forbidden);
            SASSERT(m_var2expr.size()  == m_is_int.size());
            SASSERT(m_lowers.size()    == m_is_int.size());
            SASSERT(m_uppers.size()    == m_is_int.size());
            SASSERT(m_forbidden.size() == m_is_int.size()); 
            SASSERT(m_var2pos.size()   == m_is_int.size());
            return x;
        }
        
        bvar mk_bvar(expr * t) {
            SASSERT(is_uninterp_const(t));
            SASSERT(m.is_bool(t));
            bvar p = m_bvar2expr.size();
            m_bvar2expr.push_back(t);
            m_bvar2sign.push_back(0);
            SASSERT(m_bvar2expr.size() == m_bvar2sign.size());
            m_expr2bvar.insert(t, p);
            SASSERT(p > 0);
            return p;
        }
        
        var to_var(expr * t) {
            var x;
            if (!m_expr2var.find(t, x))
                x = mk_var(t);
            SASSERT(m_expr2var.contains(t));
            SASSERT(m_var2expr.get(x) == t);
            TRACE("to_var_bug", tout << mk_ismt2_pp(t, m) << " --> " << x << "\n";);
            return x;
        }
        
        bvar to_bvar(expr * t) {
            bvar p;
            if (m_expr2bvar.find(t, p))
                return p;
            return mk_bvar(t);
        }
        
        literal to_literal(expr * t) {
            if (m.is_not(t, t))
                return -to_bvar(t); 
            else
                return to_bvar(t);
        }
        
        
        void add_constraint(expr * f, expr_dependency * dep) {
            SASSERT(!m.is_or(f) || m_fm_occ);
            sbuffer<literal> lits;
            sbuffer<var>     xs;
            buffer<rational> as;
            rational         c;
            bool             strict = false;
            unsigned         num;
            expr * const *   args;
            if (m.is_or(f)) {
                num  = to_app(f)->get_num_args();
                args = to_app(f)->get_args();
            }
            else {
                num  = 1;
                args = &f;
            }

#if Z3DEBUG
            bool found_ineq = false;
#endif
            for (unsigned i = 0; i < num; i++) {
                expr * l = args[i];
                if (is_literal(l)) {
                    lits.push_back(to_literal(l));
                }
                else {
                    // found inequality
                    SASSERT(!found_ineq);
                    DEBUG_CODE(found_ineq = true;);
                    bool neg    = m.is_not(l, l);
                    SASSERT(m_util.is_le(l) || m_util.is_ge(l));
                    strict      = neg;
                    if (m_util.is_ge(l))
                        neg = !neg;
                    expr * lhs = to_app(l)->get_arg(0);
                    expr * rhs = to_app(l)->get_arg(1);
                    m_util.is_numeral(rhs, c);
                    if (neg)
                        c.neg();
                    unsigned num_mons;
                    expr * const * mons;
                    if (m_util.is_add(lhs)) {
                        num_mons = to_app(lhs)->get_num_args();
                        mons     = to_app(lhs)->get_args();
                    }
                    else {
                        num_mons = 1;
                        mons     = &lhs;
                    }
                    
                    bool all_int = true;
                    for (unsigned j = 0; j < num_mons; j++) {
                        expr * monomial = mons[j];
                        expr * a;
                        rational a_val;
                        expr * x;
                        if (m_util.is_mul(monomial, a, x)) {
                            VERIFY(m_util.is_numeral(a, a_val));
                        }
                        else {
                            x     = monomial;
                            a_val = rational(1);
                        }
                        if (neg)
                            a_val.neg();
                        VERIFY(is_var(x, x));
                        xs.push_back(to_var(x));
                        as.push_back(a_val);
                        if (!is_int(xs.back()))
                            all_int = false;
                    }
                    mk_int(as.size(), as.data(), c);
                    if (all_int && strict) {
                        strict = false;
                        c--;
                    }
                }
            }
            
            TRACE("to_var_bug", tout << "before mk_constraint: "; for (unsigned i = 0; i < xs.size(); i++) tout << " " << xs[i]; tout << "\n";);
            
            constraint * new_c = mk_constraint(lits.size(),
                                               lits.data(),
                                               xs.size(),
                                               xs.data(),
                                               as.data(),
                                               c,
                                               strict,
                                               dep);
            
            TRACE("to_var_bug", tout << "add_constraint: "; display(tout, *new_c); tout << "\n";);
            VERIFY(register_constraint(new_c));
        }
        
        bool is_false(constraint const & c) const {
            return c.m_num_lits == 0 && c.m_num_vars == 0 && (c.m_c.is_neg() || (c.m_strict && c.m_c.is_zero()));
        }
        
        bool register_constraint(constraint * c) {
            normalize_coeffs(*c);
            if (is_false(*c)) {
                del_constraint(c);
                m_inconsistent = true;
                TRACE("add_constraint_bug", tout << "is false "; display(tout, *c); tout << "\n";);
                return false;
            }
            
            bool r = false;
            
            for (unsigned i = 0; i < c->m_num_vars; i++) {
                var x = c->m_xs[i];
                if (!is_forbidden(x)) {
                    r = true;
                    if (c->m_as[i].is_neg()) 
                        m_lowers[x].push_back(c);
                    else
                        m_uppers[x].push_back(c);
                }
            }
            
            if (r) {
                m_sub_todo.insert(*c);
                m_constraints.push_back(c);
                return true;
            }
            else {
                TRACE("add_constraint_bug", tout << "all variables are forbidden "; display(tout, *c); tout << "\n";);
                m_new_goal->assert_expr(to_expr(*c), nullptr, c->m_dep);
                del_constraint(c);
                return false;
            }
        }
        
        void init_use_list(goal const & g) {
            unsigned sz = g.size();
            for (unsigned i = 0; i < sz; i++) {
                if (m_inconsistent)
                    return;
                expr * f = g.form(i);
                if (is_occ(f))
                    add_constraint(f, g.dep(i));
                else
                    m_new_goal->assert_expr(f, nullptr, g.dep(i));
            }
        }

        unsigned get_cost(var x) const {
            unsigned long long r = static_cast<unsigned long long>(m_lowers[x].size()) * static_cast<unsigned long long>(m_uppers[x].size());
            if (r > UINT_MAX)
                return UINT_MAX;
            return static_cast<unsigned>(r);
        }
        
        typedef std::pair<var, unsigned> x_cost;
    
        struct x_cost_lt {
            char_vector const m_is_int;
            x_cost_lt(char_vector & is_int):m_is_int(is_int) {}
            bool operator()(x_cost const & p1, x_cost const & p2) const { 
                // Integer variables with cost 0 can be eliminated even if they depend on real variables.
                // Cost 0 == no lower or no upper bound.
                if (p1.second == 0) {
                    if (p2.second > 0) return true;
                    return p1.first < p2.first;
                }
                if (p2.second == 0) return false;
                bool int1 = m_is_int[p1.first] != 0;
                bool int2 = m_is_int[p2.first] != 0;
                return (!int1 && int2) || (int1 == int2 && p1.second < p2.second); 
            }
        };

        void sort_candidates(var_vector & xs) {
            svector<x_cost> x_cost_vector;
            unsigned num = num_vars();
            for (var x = 0; x < num; x++) {
                if (!is_forbidden(x)) {
                    x_cost_vector.push_back(x_cost(x, get_cost(x)));
                }
            }
            // x_cost_lt is not a total order on variables
            std::stable_sort(x_cost_vector.begin(), x_cost_vector.end(), x_cost_lt(m_is_int));
            TRACE("fm", 
                  svector<x_cost>::iterator it2  = x_cost_vector.begin();
                  svector<x_cost>::iterator end2 = x_cost_vector.end();
                  for (; it2 != end2; ++it2) {
                      tout << "(" << mk_ismt2_pp(m_var2expr.get(it2->first), m) << " " << it2->second << ") ";
                  }
                  tout << "\n";);
            svector<x_cost>::iterator it2  = x_cost_vector.begin();
            svector<x_cost>::iterator end2 = x_cost_vector.end();
            for (; it2 != end2; ++it2) {
                xs.push_back(it2->first);
            }
        }
        
        void cleanup_constraints(constraints & cs) {
            unsigned j = 0;
            unsigned sz = cs.size();
            for (unsigned i = 0; i < sz; i++) {
                constraint * c = cs[i];
                if (c->m_dead)
                    continue;
                cs[j] = c;
                j++;
            }
            cs.shrink(j);
        }
    
        // Set all_int = true if all variables in c are int.
        // Set unit_coeff = true if the coefficient of x in c is 1 or -1.
        // If all_int = false, then unit_coeff may not be set.
        void analyze(constraint const & c, var x, bool & all_int, bool & unit_coeff) const {
            all_int    = true;
            unit_coeff = true;
            for (unsigned i = 0; i < c.m_num_vars; i++) {
                if (!is_int(c.m_xs[i])) {
                    all_int = false;
                    return;
                }
                if (c.m_xs[i] == x) {
                    unit_coeff = (c.m_as[i].is_one() || c.m_as[i].is_minus_one());
                }
            }
        }

        void analyze(constraints const & cs, var x, bool & all_int, bool & unit_coeff) const {
            all_int    = true;
            unit_coeff = true;
            constraints::const_iterator it  = cs.begin();
            constraints::const_iterator end = cs.end();
            for (; it != end; ++it) {
                bool curr_unit_coeff;
                analyze(*(*it), x, all_int, curr_unit_coeff);
                if (!all_int)
                    return;
                if (!curr_unit_coeff)
                    unit_coeff = false;
            }
        }
        
        // An integer variable x may be eliminated, if 
        //   1- All variables in the constraints it occur are integer.
        //   2- The coefficient of x in all lower bounds (or all upper bounds) is unit.
        bool can_eliminate(var x) const {
            if (!is_int(x))
                return true;
            bool all_int;
            bool l_unit, u_unit;
            analyze(m_lowers[x], x, all_int, l_unit);
            if (!all_int)
                return false;
            analyze(m_uppers[x], x, all_int, u_unit);
            return all_int && (l_unit || u_unit);
        }
        
        void copy_constraints(constraints const & s, clauses & t) {
            constraints::const_iterator it  = s.begin();
            constraints::const_iterator end = s.end();
            for (; it != end; ++it) {
                app * c = to_expr(*(*it));
                t.push_back(c);
            }
        }
        
        clauses tmp_clauses;
        void save_constraints(var x) {
            if (m_produce_models) {
                tmp_clauses.reset();
                copy_constraints(m_lowers[x], tmp_clauses);
                copy_constraints(m_uppers[x], tmp_clauses);
                m_mc->insert(to_app(m_var2expr.get(x))->get_decl(), tmp_clauses);
            }
        }
        
        void mark_constraints_dead(constraints const & cs) {
            constraints::const_iterator it  = cs.begin();
            constraints::const_iterator end = cs.end();
            for (; it != end; ++it)
                (*it)->m_dead = true;
        }
        
        void mark_constraints_dead(var x) {
            save_constraints(x);
            mark_constraints_dead(m_lowers[x]);
            mark_constraints_dead(m_uppers[x]);
        }
        
        void get_coeff(constraint const & c, var x, rational & a) {
            for (unsigned i = 0; i < c.m_num_vars; i++) {
                if (c.m_xs[i] == x) {
                    a = c.m_as[i];
                    return;
                }
            }
            UNREACHABLE();
        }
        
        var_vector       new_xs;
        vector<rational> new_as;
        svector<literal> new_lits;
        
        constraint * resolve(constraint const & l, constraint const & u, var x) {
            m_counter += l.m_num_vars + u.m_num_vars + l.m_num_lits + u.m_num_lits;
            rational a, b;
            get_coeff(l, x, a);
            get_coeff(u, x, b);
            SASSERT(a.is_neg());
            SASSERT(b.is_pos());
            a.neg();
            
            SASSERT(!is_int(x) || a.is_one() || b.is_one());
            
            new_xs.reset();
            new_as.reset();
            rational         new_c = l.m_c*b + u.m_c*a;
            bool             new_strict = l.m_strict || u.m_strict;
            
            for (unsigned i = 0; i < l.m_num_vars; i++) {
                var xi = l.m_xs[i];
                if (xi == x)
                    continue;
                unsigned pos = new_xs.size();
                new_xs.push_back(xi);
                SASSERT(m_var2pos[xi] == UINT_MAX);
                m_var2pos[xi] = pos;
                new_as.push_back(l.m_as[i] * b);
                SASSERT(new_xs[m_var2pos[xi]] == xi);
                SASSERT(new_xs.size() == new_as.size());
            }
            
            for (unsigned i = 0; i < u.m_num_vars; i++) {
                var xi = u.m_xs[i];
                if (xi == x)
                    continue;
                unsigned pos = m_var2pos[xi];
                if (pos == UINT_MAX) {
                    new_xs.push_back(xi);
                    new_as.push_back(u.m_as[i] * a);
                }
                else {
                    new_as[pos] += u.m_as[i] * a;
                }
            }
            
            // remove zeros and check whether all variables are int
            bool all_int = true;
            unsigned sz = new_xs.size();
            unsigned j  = 0;
            for (unsigned i = 0; i < sz; i++) {
                if (new_as[i].is_zero())
                    continue;
                if (!is_int(new_xs[i]))
                    all_int = false;
                if (i != j) {
                    new_xs[j] = new_xs[i];
                    new_as[j] = new_as[i];
                }
                j++;
            }
            new_xs.shrink(j);
            new_as.shrink(j);
            
            if (all_int && new_strict) {
                new_strict = false;
                new_c --;
            }
            
            // reset m_var2pos
            for (unsigned i = 0; i < l.m_num_vars; i++) {
                m_var2pos[l.m_xs[i]] = UINT_MAX;
            }
            
            if (new_xs.empty() && (new_c.is_pos() || (!new_strict && new_c.is_zero()))) {
                // literal is true
                TRACE("fm", tout << "resolution " << x << " consequent literal is always true: \n";
                      display(tout, l);
                      tout << "\n";
                      display(tout, u); tout << "\n";);
                return nullptr; // no constraint needs to be created.
            }
            
            new_lits.reset();
            for (unsigned i = 0; i < l.m_num_lits; i++) {
                literal lit = l.m_lits[i];
                bvar    p   = lit2bvar(lit);
                m_bvar2sign[p] = sign(lit) ? -1 : 1;
                new_lits.push_back(lit);
            }
            
            bool tautology = false;
            for (unsigned i = 0; i < u.m_num_lits && !tautology; i++) {
                literal lit = u.m_lits[i];
                bvar    p   = lit2bvar(lit);
                switch (m_bvar2sign[p]) {
                case 0:
                    new_lits.push_back(lit);
                break;
                case -1:
                    if (!sign(lit))
                        tautology = true;
                    break;
                case 1:
                    if (sign(lit))
                        tautology = true;
                    break;
                default:
                    UNREACHABLE();
                }
            }
            
            // reset m_bvar2sign
            for (unsigned i = 0; i < l.m_num_lits; i++) {
                literal lit = l.m_lits[i];
                bvar    p   = lit2bvar(lit);
                m_bvar2sign[p] = 0;
            }
            
            if (tautology) {
                TRACE("fm", tout << "resolution " << x << " tautology: \n";
                      display(tout, l);
                      tout << "\n";
                      display(tout, u); tout << "\n";);
                return nullptr;
            }

            expr_dependency * new_dep = m.mk_join(l.m_dep, u.m_dep);
            
            if (new_lits.empty() && new_xs.empty() && (new_c.is_neg() || (new_strict && new_c.is_zero()))) {
                TRACE("fm", tout << "resolution " << x << " inconsistent: \n";
                      display(tout, l);
                      tout << "\n";
                      display(tout, u); tout << "\n";);
                m_inconsistent      = true;
                m_inconsistent_core = new_dep;
                return nullptr;
            }
            
            constraint * new_cnstr = mk_constraint(new_lits.size(),
                                                   new_lits.data(),
                                                   new_xs.size(),
                                                   new_xs.data(),
                                                   new_as.data(),
                                                   new_c,
                                                   new_strict,
                                                   new_dep);

            TRACE("fm", tout << "resolution " << x << "\n";
                  display(tout, l);
                  tout << "\n";
                  display(tout, u);
                  tout << "\n---->\n";
                  display(tout, *new_cnstr); 
                  tout << "\n";
                  tout << "new_dep: " << new_dep << "\n";);
            
            return new_cnstr;
        }
        
        ptr_vector<constraint> new_constraints;
        
        bool try_eliminate(var x) {
            constraints & l = m_lowers[x];
            constraints & u = m_uppers[x];
            cleanup_constraints(l);
            cleanup_constraints(u);
            
            if (l.empty() || u.empty()) {
                // easy case
                mark_constraints_dead(x);
                TRACE("fm", tout << "variables was eliminated (trivial case)\n";);
                return true;
            }
            
            unsigned num_lowers = l.size();
            unsigned num_uppers = u.size();
            
            if (num_lowers > m_fm_cutoff1 && num_uppers > m_fm_cutoff1)
                return false;
            
            if (num_lowers * num_uppers > m_fm_cutoff2)
                return false;
            
            if (!can_eliminate(x))
                return false;
            
            m_counter += num_lowers * num_uppers;
            
            TRACE("fm_bug", tout << "eliminating " << mk_ismt2_pp(m_var2expr.get(x), m) << "\nlowers:\n";
                  display_constraints(tout, l); tout << "uppers:\n"; display_constraints(tout, u););
            
            unsigned num_old_cnstrs = num_uppers + num_lowers;
            unsigned limit          = num_old_cnstrs + m_fm_extra;
            unsigned num_new_cnstrs = 0;
            new_constraints.reset();
            for (unsigned i = 0; i < num_lowers; i++) {
                for (unsigned j = 0; j < num_uppers; j++) {
                    if (m_inconsistent || num_new_cnstrs > limit) {
                        TRACE("fm", tout << "too many new constraints: " << num_new_cnstrs << "\n";);
                        del_constraints(new_constraints.size(), new_constraints.data());
                        return false;
                    }
                    constraint const & l_c = *(l[i]);
                    constraint const & u_c = *(u[j]);
                    constraint * new_c = resolve(l_c, u_c, x);
                    if (new_c != nullptr) {
                        num_new_cnstrs++;
                        new_constraints.push_back(new_c);
                    }
                }
            }
            
            mark_constraints_dead(x);
            
            unsigned sz = new_constraints.size();
            
            m_counter += sz;
            
            for (unsigned i = 0; i < sz; i++) {
                constraint * c = new_constraints[i];
                backward_subsumption(*c);
                register_constraint(c);
            }
            TRACE("fm", tout << "variables was eliminated old: " << num_old_cnstrs << " new_constraints: " << sz << "\n";);
            return true;
        }
        
        void copy_remaining(vector<constraints> & v2cs) {
            vector<constraints>::iterator it  = v2cs.begin();
            vector<constraints>::iterator end = v2cs.end();
            for (; it != end; ++it) {
                constraints & cs = *it;
                constraints::iterator it2  = cs.begin();
                constraints::iterator end2 = cs.end();
                for (; it2 != end2; ++it2) {
                    constraint * c = *it2;
                    if (!c->m_dead) {
                        c->m_dead = true;
                        expr * new_f = to_expr(*c);
                        TRACE("fm_bug", tout << "asserting...\n" << mk_ismt2_pp(new_f, m) << "\nnew_dep: " << c->m_dep << "\n";);
                        m_new_goal->assert_expr(new_f, nullptr, c->m_dep);
                    }
                }
            }
            v2cs.finalize();
        }
        
        // Copy remaining clauses to m_new_goal
        void copy_remaining() {
            copy_remaining(m_uppers);
            copy_remaining(m_lowers);
        }
        
        void checkpoint() {
            if (!m.inc())
                throw tactic_exception(m.limit().get_cancel_msg());
            if (memory::get_allocation_size() > m_max_memory)
                throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
        }
        
        void operator()(goal_ref const & g, 
                        goal_ref_buffer & result) {
            tactic_report report("fm", *g);
            fail_if_proof_generation("fm", g);
            m_produce_models = g->models_enabled();
            
            init(*g);
            
            m_new_goal = alloc(goal, *g, true);
            SASSERT(m_new_goal->depth() == g->depth());
            SASSERT(m_new_goal->prec() == g->prec());
            m_new_goal->inc_depth();

            init_use_list(*g);
            
            if (m_inconsistent) {
                m_new_goal->reset();
                m_new_goal->assert_expr(m.mk_false(), nullptr, m_inconsistent_core);
            }
            else {
                TRACE("fm", display(tout););
                
                subsume();
                var_vector candidates;
                sort_candidates(candidates);
                
                unsigned eliminated = 0;
                
                if (m_produce_models)
                    m_mc = alloc(fm_model_converter, m);
                
                unsigned num = candidates.size();
                for (unsigned i = 0; i < num; i++) {
                    checkpoint();
                    if (m_counter > m_fm_limit)
                        break;
                    m_counter++;
                    if (try_eliminate(candidates[i]))
                        eliminated++;
                    if (m_inconsistent) {
                        m_new_goal->reset();
                        m_new_goal->assert_expr(m.mk_false(), nullptr, m_inconsistent_core);
                        break;
                    }
                }
                report_tactic_progress(":fm-eliminated", eliminated);
                report_tactic_progress(":fm-cost", m_counter);
                if (!m_inconsistent) {
                    copy_remaining();
                    m_new_goal->add(concat(g->mc(), m_mc.get()));
                }
            }
            reset_constraints();
            result.push_back(m_new_goal.get());
            TRACE("fm", m_new_goal->display(tout););
        }
        
        void display_constraints(std::ostream & out, constraints const & cs) const {
            constraints::const_iterator it  = cs.begin();
            constraints::const_iterator end = cs.end();
            for (; it != end; ++it) {
                out << "  ";
                display(out, *(*it));
                out << "\n";
            }
        }
        
        void display(std::ostream & out) const {
            unsigned num = num_vars();
            for (var x = 0; x < num; x++) {
                if (is_forbidden(x))
                    continue;
                out << mk_ismt2_pp(m_var2expr.get(x), m) << "\n";
                display_constraints(out, m_lowers[x]);
                display_constraints(out, m_uppers[x]);
            }
        }
    };

    imp *      m_imp;
    params_ref m_params;
public:

    fm_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(fm_tactic, m, m_params);
    }

    ~fm_tactic() override {
        dealloc(m_imp);
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
        m_imp->updt_params(p);
    }

    void collect_param_descrs(param_descrs & r) override {
        insert_produce_models(r);
        insert_max_memory(r);
        r.insert("fm_real_only", CPK_BOOL, "(default: true) consider only real variables for fourier-motzkin elimination.");
        r.insert("fm_occ", CPK_BOOL, "(default: false) consider inequalities occurring in clauses for FM.");
        r.insert("fm_limit", CPK_UINT, "(default: 5000000) maximum number of constraints, monomials, clauses visited during FM.");
        r.insert("fm_cutoff1", CPK_UINT, "(default: 8) first cutoff for FM based on maximum number of lower/upper occurrences.");
        r.insert("fm_cutoff2", CPK_UINT, "(default: 256) second cutoff for FM based on num_lower * num_upper occurrences.");
        r.insert("fm_extra", CPK_UINT, "(default: 0) max. increase on the number of inequalities for each FM variable elimination step.");
    }


    void cleanup() override {
        imp * d = alloc(imp, m_imp->m, m_params);
        std::swap(d, m_imp);        
        dealloc(d);
    }

    void operator()(goal_ref const & in, 
                    goal_ref_buffer & result) override {
        (*m_imp)(in, result);
    }
};

tactic * mk_fm_tactic(ast_manager & m, params_ref const & p) {
    params_ref s_p = p;
    s_p.set_bool("arith_lhs", true);
    s_p.set_bool("elim_and", true);
    s_p.set_bool("som", true);
    return and_then(using_params(mk_simplify_tactic(m, s_p), s_p), 
                    clean(alloc(fm_tactic, m, p)));
}
