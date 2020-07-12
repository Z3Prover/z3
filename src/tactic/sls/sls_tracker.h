/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    sls_score_tracker.h

Abstract:

    Score and value tracking module for SLS

Author:

    Christoph (cwinter) 2012-02-29

Notes:

--*/

#pragma once

#include<math.h>
#include "ast/for_each_expr.h"
#include "ast/ast_smt2_pp.h"
#include "ast/bv_decl_plugin.h"
#include "model/model.h"

#include "tactic/sls/sls_params.hpp"
#include "tactic/sls/sls_powers.h"

class sls_tracker {
    ast_manager         & m_manager;
    unsynch_mpz_manager & m_mpz_manager;
    bv_util             & m_bv_util;
    powers              & m_powers;
    random_gen            m_rng;
    unsigned              m_random_bits;
    unsigned              m_random_bits_cnt;
    mpz                   m_zero, m_one, m_two;

    struct value_score {
    value_score() : m(nullptr), value(unsynch_mpz_manager::mk_z(0)), score(0.0), score_prune(0.0), has_pos_occ(0), has_neg_occ(0), distance(0), touched(1) {};
        value_score(value_score&&) noexcept = default;
        ~value_score() { if (m) m->del(value); }
        value_score& operator=(value_score&&) = default;
        unsynch_mpz_manager * m;
        mpz value;
        double score;
        double score_prune;
        unsigned has_pos_occ;
        unsigned has_neg_occ;
        unsigned distance; // max distance from any root
        unsigned touched;
    };

public:
    typedef obj_map<func_decl, expr* > entry_point_type;

private:
    typedef obj_map<expr, value_score> scores_type;    
    typedef obj_map<expr, ptr_vector<expr> > uplinks_type;    
    typedef obj_map<expr, ptr_vector<func_decl> > occ_type;
    obj_hashtable<expr>      m_top_expr;
    scores_type           m_scores;
    uplinks_type          m_uplinks;
    entry_point_type      m_entry_points;
    ptr_vector<func_decl> m_constants;
    ptr_vector<func_decl> m_temp_constants;
    occ_type              m_constants_occ;
    unsigned              m_last_pos;
    unsigned              m_walksat;
    unsigned              m_ucb;
    double                m_ucb_constant;
    unsigned              m_ucb_init;
    double                m_ucb_forget;
    double                m_ucb_noise;
    unsigned              m_touched;
    double                m_scale_unsat;
    unsigned              m_paws_init;
    obj_map<expr, unsigned>    m_where_false;
    expr**                    m_list_false;
    unsigned              m_track_unsat;
    obj_map<expr, unsigned> m_weights;
    double                  m_top_sum;
    obj_hashtable<expr>   m_temp_seen;

public:    
    sls_tracker(ast_manager & m, bv_util & bvu, unsynch_mpz_manager & mm, powers & p) :
        m_manager(m),
        m_mpz_manager(mm),
        m_bv_util(bvu),
        m_powers(p),
        m_random_bits_cnt(0),        
        m_zero(m_mpz_manager.mk_z(0)),
        m_one(m_mpz_manager.mk_z(1)),
        m_two(m_mpz_manager.mk_z(2)) {
    }
            
    ~sls_tracker() {
        m_mpz_manager.del(m_zero);
        m_mpz_manager.del(m_one);
        m_mpz_manager.del(m_two);            
    }

    void updt_params(params_ref const & _p) {
        sls_params p(_p);
        m_walksat = p.walksat();
        m_ucb = p.walksat_ucb();
        m_ucb_constant = p.walksat_ucb_constant();
        m_ucb_init = p.walksat_ucb_init();
        m_ucb_forget = p.walksat_ucb_forget();
        m_ucb_noise = p.walksat_ucb_noise();
        m_scale_unsat = p.scale_unsat();
        m_paws_init = p.paws_init();
        // Andreas: track_unsat is currently disabled because I cannot guarantee that it is not buggy.
        // If you want to use it, you will also need to change comments in the assertion selection.
        m_track_unsat = 0;//p.track_unsat();
    }

    /* Andreas: Tried to give some measure for the formula size by the following two methods but both are not used currently.
    unsigned get_formula_size() {
        return m_scores.size();
    }

    double get_avg_bw(goal_ref const & g) {
        double sum = 0.0;
        unsigned count = 0;

        for (unsigned i = 0; i < g->size(); i++)
        {
            m_temp_constants.reset();
            ptr_vector<func_decl> const & this_decls = m_constants_occ.find(g->form(i));
            unsigned sz = this_decls.size();
            for (unsigned i = 0; i < sz; i++) {
                func_decl * fd = this_decls[i];
                m_temp_constants.push_back(fd);
                sort * srt = fd->get_range();
                sum += (m_manager.is_bool(srt)) ? 1 : m_bv_util.get_bv_size(srt);         
                count++;
            }
        }

        return sum / count;   
    }*/

    inline void adapt_top_sum(expr * e, double add, double sub) {
        m_top_sum += m_weights.find(e) * (add - sub);
    }

    inline void set_top_sum(double new_score) {
        m_top_sum = new_score;
    }

    inline double get_top_sum() {
        return m_top_sum;
    }

    inline obj_hashtable<expr> const & get_top_exprs() {
        return m_top_expr;
    }

    inline bool is_sat() {
        for (obj_hashtable<expr>::iterator it = m_top_expr.begin();
             it != m_top_expr.end();
             it++)
            if (!m_mpz_manager.is_one(get_value(*it)))
                return false;
        return true;
    }

    inline void set_value(expr * n, const mpz & r) {
        SASSERT(m_scores.contains(n));
        m_mpz_manager.set(m_scores.find(n).value, r);
    }

    inline void set_value(func_decl * fd, const mpz & r) {
        SASSERT(m_entry_points.contains(fd));
        expr * ep = get_entry_point(fd);
        set_value(ep, r);
    }

    inline mpz & get_value(expr * n) {            
        SASSERT(m_scores.contains(n));
        return m_scores.find(n).value;
    }

    inline mpz & get_value(func_decl * fd) {
        SASSERT(m_entry_points.contains(fd));
        expr * ep = get_entry_point(fd);
        return get_value(ep);
    }        

    inline void set_score(expr * n, double score) {
        SASSERT(m_scores.contains(n));
        m_scores.find(n).score = score;
    }

    inline void set_score(func_decl * fd, double score) {            
        SASSERT(m_entry_points.contains(fd));
        expr * ep = get_entry_point(fd);
        set_score(ep, score);    
    }

    inline double & get_score(expr * n) {
        SASSERT(m_scores.contains(n));
        return m_scores.find(n).score;
    }

    inline double & get_score(func_decl * fd) {
        SASSERT(m_entry_points.contains(fd));
        expr * ep = get_entry_point(fd);
        return get_score(ep);
    }

    inline void set_score_prune(expr * n, double score) {
        SASSERT(m_scores.contains(n));
        m_scores.find(n).score_prune = score;
    }

    inline double & get_score_prune(expr * n) {
        SASSERT(m_scores.contains(n));
        return m_scores.find(n).score_prune;
    }

    inline unsigned has_pos_occ(expr * n) {
        SASSERT(m_scores.contains(n));
        return m_scores.find(n).has_pos_occ;
    }

    inline unsigned has_neg_occ(expr * n) {
        SASSERT(m_scores.contains(n));
        return m_scores.find(n).has_neg_occ;
    }

    inline unsigned get_distance(expr * n) {
        SASSERT(m_scores.contains(n));
        return m_scores.find(n).distance;
    }

    inline void set_distance(expr * n, unsigned d) {
        SASSERT(m_scores.contains(n));
        m_scores.find(n).distance = d;
    }

    inline expr * get_entry_point(func_decl * fd) {
        SASSERT(m_entry_points.contains(fd));
        return m_entry_points.find(fd);
    }

    inline entry_point_type const & get_entry_points() {
        return m_entry_points;
    }

    inline bool has_uplinks(expr * n) {
        return m_uplinks.contains(n);
    }

    inline bool is_top_expr(expr * n) {
        return m_top_expr.contains(n);
    }

    inline ptr_vector<expr> & get_uplinks(expr * n) {
        SASSERT(m_uplinks.contains(n));
        return m_uplinks.find(n);
    }

    inline void ucb_forget(ptr_vector<expr> & as) {
        if (m_ucb_forget < 1.0)
        {
            expr * e;
            unsigned touched_old, touched_new;

            for (unsigned i = 0; i < as.size(); i++)
            {
                e = as[i];
                touched_old = m_scores.find(e).touched;
                touched_new = (unsigned)((touched_old - 1) * m_ucb_forget + 1);
                m_scores.find(e).touched = touched_new;
                m_touched += touched_new - touched_old;
            }
        }
    }

    void initialize(app * n) {
        // Build score table
        if (!m_scores.contains(n)) {
            value_score vs;
            vs.m = & m_mpz_manager;
            m_scores.insert(n, std::move(vs));
        }

        // Update uplinks
        unsigned na = n->get_num_args();
        for (unsigned i = 0; i < na; i++) {
            expr * c = n->get_arg(i); 
            m_uplinks.insert_if_not_there(c, ptr_vector<expr>()).push_back(n);
        }

        func_decl * d = n->get_decl();

        if (n->get_num_args() == 0) {
            if (d->get_family_id() != null_family_id) {
                // Interpreted constant
                mpz t;
                value2mpz(n, t);
                set_value(n, t);
                m_mpz_manager.del(t);
            }
            else {
                // Uninterpreted constant
                m_entry_points.insert_if_not_there(d, n);
                m_constants.push_back(d);
            }
        }            
    }

    struct init_proc {
        ast_manager & m_manager;        
        sls_tracker & m_tracker;

        init_proc(ast_manager & m, sls_tracker & tracker):
            m_manager(m),
            m_tracker(tracker) {
        }
        
        void operator()(var * n) {}
        
        void operator()(quantifier * n) {}
        
        void operator()(app * n) {
            m_tracker.initialize(n);
        }
    };

    struct find_func_decls_proc {
        ast_manager   & m_manager;        
        ptr_vector<func_decl> & m_occs;

        find_func_decls_proc (ast_manager & m, ptr_vector<func_decl> & occs):
            m_manager(m),
            m_occs(occs) {
        }
        
        void operator()(var * n) {}
        
        void operator()(quantifier * n) {}
        
        void operator()(app * n) {
            if (n->get_num_args() != 0)
                return;
            func_decl * d = n->get_decl();
            if (d->get_family_id() != null_family_id)
                return;
            m_occs.push_back(d);
        }
    };

    void calculate_expr_distances(ptr_vector<expr> const & as) {
        // precondition: m_scores is set up.
        unsigned sz = as.size();
        ptr_vector<app> stack;
        for (unsigned i = 0; i < sz; i++)
            stack.push_back(to_app(as[i]));
        while (!stack.empty()) {
            app * cur = stack.back();
            stack.pop_back();
                
            unsigned d = get_distance(cur);

            for (unsigned i = 0; i < cur->get_num_args(); i++) {
                app * child = to_app(cur->get_arg(i));                    
                unsigned d_child = get_distance(child);
                if (d >= d_child) {
                    set_distance(child, d+1);
                    stack.push_back(child);
                }
            }
        }
    }

    /* Andreas: Used this at some point to have values for the non-top-level expressions.
                However, it did not give better performance but even cause some additional m/o - is not used currently.
    void initialize_recursive(init_proc proc, expr_mark visited, expr * e) {
        if (m_manager.is_and(e) || m_manager.is_or(e)) {
            app * a = to_app(e);
            expr * const * args = a->get_args();
            unsigned int sz = a->get_num_args();
            for (unsigned int i = 0; i < sz; i++) {
                expr * q = args[i];
                initialize_recursive(proc, visited, q);
            }
        }
        for_each_expr(proc, visited, e);
    }

    void initialize_recursive(expr * e) {
        if (m_manager.is_and(e) || m_manager.is_or(e)) {
            app * a = to_app(e);
            expr * const * args = a->get_args();
            unsigned int sz = a->get_num_args();
            for (unsigned int i = 0; i < sz; i++) {
                expr * q = args[i];
                initialize_recursive(q);
            }
        }
        ptr_vector<func_decl> t;
        m_constants_occ.insert_if_not_there(e, t);
        find_func_decls_proc ffd_proc(m_manager, m_constants_occ.find(e));
        expr_fast_mark1 visited;
        quick_for_each_expr(ffd_proc, visited, e);
    }*/

    void initialize(ptr_vector<expr> const & as) {
        init_proc proc(m_manager, *this);
        expr_mark visited;
        unsigned sz = as.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * e = as[i];
            if (!m_top_expr.contains(e))
                m_top_expr.insert(e);
            for_each_expr(proc, visited, e);
        }

        visited.reset();

        for (unsigned i = 0; i < sz; i++) {
            expr * e = as[i];
            ptr_vector<func_decl> t;
            m_constants_occ.insert_if_not_there(e, t);
            find_func_decls_proc ffd_proc(m_manager, m_constants_occ.find(e));
            expr_fast_mark1 visited;
            quick_for_each_expr(ffd_proc, visited, e);
        }

        calculate_expr_distances(as);

        TRACE("sls", tout << "Initial model:" << std::endl; show_model(tout); );

        if (m_track_unsat)
        {
            m_list_false = new expr*[sz];
            for (unsigned i = 0; i < sz; i++)
            {
                if (m_mpz_manager.eq(get_value(as[i]), m_zero))
                    break_assertion(as[i]);
            }
        }

        m_temp_seen.reset();
        for (unsigned i = 0; i < sz; i++)
        {
            expr * e = as[i];

            // initialize weights
            if (!m_weights.contains(e))
                m_weights.insert(e, m_paws_init);

            // positive/negative occurrences used for early pruning
            setup_occs(as[i]);
        }

        // initialize ucb total touched value (individual ones are always initialized to 1)
        m_touched = m_ucb_init ? as.size() : 1;
    }

    void increase_weight(expr * e)
    {
        m_weights.find(e)++;
    }

    void decrease_weight(expr * e)
    {
        unsigned old_weight = m_weights.find(e);
        m_weights.find(e) = old_weight > m_paws_init ? old_weight - 1 : m_paws_init;
    }

    unsigned get_weight(expr * e)
    {
        return m_weights.find(e);
    }

    void make_assertion(expr * e)
    {
        if (m_track_unsat)
        {
            if (m_where_false.contains(e))
            {
                unsigned pos = m_where_false.find(e);
                m_where_false.erase(e);
                if (pos != m_where_false.size())
                {
                    expr * q = m_list_false[m_where_false.size()];
                    m_list_false[pos] = q;
                    m_where_false.find(q) = pos;
                }
            }
        }
    }

    void break_assertion(expr * e)
    {
        if (m_track_unsat)
        {
            if (!m_where_false.contains(e))
            {
                unsigned pos = m_where_false.size();
                m_list_false[pos] = e;
                m_where_false.insert(e, pos);
            }
        }
    }

    void show_model(std::ostream & out) {
        unsigned sz = get_num_constants();
        for (unsigned i = 0; i < sz; i++) {
            func_decl * fd = get_constant(i);
            out << fd->get_name() << " = " << m_mpz_manager.to_string(get_value(fd)) << std::endl;
        }
    }

    void set_model(model_ref const & mdl) {
        for (unsigned i = 0; i < mdl->get_num_constants(); i++) {
            func_decl * fd = mdl->get_constant(i);
            expr * val = mdl->get_const_interp(fd);
            if (m_entry_points.contains(fd)) {
                if (m_manager.is_bool(val)) {
                    set_value(fd, m_manager.is_true(val) ? m_mpz_manager.mk_z(1) : m_mpz_manager.mk_z(0));
                }
                else if (m_bv_util.is_numeral(val)) {
                    rational r_val;
                    unsigned bv_sz;
                    m_bv_util.is_numeral(val, r_val, bv_sz);
                    const mpq& q = r_val.to_mpq();
                    SASSERT(m_mpz_manager.is_one(q.denominator()));
                    set_value(fd, q.numerator());
                }
                else
                    NOT_IMPLEMENTED_YET();
            }
        }
    }

    model_ref get_model() {
        model_ref res = alloc(model, m_manager);
        unsigned sz = get_num_constants();
        for (unsigned i = 0; i < sz; i++) {
            func_decl * fd = get_constant(i);
            res->register_decl(fd, mpz2value(fd->get_range(), get_value(fd)));
        }
        return res;
    }

    unsigned get_num_constants() {
        return m_constants.size();
    }

    ptr_vector<func_decl> & get_constants() {
        return m_constants;
    }

    func_decl * get_constant(unsigned i) {
        return m_constants[i];
    }

    void set_random_seed(unsigned s) {
        m_rng.set_seed(s);
    }

    mpz get_random_bv(sort * s) {
        SASSERT(m_bv_util.is_bv_sort(s));
        unsigned bv_size = m_bv_util.get_bv_size(s);
        mpz r; m_mpz_manager.set(r, 0);            

        mpz temp;
        do
        {                
            m_mpz_manager.mul(r, m_two, temp);                
            m_mpz_manager.add(temp, get_random_bool(), r);
        } while (--bv_size > 0);            
        m_mpz_manager.del(temp);

        return r;
    }

    mpz & get_random_bool() {
        if (m_random_bits_cnt == 0) {
            m_random_bits = m_rng();
            m_random_bits_cnt = 15; // random_gen produces 15 bits of randomness.
        }

        bool val = (m_random_bits & 0x01) != 0;
        m_random_bits = m_random_bits >> 1;
        m_random_bits_cnt--;

        return (val) ? m_one : m_zero;
    }

    unsigned get_random_uint(unsigned bits) {
        if (m_random_bits_cnt == 0) {
            m_random_bits = m_rng();
            m_random_bits_cnt = 15; // random_gen produces 15 bits of randomness.
        }

        unsigned val = 0;
        while (bits-- > 0) {
            if ((m_random_bits & 0x01) != 0) val++;
            val <<= 1;
            m_random_bits >>= 1;
            m_random_bits_cnt--;

            if (m_random_bits_cnt == 0) {
                m_random_bits = m_rng();
                m_random_bits_cnt = 15; // random_gen produces 15 bits of randomness.
            }
        }

        return val;
    }

    mpz get_random(sort * s) {
        if (m_bv_util.is_bv_sort(s))
            return get_random_bv(s);
        else if (m_manager.is_bool(s))
            return m_mpz_manager.dup(get_random_bool());
        else {
            NOT_IMPLEMENTED_YET(); // This only works for bit-vectors for now.
            return get_random_bv(nullptr);
        }
    }    

    void randomize(ptr_vector<expr> const & as) {
        TRACE("sls", tout << "Abandoned model:" << std::endl; show_model(tout); );

        for (entry_point_type::iterator it = m_entry_points.begin(); it != m_entry_points.end(); it++) {
            func_decl * fd = it->m_key;
            sort * s = fd->get_range();
            mpz temp = get_random(s);
            set_value(it->m_value, temp);
            m_mpz_manager.del(temp);
        }

        TRACE("sls", tout << "Randomized model:" << std::endl; show_model(tout); );
    }              

    void reset(ptr_vector<expr> const & as) {
        TRACE("sls", tout << "Abandoned model:" << std::endl; show_model(tout); );

        for (entry_point_type::iterator it = m_entry_points.begin(); it != m_entry_points.end(); it++) {
            set_value(it->m_value, m_zero);
        }
    }              

    void setup_occs(expr * n, bool negated = false) {
        if (m_manager.is_bool(n))
        {
            if (m_manager.is_and(n) || m_manager.is_or(n))
            {
                SASSERT(!negated);
                app * a = to_app(n);
                expr * const * args = a->get_args();
                for (unsigned i = 0; i < a->get_num_args(); i++)
                {
                    expr * child = args[i];
                    if (!m_temp_seen.contains(child))
                    {
                        setup_occs(child, false);
                        m_temp_seen.insert(child);
                    }
                }
            }
            else if (m_manager.is_not(n))
            {
                SASSERT(!negated);
                app * a = to_app(n);
                SASSERT(a->get_num_args() == 1);
                expr * child = a->get_arg(0);
                SASSERT(!m_manager.is_and(child) && !m_manager.is_or(child));
                setup_occs(child, true);
            }
            else
            {
                if (negated)
                    m_scores.find(n).has_neg_occ = 1;
                else
                    m_scores.find(n).has_pos_occ = 1;
            }
        }
        else if (m_bv_util.is_bv(n)) {
            /* CMW: I need this for optimization. Safe to ignore? */
        }
        else
            NOT_IMPLEMENTED_YET();
    }

    double score_bool(expr * n, bool negated = false) {
        TRACE("sls_score", tout << ((negated)?"NEG ":"") << "BOOL: " << mk_ismt2_pp(n, m_manager) << std::endl; );

        double res = 0.0;
            
        if (is_uninterp_const(n)) {
            const mpz & r = get_value(n);
            if (negated)
                res = (m_mpz_manager.is_one(r)) ? 0.0 : 1.0;
            else
                res = (m_mpz_manager.is_one(r)) ? 1.0 : 0.0;
        }            
        else if (m_manager.is_and(n)) {
            SASSERT(!negated);
            app * a = to_app(n);
            expr * const * args = a->get_args();
            /* Andreas: Seems to have no effect. But maybe you want to try it again at some point.
            double sum = 0.0;
            for (unsigned i = 0; i < a->get_num_args(); i++)
                sum += get_score(args[i]);
            res = sum / (double) a->get_num_args(); */
            double min = 1.0;
            for (unsigned i = 0; i < a->get_num_args(); i++) {
                double cur = get_score(args[i]);
                if (cur < min) min = cur;
            }
            res = min;
        }
        else if (m_manager.is_or(n)) {
            SASSERT(!negated);
            app * a = to_app(n);
            expr * const * args = a->get_args();
            double max = 0.0;
            for (unsigned i = 0; i < a->get_num_args(); i++) {
                double cur = get_score(args[i]);
                if (cur > max) max = cur;
            }
            res = max;
        }
        else if (m_manager.is_ite(n)) {
            SASSERT(!negated);
            app * a = to_app(n);
            SASSERT(a->get_num_args() == 3);
            const mpz & cond = get_value(a->get_arg(0));
            double s_t = get_score(a->get_arg(1));
            double s_f = get_score(a->get_arg(2));
            res = (m_mpz_manager.is_one(cond)) ? s_t : s_f;
        }
        else if (m_manager.is_eq(n) || m_manager.is_iff(n)) {                
            app * a = to_app(n);
            SASSERT(a->get_num_args() == 2);
            expr * arg0 = a->get_arg(0);
            expr * arg1 = a->get_arg(1);
            const mpz & v0 = get_value(arg0);
            const mpz & v1 = get_value(arg1);
            
            if (negated) {                    
                res = (m_mpz_manager.eq(v0, v1)) ? 0.0 : 1.0;
                TRACE("sls_score", tout << "V0 = " << m_mpz_manager.to_string(v0) << " ; V1 = " << 
                                        m_mpz_manager.to_string(v1) << std::endl; );
            }
            else if (m_manager.is_bool(arg0)) {
                res = m_mpz_manager.eq(v0, v1) ? 1.0 : 0.0;
                TRACE("sls_score", tout << "V0 = " << m_mpz_manager.to_string(v0) << " ; V1 = " << 
                                        m_mpz_manager.to_string(v1) << std::endl; );
            }
            else if (m_bv_util.is_bv(arg0)) {
                mpz diff, diff_m1;
                m_mpz_manager.bitwise_xor(v0, v1, diff);
                unsigned hamming_distance = 0;
                unsigned bv_sz = m_bv_util.get_bv_size(arg0);
                // unweighted hamming distance
                while (!m_mpz_manager.is_zero(diff)) {
                    if (!m_mpz_manager.is_even(diff)) {
                        hamming_distance++;
                    }
                    m_mpz_manager.machine_div(diff, m_two, diff);
                }
                res = 1.0 - (hamming_distance / (double) bv_sz);
                TRACE("sls_score", tout << "V0 = " << m_mpz_manager.to_string(v0) << " ; V1 = " << 
                                        m_mpz_manager.to_string(v1) << " ; HD = " << hamming_distance << 
                                        " ; SZ = " << bv_sz << std::endl; );                    
                m_mpz_manager.del(diff);
                m_mpz_manager.del(diff_m1);
            }
            else
                NOT_IMPLEMENTED_YET();
        }            
        else if (m_bv_util.is_bv_ule(n)) { // x <= y
            app * a = to_app(n);
            SASSERT(a->get_num_args() == 2);
            const mpz & x = get_value(a->get_arg(0));
            const mpz & y = get_value(a->get_arg(1));
            int bv_sz = m_bv_util.get_bv_size(a->get_decl()->get_domain()[0]);

            if (negated) {
                if (m_mpz_manager.gt(x, y))
                    res = 1.0; 
                else {
                    mpz diff;
                    m_mpz_manager.sub(y, x, diff);
                    m_mpz_manager.inc(diff);                            
                    rational n(diff);
                    n /= rational(m_powers(bv_sz));                            
                    double dbl = n.get_double();
                    // In extreme cases, n is 0.9999 but to_double returns something > 1.0
                    res = (dbl > 1.0) ? 0.0 : (dbl < 0.0) ? 1.0 : 1.0 - dbl;
                    m_mpz_manager.del(diff);
                }
            }
            else {
                if (m_mpz_manager.le(x, y))                        
                    res = 1.0; 
                else {
                    mpz diff;
                    m_mpz_manager.sub(x, y, diff);
                    rational n(diff);
                    n /= rational(m_powers(bv_sz));
                    double dbl = n.get_double();
                    res = (dbl > 1.0) ? 0.0 : (dbl < 0.0) ? 1.0 : 1.0 - dbl;
                    m_mpz_manager.del(diff);
                }
            }
            TRACE("sls_score", tout << "x = " << m_mpz_manager.to_string(x) << " ; y = " << 
                                    m_mpz_manager.to_string(y) << " ; SZ = " << bv_sz << std::endl; );
        }
        else if (m_bv_util.is_bv_sle(n)) { // x <= y
            app * a = to_app(n);
            SASSERT(a->get_num_args() == 2);
            mpz x; m_mpz_manager.set(x, get_value(a->get_arg(0)));
            mpz y; m_mpz_manager.set(y, get_value(a->get_arg(1)));
            unsigned bv_sz = m_bv_util.get_bv_size(a->get_decl()->get_domain()[0]);
            const mpz & p = m_powers(bv_sz);
            const mpz & p_half = m_powers(bv_sz-1);
            if (x >= p_half) { m_mpz_manager.sub(x, p, x); } 
            if (y >= p_half) { m_mpz_manager.sub(y, p, y); }                 

            if (negated) {
                if (x > y)
                    res = 1.0; 
                else {
                    mpz diff;
                    m_mpz_manager.sub(y, x, diff);
                    m_mpz_manager.inc(diff);
                    rational n(diff);
                    n /= p;
                    double dbl = n.get_double();
                    res = (dbl > 1.0) ? 0.0 : (dbl < 0.0) ? 1.0 : 1.0 - dbl;
                    m_mpz_manager.del(diff);
                }
                TRACE("sls_score", tout << "x = " << m_mpz_manager.to_string(x) << " ; y = " << 
                                        m_mpz_manager.to_string(y) << " ; SZ = " << bv_sz << std::endl; );
            }
            else {
                if (x <= y)
                    res = 1.0; 
                else {
                    mpz diff;
                    m_mpz_manager.sub(x, y, diff);
                    SASSERT(!m_mpz_manager.is_neg(diff));
                    rational n(diff);
                    n /= p;
                    double dbl = n.get_double();
                    res = (dbl > 1.0) ? 0.0 : (dbl < 0.0) ? 1.0 : 1.0 - dbl;
                    m_mpz_manager.del(diff);
                }
                TRACE("sls_score", tout << "x = " << m_mpz_manager.to_string(x) << " ; y = " << 
                                        m_mpz_manager.to_string(y) << " ; SZ = " << bv_sz << std::endl; );
            }
            m_mpz_manager.del(x);
            m_mpz_manager.del(y);                
        }
        else if (m_manager.is_not(n)) {                
            SASSERT(!negated);
            app * a = to_app(n);
            SASSERT(a->get_num_args() == 1);
            expr * child = a->get_arg(0);
            // Precondition: Assertion set is in NNF.
            // Also: careful about the unsat assertion scaling further down.
            if (m_manager.is_and(child) || m_manager.is_or(child)) 
                NOT_IMPLEMENTED_YET();
            res = score_bool(child, true);
        }
        else if (m_manager.is_distinct(n)) {
            app * a = to_app(n);
            unsigned pairs = 0, distinct_pairs = 0;
            unsigned sz = a->get_num_args();
            for (unsigned i = 0; i < sz; i++) {
                for (unsigned j = i+1; j < sz; j++) {
                    // pair i/j
                    const mpz & v0 = get_value(a->get_arg(0));
                    const mpz & v1 = get_value(a->get_arg(1));
                    pairs++;
                    if (v0 != v1)
                        distinct_pairs++;
                }
            }                
            res = (distinct_pairs/(double)pairs);
            if (negated) res = 1.0 - res;
        }
        else
            NOT_IMPLEMENTED_YET();

        SASSERT(res >= 0.0 && res <= 1.0);

        app * a = to_app(n);
        family_id afid = a->get_family_id();

        if (afid == m_bv_util.get_family_id())
            if (res < 1.0) res *= m_scale_unsat;

        TRACE("sls_score", tout << "SCORE = " << res << std::endl; );
        return res;
    }
    
    double score_bv(expr * n) {
        return 0.0; // a bv-expr is always scored as 0.0; we won't use those scores.
    }

    void value2mpz(expr * n, mpz & result) {
        m_mpz_manager.set(result, m_zero);

        if (m_manager.is_bool(n)) {
            m_mpz_manager.set(result, m_manager.is_true(n) ? m_one : m_zero);
        }
        else if (m_bv_util.is_bv(n)) {
            unsigned bv_sz = m_bv_util.get_bv_size(n);
            rational q;
            if (!m_bv_util.is_numeral(n, q, bv_sz))
                NOT_IMPLEMENTED_YET();
            const mpq& temp = q.to_mpq();
            SASSERT(m_mpz_manager.is_one(temp.denominator()));
            m_mpz_manager.set(result, temp.numerator());
        }
        else
            NOT_IMPLEMENTED_YET();            
    }

    expr_ref mpz2value(sort * s, const mpz & r) {
        expr_ref res(m_manager);
        if (m_manager.is_bool(s))
            res = (m_mpz_manager.is_zero(r)) ? m_manager.mk_false() : m_manager.mk_true();
        else if (m_bv_util.is_bv_sort(s)) {
            rational rat(r);
            res = m_bv_util.mk_numeral(rat, s);
        }
        else
            NOT_IMPLEMENTED_YET();
        return res;
    }

    double score(expr * n) {
        if (m_manager.is_bool(n))
            return score_bool(n);
        else if (m_bv_util.is_bv(n))
            return score_bv(n);
        else {
            NOT_IMPLEMENTED_YET();
            return 0;
        }
    }    

    ptr_vector<func_decl> & get_constants(expr * e) {
        ptr_vector<func_decl> const & this_decls = m_constants_occ.find(e);
        unsigned sz = this_decls.size();
        for (unsigned i = 0; i < sz; i++) {
            func_decl * fd = this_decls[i];
            if (!m_temp_constants.contains(fd))
                m_temp_constants.push_back(fd);
        }
        return m_temp_constants;
    }

    ptr_vector<func_decl> & get_unsat_constants_gsat(ptr_vector<expr> const & as) {
        unsigned sz = as.size();
        if (sz == 1) {
            if (m_mpz_manager.neq(get_value(as[0]), m_one))
                return get_constants();
        }

        m_temp_constants.reset();

        for (unsigned i = 0; i < sz; i++) {
            expr * q = as[i];
            if (m_mpz_manager.eq(get_value(q), m_one))
                continue;
            ptr_vector<func_decl> const & this_decls = m_constants_occ.find(q);
            unsigned sz2 = this_decls.size();
            for (unsigned j = 0; j < sz2; j++) {
                func_decl * fd = this_decls[j];
                if (!m_temp_constants.contains(fd))
                    m_temp_constants.push_back(fd);
            }
        }
        return m_temp_constants;
    }

    ptr_vector<func_decl> & get_unsat_constants_walksat(expr * e) {
            if (!e || !m_temp_constants.empty())
                return m_temp_constants;
            ptr_vector<func_decl> const & this_decls = m_constants_occ.find(e);
            unsigned sz = this_decls.size();
            for (unsigned j = 0; j < sz; j++) {
                func_decl * fd = this_decls[j];
                if (!m_temp_constants.contains(fd))
                    m_temp_constants.push_back(fd);
            }
            return m_temp_constants;
    }

    ptr_vector<func_decl> & get_unsat_constants(ptr_vector<expr> const & as) {
        if (m_walksat)
        {
            expr * e = get_unsat_assertion(as);

            if (!e)
            {
                m_temp_constants.reset();
                return m_temp_constants;
            }

            return get_unsat_constants_walksat(e);
        }
        else
            return get_unsat_constants_gsat(as);
    }
    
    expr * get_unsat_assertion(ptr_vector<expr> const & as) {
        unsigned sz = as.size();
        if (sz == 1) {
            if (m_mpz_manager.neq(get_value(as[0]), m_one))
                return as[0];
            else
                return nullptr;
        }
        m_temp_constants.reset();

        unsigned pos = -1;
        if (m_ucb)
        {
            double max = -1.0;
            // Andreas: Commented things here might be used for track_unsat data structures as done in SLS for SAT. But seems to have no benefit.
            /* for (unsigned i = 0; i < m_where_false.size(); i++) {
                expr * e = m_list_false[i]; */
            for (unsigned i = 0; i < sz; i++) {
                expr * e = as[i];
                if (m_mpz_manager.neq(get_value(e), m_one))
                {
                    value_score & vscore = m_scores.find(e);
                    // Andreas: Select the assertion with the greatest ucb score. Potentially add some noise.
                    // double q = vscore.score + m_ucb_constant * sqrt(log((double)m_touched) / vscore.touched);
                    double q = vscore.score + m_ucb_constant * sqrt(log((double)m_touched) / vscore.touched) + m_ucb_noise * get_random_uint(8); 
                    if (q > max) { max = q; pos = i; }
                }
            }
            if (pos == static_cast<unsigned>(-1))
                return nullptr;

            m_touched++;
            m_scores.find(as[pos]).touched++;
            // Andreas: Also part of track_unsat data structures. Additionally disable the previous line!
            /* m_last_pos = pos;
            m_scores.find(m_list_false[pos]).touched++;
            return m_list_false[pos]; */
        }
        else
        {
            // Andreas: The track_unsat data structures for random assertion selection.
            /* sz = m_where_false.size();
            if (sz == 0)
                return 0;
            return m_list_false[get_random_uint(16) % sz]; */

            unsigned cnt_unsat = 0;
            for (unsigned i = 0; i < sz; i++)
                if (m_mpz_manager.neq(get_value(as[i]), m_one) && (get_random_uint(16) % ++cnt_unsat == 0)) pos = i;    
            if (pos == static_cast<unsigned>(-1))
                return nullptr;
        }
        
        m_last_pos = pos;
        return as[pos];
    }

    expr * get_new_unsat_assertion(ptr_vector<expr> const & as) {
        unsigned sz = as.size();
        if (sz == 1)
            return nullptr;
        m_temp_constants.reset();
        
        unsigned cnt_unsat = 0, pos = -1;
        for (unsigned i = 0; i < sz; i++)
            if ((i != m_last_pos) && m_mpz_manager.neq(get_value(as[i]), m_one) && (get_random_uint(16) % ++cnt_unsat == 0)) pos = i;

        if (pos == static_cast<unsigned>(-1))
            return nullptr;
        return as[pos];
    }
};

