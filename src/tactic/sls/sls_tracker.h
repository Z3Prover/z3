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

#ifndef _SLS_TRACKER_H_
#define _SLS_TRACKER_H_

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
        value_score() : m(0), value(unsynch_mpz_manager::mk_z(0)), score(0.0), distance(0) { };
        ~value_score() { if (m) m->del(value); }
        unsynch_mpz_manager * m;
        mpz value;
        double score;
        unsigned distance; // max distance from any root
        value_score & operator=(const value_score & other) {
            SASSERT(m == 0 || m == other.m);
            if (m) m->set(value, 0); else m = other.m;
            m->set(value, other.value);
            score = other.score;
            distance = other.distance;
            return *this;
        }
    };

public:
    typedef obj_map<func_decl, expr* > entry_point_type;

private:
    typedef obj_map<expr, value_score> scores_type;    
    typedef obj_map<expr, ptr_vector<expr> > uplinks_type;    
    typedef obj_map<expr, ptr_vector<func_decl> > occ_type;
    scores_type           m_scores;
    uplinks_type          m_uplinks;
    entry_point_type      m_entry_points;
    ptr_vector<func_decl> m_constants;
    ptr_vector<func_decl> m_temp_constants;
    occ_type              m_constants_occ;

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

    inline ptr_vector<expr> & get_uplinks(expr * n) {
        SASSERT(m_uplinks.contains(n));
        return m_uplinks.find(n);
    }

    void initialize(app * n) {
        // Build score table
        if (!m_scores.contains(n)) {
            value_score vs;
            vs.m = & m_mpz_manager;
            m_scores.insert(n, vs);
        }

        // Update uplinks
        unsigned na = n->get_num_args();
        for (unsigned i = 0; i < na; i++) {
            expr * c = n->get_arg(i); 
            uplinks_type::obj_map_entry * entry = m_uplinks.insert_if_not_there2(c, ptr_vector<expr>());
            entry->get_data().m_value.push_back(n);
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

    void calculate_expr_distances(goal_ref const & g) {
        // precondition: m_scores is set up.
        unsigned sz = g->size();
        ptr_vector<app> stack;
        for (unsigned i = 0; i < sz; i++)
            stack.push_back(to_app(g->form(i)));
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

    void initialize(goal_ref const & g) {
        init_proc proc(m_manager, *this);
        expr_mark visited;
        unsigned sz = g->size();
        for (unsigned i = 0; i < sz; i++) {
            expr * e = g->form(i);                
            for_each_expr(proc, visited, e);
        }

        visited.reset();

        for (unsigned i = 0; i < sz; i++) {
            expr * e = g->form(i);
            ptr_vector<func_decl> t;
            m_constants_occ.insert_if_not_there(e, t);
            find_func_decls_proc ffd_proc(m_manager, m_constants_occ.find(e));
            expr_fast_mark1 visited;
            quick_for_each_expr(ffd_proc, visited, e);
        }

        calculate_expr_distances(g);

        TRACE("sls", tout << "Initial model:" << std::endl; show_model(tout); );
    }

    void show_model(std::ostream & out) {
        unsigned sz = get_num_constants();
        for (unsigned i = 0; i < sz; i++) {
            func_decl * fd = get_constant(i);
            out << fd->get_name() << " = " << m_mpz_manager.to_string(get_value(fd)) << std::endl;
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
            return get_random_bool();
        else
            NOT_IMPLEMENTED_YET(); // This only works for bit-vectors for now.
    }    

    void randomize() {
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

#define _SCORE_AND_MIN

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
            #ifdef _SCORE_AND_MIN
            double min = 1.0;
            for (unsigned i = 0; i < a->get_num_args(); i++) {
                double cur = get_score(args[i]);
                if (cur < min) min = cur;
            }
            res = min;
            #else 
            double sum = 0.0;
            for (unsigned i = 0; i < a->get_num_args(); i++)
                sum += get_score(args[i]);
            res = sum / (double) a->get_num_args();
            #endif
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
                #if 1 // unweighted hamming distance
                while (!m_mpz_manager.is_zero(diff)) {
                    //m_mpz_manager.set(diff_m1, diff);
                    //m_mpz_manager.dec(diff_m1);
                    //m_mpz_manager.bitwise_and(diff, diff_m1, diff);
                    //hamming_distance++;
                    if (!m_mpz_manager.is_even(diff)) {
                        hamming_distance++;
                    }
                    m_mpz_manager.machine_div(diff, m_two, diff);
                }
                res = 1.0 - (hamming_distance / (double) bv_sz);                    
                #else                    
                rational r(diff);
                r /= m_powers(bv_sz);
                double dbl = r.get_double();
                res = (dbl < 0.0) ? 1.0 : (dbl > 1.0) ? 0.0 : 1.0 - dbl;
                #endif
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
            unsigned bv_sz = m_bv_util.get_bv_size(a->get_decl()->get_domain()[0]);

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
                    res = (dbl > 1.0) ? 1.0 : (dbl < 0.0) ? 0.0 : dbl;
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
                    rational n(diff);
                    n /= p;
                    double dbl = n.get_double();
                    res = (dbl > 1.0) ? 1.0 : (dbl < 0.0) ? 0.0 : dbl;
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
            if (m_manager.is_and(child) || m_manager.is_or(child)) // Precondition: Assertion set is in NNF.
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
            mpq temp = q.to_mpq();
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
        else
            NOT_IMPLEMENTED_YET();
    }    

    ptr_vector<func_decl> & get_unsat_constants(goal_ref const & g) {
        unsigned sz = g->size();

        if (sz == 1) {
            return get_constants();
        }
        else {
            m_temp_constants.reset();
            for (unsigned i = 0; i < sz; i++) {
                expr * q = g->form(i);
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
    }
};

#endif