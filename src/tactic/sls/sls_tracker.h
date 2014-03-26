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

#include"bv_decl_plugin.h"
#include"model.h"

#include"sls_compilation_settings.h"
#include"sls_powers.h"

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
#if _EARLY_PRUNE_
        value_score() : m(0), value(unsynch_mpz_manager::mk_z(0)), score(0.0), distance(0), touched(1), score_prune(0.0), has_pos_occ(0), has_neg_occ(0) { };
#else
        value_score() : m(0), value(unsynch_mpz_manager::mk_z(0)), score(0.0), distance(0), touched(1) { };
#endif
        ~value_score() { if (m) m->del(value); }
        unsynch_mpz_manager * m;
        mpz value;
        double score;
#if _EARLY_PRUNE_
        double score_prune;
        unsigned has_pos_occ;
        unsigned has_neg_occ;
#endif
        unsigned distance; // max distance from any root
        unsigned touched;
        value_score & operator=(const value_score & other) {
            SASSERT(m == 0 || m == other.m);
            if (m) m->set(value, 0); else m = other.m;
            m->set(value, other.value);
            score = other.score;
            distance = other.distance;
            touched = other.touched;
            return *this;
        }
    };

public:
    typedef obj_map<func_decl, expr* > entry_point_type;

private:
    typedef obj_map<expr, value_score> scores_type;    
    typedef obj_map<expr, ptr_vector<expr> > uplinks_type;    
    typedef obj_map<expr, ptr_vector<func_decl> > occ_type;
    obj_hashtable<expr>	  m_top_expr;
    scores_type           m_scores;
    uplinks_type          m_uplinks;
    entry_point_type      m_entry_points;
    ptr_vector<func_decl> m_constants;
    ptr_vector<func_decl> m_temp_constants;
    occ_type              m_constants_occ;
#if _UCT_
    unsigned              m_touched;
#endif
#if _REAL_RS_ || _REAL_PBFS_
    ptr_vector<expr>	  m_unsat_expr;
    obj_map<expr, unsigned>	m_where_false;
    expr**					m_list_false;
#endif
#if _CACHE_TOP_SCORE_
    double				  m_top_sum;
#endif
#if _WEIGHT_DIST_ == 4 || _WEIGHT_TOGGLE_
    double				  m_weight_dist_factor;
#endif

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

#if _WEIGHT_DIST_ == 4 || _WEIGHT_TOGGLE_
    inline void set_weight_dist_factor(double val) {
        m_weight_dist_factor = val;
    }
#endif

#if _CACHE_TOP_SCORE_
    inline void adapt_top_sum(double add, double sub) {
        m_top_sum += add - sub;
    }

    inline void set_top_sum(double new_score) {
        m_top_sum = new_score;
    }

    inline double get_top_sum() {
        return m_top_sum;
    }
#endif

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

#if _EARLY_PRUNE_
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
#endif

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

#if _REAL_RS_ || _REAL_PBFS_
    void debug_real(goal_ref const & g, unsigned flip)
    {
        unsigned count = 0;
        for (unsigned i = 0; i < g->size(); i++)
        {
            expr * e = g->form(i);
            if (m_mpz_manager.eq(get_value(e),m_one) && m_where_false.contains(e))
            {
                printf("iteration %d: ", flip);
                printf("form %d is sat but in unsat list at position %d of %d\n", i, m_where_false.find(e), m_where_false.size());
                exit(4);
            }

            if (m_mpz_manager.eq(get_value(e),m_zero) && !m_where_false.contains(e))
            {
                printf("iteration %d: ", flip);
                printf("form %d is unsat but not in unsat list\n", i);
                exit(4);
            }

            if (m_mpz_manager.eq(get_value(e),m_zero) && m_where_false.contains(e))
            {
                unsigned pos = m_where_false.find(e);
                expr * q = m_list_false[pos];
                if (q != e)
                {
                    printf("iteration %d: ", flip);
                    printf("form %d is supposed to be at pos %d in unsat list but something else was there\n", i, pos);
                    exit(4);
                }
            }

            if (m_mpz_manager.eq(get_value(e),m_zero))
                count++;
        }

        // should be true now that duplicate assertions are removed
        if (count != m_where_false.size())
        {
                printf("iteration %d: ", flip);
                printf("%d are unsat but list is of size %d\n", count, m_where_false.size());
                exit(4);
        }
    }
#endif

    void uct_forget(goal_ref const & g) {
        expr * e;
        unsigned touched_old, touched_new;

        for (unsigned i = 0; i < g->size(); i++)
        {
            e = g->form(i);
            touched_old = m_scores.find(e).touched;
            touched_new = (unsigned)((touched_old - 1) * _UCT_FORGET_FACTOR_ + 1);
            m_scores.find(e).touched = touched_new;
            m_touched += touched_new - touched_old;
        }
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
    }

    void initialize(ptr_vector<expr> const & as) {
        init_proc proc(m_manager, *this);
        expr_mark visited;
        unsigned sz = as.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * e = as[i];
            if (!m_top_expr.contains(e))
                m_top_expr.insert(e);
            else
                printf("this is already in ...\n");
            // Andreas: Maybe not fully correct.
#if _FOCUS_ == 2
            initialize_recursive(proc, visited, e);
#endif
            for_each_expr(proc, visited, e);
        }

        visited.reset();

        for (unsigned i = 0; i < sz; i++) {
            expr * e = as[i];
            // Andreas: Maybe not fully correct.
#if _FOCUS_ == 2 || _INTENSIFICATION_
            initialize_recursive(e);
#endif
            ptr_vector<func_decl> t;
            m_constants_occ.insert_if_not_there(e, t);
            find_func_decls_proc ffd_proc(m_manager, m_constants_occ.find(e));
            expr_fast_mark1 visited;
            quick_for_each_expr(ffd_proc, visited, e);
        }

        calculate_expr_distances(as);

        TRACE("sls", tout << "Initial model:" << std::endl; show_model(tout); );

#if _REAL_RS_ || _REAL_PBFS_
        m_list_false = new expr*[sz];
        //for (unsigned i = 0; i < sz; i++)
        //{
        //	if (m_mpz_manager.eq(get_value(g->form(i)),m_zero))
        //		break_assertion(g->form(i));
        //}
#endif

#if _EARLY_PRUNE_
        for (unsigned i = 0; i < sz; i++)
            setup_occs(as[i]);
#endif

#if _UCT_
        m_touched = _UCT_INIT_ ? as.size() : 1;
#endif
    }

#if _REAL_RS_ || _REAL_PBFS_
    void make_assertion(expr * e)
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
                //printf("Moving %d from %d to %d\n", q, m_where_false.size(), pos);
            }
            //else
                //printf("Erasing %d from %d to %d\n", e, pos);
//			m_list_false[m_where_false.size()] = 0;
//			printf("Going in %d\n", m_where_false.size());
        }
        //if (m_unsat_expr.contains(e))
            //m_unsat_expr.erase(e);
    }

    void break_assertion(expr * e)
    {
        //printf("I'm broken... that's still fine.\n");
        if (!m_where_false.contains(e))
        {
            //printf("This however is not so cool...\n");
            unsigned pos = m_where_false.size();
            m_list_false[pos] = e;
            m_where_false.insert(e, pos);
    //		printf("Going in %d\n", m_where_false.size());
        }
        //if (!m_unsat_expr.contains(e))
            //m_unsat_expr.push_back(e);
    }
#endif

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

#if _UCT_RESET_
        m_touched = _UCT_INIT_ ? as.size() : 1;
        for (unsigned i = 0; i < as.size(); i++)
            m_scores.find(as[i]).touched = 1;
#endif
    }              

    void reset(ptr_vector<expr> const & as) {
        TRACE("sls", tout << "Abandoned model:" << std::endl; show_model(tout); );

        for (entry_point_type::iterator it = m_entry_points.begin(); it != m_entry_points.end(); it++) {
            mpz temp = m_zero;
            set_value(it->m_value, temp);
            m_mpz_manager.del(temp);
        }

#if _UCT_RESET_
        m_touched = _UCT_INIT_ ? as.size() : 1;
        for (unsigned i = 0; i < as.size(); i++)
            m_scores.find(as[i]).touched = 1;
#endif
    }              

#if _EARLY_PRUNE_
    void setup_occs(expr * n, bool negated = false) {
        if (m_manager.is_bool(n))
        {
            if (m_manager.is_and(n) || m_manager.is_or(n))
            {
                SASSERT(!negated);
                app * a = to_app(n);
                expr * const * args = a->get_args();
                for (unsigned i = 0; i < a->get_num_args(); i++)
                    setup_occs(args[i]);
            }
            else if (m_manager.is_not(n))
            {
                SASSERT(!negated);
                app * a = to_app(n);
                SASSERT(a->get_num_args() == 1);
                expr * child = a->get_arg(0);
                if (m_manager.is_and(child) || m_manager.is_or(child))
                    NOT_IMPLEMENTED_YET();
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
        else
            NOT_IMPLEMENTED_YET();
    }
#endif

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
            // Andreas: Seems to have no effect. Probably it does not even occur.
#if _SCORE_AND_AVG_
            double sum = 0.0;
            for (unsigned i = 0; i < a->get_num_args(); i++)
#if _DIRTY_UP_
                sum += is_top_expr(args[i]) ? 1.0 : get_score(args[i]);
#else
                sum += get_score(args[i]);
#endif
            res = sum / (double) a->get_num_args();
#else
            double min = 1.0;
            for (unsigned i = 0; i < a->get_num_args(); i++) {
#if _DIRTY_UP_
                double cur = is_top_expr(args[i]) ? 1.0 : get_score(args[i]);
#else
                double cur = get_score(args[i]);
#endif
                if (cur < min) min = cur;
            }
            res = min;
#endif
        }
        else if (m_manager.is_or(n)) {
            SASSERT(!negated);
            app * a = to_app(n);
            expr * const * args = a->get_args();
            // Andreas: Seems to have no effect. Probably it is still too similar to the original version.
#if _SCORE_OR_MUL_
            double inv = 1.0;
            for (unsigned i = 0; i < a->get_num_args(); i++) {
#if _DIRTY_UP_
                double cur = is_top_expr(args[i]) ? 1.0 : get_score(args[i]);
#else
                double cur = get_score(args[i]);
#endif
                inv *= (1.0 - get_score(args[i]));
            }
            res = 1.0 - inv;
#else
            double max = 0.0;
            for (unsigned i = 0; i < a->get_num_args(); i++) {
#if _DIRTY_UP_
                double cur = is_top_expr(args[i]) ? 1.0 : get_score(args[i]);
#else
                double cur = get_score(args[i]);
#endif
                if (cur > max) max = cur;
            }
            res = max;
#endif
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
#if _DIRTY_UP_
            res = is_top_expr(child) ? 0.0 : score_bool(child, true);
#else
            res = score_bool(child, true);
#endif
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

#if _WEIGHT_DIST_
        app * a = to_app(n);
        family_id afid = a->get_family_id();

        if (afid == m_bv_util.get_family_id())
#endif
#if _WEIGHT_DIST_ == 1
#if _WEIGHT_TOGGLE_
        if (res < 1.0) res *= m_weight_dist_factor;
#else
        if (res < 1.0) res *= _WEIGHT_DIST_FACTOR_;
#endif
#elif _WEIGHT_DIST_ == 2
        res *= res;
#elif _WEIGHT_DIST_ == 3
        if (res < 1.0) res = 0.0;
#elif _WEIGHT_DIST_ == 4
        if (res < 1.0) res *= m_weight_dist_factor;
#endif

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

    expr * get_unsat_expression(expr * e) {
        if (m_manager.is_bool(e)) {
            if (m_manager.is_and(e) || m_manager.is_or(e)) {
                app * a = to_app(e);
                expr * const * args = a->get_args();
                // Andreas: might be used for guided branching
                //for (unsigned i = 0; i < a->get_num_args(); i++) {
                    //double cur = get_score(args[i]);
                //}
                // Andreas: A random number is better here since reusing flip will cause patterns.
                unsigned int sz = a->get_num_args();
                unsigned int pos = get_random_uint(16) % sz;
                for (unsigned int i = pos; i < sz; i++) {
                    expr * q = args[i];
                    if (m_mpz_manager.neq(get_value(q), m_one))
                        return get_unsat_expression(q);
                }
                for (unsigned int i = 0; i < pos; i++) {
                    expr * q = args[i];
                    if (m_mpz_manager.neq(get_value(q), m_one))
                        return get_unsat_expression(q);
                }
            }
        }
        return e;
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

    ptr_vector<func_decl> & get_unsat_constants_gsat(ptr_vector<expr> const & as, unsigned sz) {
        if (sz == 1)
            return get_constants();
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

    expr * get_unsat_assertion(ptr_vector<expr> const & as, unsigned sz, unsigned int pos) {
            for (unsigned i = pos; i < sz; i++) {
                expr * q = as[i];
                if (m_mpz_manager.neq(get_value(q), m_one))
                    return q;
            }
            for (unsigned i = 0; i < pos; i++) {
                expr * q = as[i];
                if (m_mpz_manager.neq(get_value(q), m_one))
                    return q;
            }
            return 0;
    }

    ptr_vector<func_decl> & get_unsat_constants_walksat(ptr_vector<expr> const & as, unsigned sz, unsigned int pos) {
            expr * q = get_unsat_assertion(as, sz, pos);
            // Andreas: I should probably fix this. If this is the case then the formula is SAT anyway but this is not checked in the first iteration.
            if (!q)
                return m_temp_constants;
            ptr_vector<func_decl> const & this_decls = m_constants_occ.find(q);
            unsigned sz2 = this_decls.size();
            for (unsigned j = 0; j < sz2; j++) {
                func_decl * fd = this_decls[j];
                if (!m_temp_constants.contains(fd))
                    m_temp_constants.push_back(fd);
            }
            return m_temp_constants;
    }

    ptr_vector<func_decl> & get_unsat_constants_walksat(expr * e) {
            if (!e || m_temp_constants.size())
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

    ptr_vector<func_decl> & go_deeper(expr * e) {
            if (m_manager.is_bool(e)) {
                if (m_manager.is_and(e)) {
                    app * a = to_app(e);
                    expr * const * args = a->get_args();
                    // Andreas: might be used for guided branching
                    //for (unsigned i = 0; i < a->get_num_args(); i++) {
                        //double cur = get_score(args[i]);
                    //}
                    // Andreas: A random number is better here since reusing flip will cause patterns.
                    unsigned int sz = a->get_num_args();
                    unsigned int pos = get_random_uint(16) % sz;
                    for (unsigned int i = pos; i < sz; i++) {
                        expr * q = args[i];
                        if (m_mpz_manager.neq(get_value(q), m_one))
                            return go_deeper(q);
                    }
                    for (unsigned int i = 0; i < pos; i++) {
                        expr * q = args[i];
                        if (m_mpz_manager.neq(get_value(q), m_one))
                            return go_deeper(q);
                    }
                }
                else if (m_manager.is_or(e)) {
                    app * a = to_app(e);
                    expr * const * args = a->get_args();
                    unsigned int sz = a->get_num_args();
                    unsigned int pos = get_random_uint(16) % sz;
                    for (unsigned int i = pos; i < sz; i++) {
                        expr * q = args[i];
                        if (m_mpz_manager.neq(get_value(q), m_one))
                            return go_deeper(q);
                    }
                    for (unsigned int i = 0; i < pos; i++) {
                        expr * q = args[i];
                        if (m_mpz_manager.neq(get_value(q), m_one))
                            return go_deeper(q);
                    }
                }
            }
            ptr_vector<func_decl> const & this_decls = m_constants_occ.find(e);
            unsigned sz2 = this_decls.size();
            for (unsigned j = 0; j < sz2; j++) {
                func_decl * fd = this_decls[j];
                if (!m_temp_constants.contains(fd))
                    m_temp_constants.push_back(fd);
            }
            return m_temp_constants;
    }

    ptr_vector<func_decl> & get_unsat_constants_crsat(ptr_vector<expr> const & as, unsigned sz, unsigned int pos) {
        expr * q = get_unsat_assertion(as, sz, pos);
        if (!q)
            return m_temp_constants;

        return go_deeper(q);
    }

    ptr_vector<func_decl> & get_unsat_constants(ptr_vector<expr> const & as, unsigned int flip) {
        unsigned sz = as.size();

        if (sz == 1) {
            if (m_mpz_manager.eq(get_value(as[0]), m_one))
                return m_temp_constants;
            else
                return get_constants();
        }
        else {
            m_temp_constants.reset();
#if _FOCUS_ == 1
#if _UCT_
            unsigned pos = -1;
            value_score vscore;
#if _PROBABILISTIC_UCT_
            double sum_score = 0.0;
            unsigned start_index = get_random_uint(16) % sz;

            for (unsigned i = start_index; i < sz; i++)
            {
                expr * e = g->form(i);
                vscore = m_scores.find(e);

#if _PROBABILISTIC_UCT_ == 2
                double q = vscore.score * vscore.score; 
#else
                double q = vscore.score + _UCT_CONSTANT_ * sqrt(log(m_touched)/vscore.touched) + _UCT_EPS_; 
#endif
                if (m_mpz_manager.neq(get_value(g->form(i)), m_one)) {
                    sum_score += q;
                    if (rand() <= (q * RAND_MAX / sum_score) + 1)
                        pos = i;
                }	
            }
            for (unsigned i = 0; i < start_index; i++)
            {
                expr * e = g->form(i);
                vscore = m_scores.find(e);
#if _PROBABILISTIC_UCT_ == 2
                double q = vscore.score * vscore.score; 
#else
                double q = vscore.score + _UCT_CONSTANT_ * sqrt(log(m_touched)/vscore.touched) + _UCT_EPS_; 
#endif
                if (m_mpz_manager.neq(get_value(g->form(i)), m_one)) {
                    sum_score += q;
                    if (rand() <= (q * RAND_MAX / sum_score) + 1)
                        pos = i;
                }	
            }
#else
            double max = -1.0;
            for (unsigned i = 0; i < sz; i++) {
                expr * e = as[i];
//            for (unsigned i = 0; i < m_where_false.size(); i++) {
//                expr * e = m_list_false[i];
                vscore = m_scores.find(e);
#if _UCT_ == 1
                double q = vscore.score + _UCT_CONSTANT_ * sqrt(log((double)m_touched)/vscore.touched); 
#elif _UCT_ == 2
                double q = vscore.score + (_UCT_CONSTANT_ * (flip - vscore.touched)) / sz; 
#elif _UCT_ == 3
                double q = vscore.score + _UCT_CONSTANT_ * sqrt(log(m_touched)/vscore.touched) + (get_random_uint(16) * 0.1 / (2<<16)); 
#endif
                if (q > max && m_mpz_manager.neq(get_value(e), m_one) ) { max = q; pos = i; }
            }
#endif
            if (pos == static_cast<unsigned>(-1))
                return m_temp_constants;

#if _UCT_ == 1 || _UCT_ == 3
            m_scores.find(as[pos]).touched++;
            m_touched++;
#elif _UCT_ == 2
            m_scores.find(as[pos]).touched = flip; 
#endif
            expr * e = as[pos];
//            expr * e = m_list_false[pos];

#elif _BFS_ == 3
            unsigned int pos = -1;
            double max = -1.0;
            for (unsigned i = 0; i < sz; i++) {
                expr * e = g->form(i);
                double q = get_score(e);
                if (q > max && m_mpz_manager.neq(get_value(e), m_one) ) { max = q; pos = i; }
            }
            if (pos == static_cast<unsigned>(-1))
                return m_temp_constants;
            expr * e = g->form(pos);
#elif _BFS_ == 2
            unsigned int pos = -1;
            double min = 2.0;
            for (unsigned i = 0; i < sz; i++) {
                expr * e = g->form(i);
                double q = get_score(e);
                if (q < min && m_mpz_manager.neq(get_value(e), m_one) ) { min = q; pos = i; }
            }
            if (pos == static_cast<unsigned>(-1))
                return m_temp_constants;
            expr * e = g->form(pos);
#elif _BFS_ == 1
            // I guess it was buggy ...
            // unsigned int pos = flip % m_constants.size();
            unsigned int pos = flip % sz;
            expr * e = get_unsat_assertion(g, sz, pos);
#elif _UNIFORM_RANDOM_
            unsigned cnt_unsat = 0, pos = -1;
            for (unsigned i = 0; i < sz; i++)
                if (m_mpz_manager.neq(get_value(g->form(i)), m_one) && (get_random_uint(16) % ++cnt_unsat == 0)) pos = i;	
            if (pos == static_cast<unsigned>(-1))
                return m_temp_constants;
            expr * e = g->form(pos);
#elif _REAL_RS_
            //unsigned pos = m_false_list[get_random_uint(16) % m_cnt_false];
            //expr * e = get_unsat_assertion(g, sz, pos);
            //expr * e = m_unsat_expr[get_random_uint(16) % m_unsat_expr.size()];
            sz = m_where_false.size();
            if (sz == 0)
                return m_temp_constants;
            expr * e = m_list_false[get_random_uint(16) % sz];
#elif _REAL_PBFS_
            //unsigned pos = m_false_list[flip % m_cnt_false];
            //expr * e = get_unsat_assertion(g, sz, pos);
            //expr * e = m_unsat_expr[flip % m_unsat_expr.size()];
            sz = m_where_false.size();
            if (sz == 0)
                return m_temp_constants;
            else
                expr * e = m_list_false[flip % sz];
#else
            // I guess it was buggy ...
            // unsigned int pos = get_random_uint(16) % m_constants.size();
            unsigned int pos = get_random_uint(16) % sz;
            expr * e = get_unsat_assertion(g, sz, pos);
#endif
            return get_unsat_constants_walksat(e);
#elif _FOCUS_ == 2
#if _BFS_
            // I guess it was buggy ...
            // unsigned int pos = flip % m_constants.size();
            unsigned int pos = flip % sz;
#else
            // I guess it was buggy ...
            // unsigned int pos = get_random_uint(16) % m_constants.size();
            unsigned int pos = get_random_uint(16) % sz;
#endif
            return get_unsat_constants_crsat(g, sz, pos);
#else
            return get_unsat_constants_gsat(g, sz);
#endif
        }
    }
    

    expr * get_unsat_assertion(ptr_vector<expr> const & as, unsigned int flip) {
        unsigned sz = as.size();

        if (sz == 1)
            return as[0];

        m_temp_constants.reset();
#if _FOCUS_ == 1
#if _UCT_
        unsigned pos = -1;
        value_score vscore;
#if _PROBABILISTIC_UCT_
        double sum_score = 0.0;
        unsigned start_index = get_random_uint(16) % sz;
            
        for (unsigned i = start_index; i < sz; i++)
        {
            expr * e = g->form(i);
            vscore = m_scores.find(e);
#if _PROBABILISTIC_UCT_ == 2
            double q = vscore.score * vscore.score + _UCT_EPS_; 
#else
            double q = vscore.score + _UCT_CONSTANT_ * sqrt(log(m_touched)/vscore.touched) + _UCT_EPS_; 
#endif
            if (m_mpz_manager.neq(get_value(g->form(i)), m_one)) {
                sum_score += q;
                if (rand() <= (q * RAND_MAX / sum_score) + 1)
                    pos = i;
            }	
        }
        for (unsigned i = 0; i < start_index; i++)
        {
            expr * e = g->form(i);
            vscore = m_scores.find(e);
#if _PROBABILISTIC_UCT_ == 2
            double q = vscore.score * vscore.score + _UCT_EPS_; 
#else
            double q = vscore.score + _UCT_CONSTANT_ * sqrt(log(m_touched)/vscore.touched) + _UCT_EPS_; 
#endif
            if (m_mpz_manager.neq(get_value(g->form(i)), m_one)) {
                sum_score += q;
                if (rand() <= (q * RAND_MAX / sum_score) + 1)
                    pos = i;
            }	
        }
#else
        double max = -1.0;
            for (unsigned i = 0; i < sz; i++) {
                expr * e = as[i];
//            for (unsigned i = 0; i < m_where_false.size(); i++) {
//                expr * e = m_list_false[i];
                vscore = m_scores.find(e);
#if _UCT_ == 1
                double q = vscore.score + _UCT_CONSTANT_ * sqrt(log((double)m_touched) / vscore.touched);
#elif _UCT_ == 2
            double q = vscore.score + (_UCT_CONSTANT_ * (flip - vscore.touched)) / sz; 
#elif _UCT_ == 3
            double q = vscore.score + _UCT_CONSTANT_ * sqrt(log(m_touched)/vscore.touched) + (get_random_uint(16) * 0.1 / (2<<16)); 
#endif
            if (q > max && m_mpz_manager.neq(get_value(e), m_one) ) { max = q; pos = i; }
            }
#endif
        if (pos == static_cast<unsigned>(-1))
            return 0;

#if _UCT_ == 1 || _UCT_ == 3
        m_scores.find(as[pos]).touched++;
        m_touched++;
#elif _UCT_ == 2
        m_scores.find(g->form(pos)).touched = flip; 
#endif
//        return m_list_false[pos];
        return as[pos];

#elif _BFS_ == 3
        unsigned int pos = -1;
        double max = -1.0;
        for (unsigned i = 0; i < sz; i++) {
            expr * e = g->form(i);
               double q = get_score(e);
            if (q > max && m_mpz_manager.neq(get_value(e), m_one) ) { max = q; pos = i; }
        if (pos == static_cast<unsigned>(-1))
            return 0;
        return g->form(pos);
#elif _BFS_ == 2
        unsigned int pos = -1;
        double min = 2.0;
        for (unsigned i = 0; i < sz; i++) {
            expr * e = g->form(i);
               double q = get_score(e);
            if (q < min && m_mpz_manager.neq(get_value(e), m_one) ) { min = q; pos = i; }
        }
        if (pos == static_cast<unsigned>(-1))
            return 0;
        return g->form(pos);
#elif _BFS_ == 1
        unsigned int pos = flip % sz;
        return get_unsat_assertion(g, sz, pos);
#elif _UNIFORM_RANDOM_
        unsigned cnt_unsat = 0, pos = -1;
        for (unsigned i = 0; i < sz; i++)
            if (m_mpz_manager.neq(get_value(g->form(i)), m_one) && (get_random_uint(16) % ++cnt_unsat == 0)) pos = i;	
        if (pos == static_cast<unsigned>(-1))
            return 0;
        return g->form(pos);
#elif _REAL_RS_
        //unsigned pos = m_false_list[get_random_uint(16) % m_cnt_false];
        //expr * e = get_unsat_assertion(g, sz, pos);
        //expr * e = m_unsat_expr[get_random_uint(16) % m_unsat_expr.size()];
        sz = m_where_false.size();
        if (sz == 0)
            return 0;
        return m_list_false[get_random_uint(16) % sz];
#elif _REAL_PBFS_
        //unsigned pos = m_false_list[flip % m_cnt_false];
        //expr * e = get_unsat_assertion(g, sz, pos);
        //expr * e = m_unsat_expr[flip % m_unsat_expr.size()];
        sz = m_where_false.size();
        if (sz == 0)
            return0;
        else
            return m_list_false[flip % sz];
#else
        unsigned int pos = get_random_uint(16) % sz;
        return get_unsat_assertion(g, sz, pos);
#endif
        return as[pos];
#elif _FOCUS_ == 2
#if _BFS_
        unsigned int pos = flip % sz;
#else
        unsigned int pos = get_random_uint(16) % sz;
#endif
        return get_unsat_constants_crsat(g, sz, pos);
#endif
    }
};

#endif