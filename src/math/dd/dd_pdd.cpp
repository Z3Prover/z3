/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    dd_pdd.cpp

Abstract:

    Poly DD package 

Author:

    Nikolaj Bjorner (nbjorner) 2019-12-17

Revision History:

--*/

#include "util/trace.h"
#include "util/stopwatch.h"
#include "math/dd/dd_pdd.h"

namespace dd {

    pdd_manager::pdd_manager(unsigned num_vars, semantics s) {
        m_spare_entry = nullptr;
        m_max_num_nodes = 1 << 24; // up to 16M nodes
        m_mark_level = 0;
        m_dmark_level = 0;
        m_disable_gc = false;
        m_is_new_node = false;
        m_semantics = s;
        unsigned_vector l2v;
        for (unsigned i = 0; i < num_vars; ++i) l2v.push_back(i);
        init_nodes(l2v);
    }

    pdd_manager::~pdd_manager() {
        if (m_spare_entry) {
            m_alloc.deallocate(sizeof(*m_spare_entry), m_spare_entry);
            m_spare_entry = nullptr;
        }
        reset_op_cache();
    }

    void pdd_manager::reset(unsigned_vector const& level2var) {
        reset_op_cache();
        m_node_table.reset();
        m_nodes.reset();
        m_free_nodes.reset();
        m_pdd_stack.reset();
        m_values.reset();
        m_free_values.reset();
        m_mpq_table.reset();  
        init_nodes(level2var);
    }

    void pdd_manager::init_nodes(unsigned_vector const& l2v) {
        // add dummy nodes for operations, and 0, 1 pdds.
        for (unsigned i = 0; i < pdd_no_op; ++i) {
            m_nodes.push_back(node());
            m_nodes[i].m_refcount = max_rc;
            m_nodes[i].m_index = i;
        }
        init_value(rational::zero(), 0);
        init_value(rational::one(), 1);
        SASSERT(is_val(0));
        SASSERT(is_val(1));
        alloc_free_nodes(1024 + l2v.size());   
        init_vars(l2v);
    }

    void pdd_manager::init_vars(unsigned_vector const& level2var) {
        unsigned n = level2var.size();
        m_level2var.resize(n);
        m_var2level.resize(n);
        m_var2pdd.resize(n);
        for (unsigned l = 0; l < n; ++l) {
            unsigned v = level2var[l];
            m_var2pdd[v] = make_node(l, zero_pdd, one_pdd);
            m_nodes[m_var2pdd[v]].m_refcount = max_rc;
            m_var2level[v] = l;
            m_level2var[l] = v;
        }
    }

    void pdd_manager::reset_op_cache() {
        for (auto* e : m_op_cache) {
            SASSERT(e != m_spare_entry);
            m_alloc.deallocate(sizeof(*e), e);
        }
        m_op_cache.reset();
    }

    pdd pdd_manager::add(pdd const& a, pdd const& b) { return pdd(apply(a.root, b.root, pdd_add_op), this); }
    pdd pdd_manager::sub(pdd const& a, pdd const& b) { return pdd(apply(a.root, b.root, pdd_sub_op), this); }
    pdd pdd_manager::mul(pdd const& a, pdd const& b) { return pdd(apply(a.root, b.root, pdd_mul_op), this); }
    pdd pdd_manager::reduce(pdd const& a, pdd const& b) { return pdd(apply(a.root, b.root, pdd_reduce_op), this); }
    pdd pdd_manager::mk_val(rational const& r) { return pdd(imk_val(r), this); }
    pdd pdd_manager::mk_val(unsigned r) { return mk_val(rational(r)); }
    pdd pdd_manager::mul(rational const& r, pdd const& b) { pdd c(mk_val(r)); return pdd(apply(c.root, b.root, pdd_mul_op), this); }
    pdd pdd_manager::add(rational const& r, pdd const& b) { pdd c(mk_val(r)); return pdd(apply(c.root, b.root, pdd_add_op), this); }
    pdd pdd_manager::zero() { return pdd(zero_pdd, this); }
    pdd pdd_manager::one() { return pdd(one_pdd, this); }
    
    pdd pdd_manager::mk_or(pdd const& p, pdd const& q) { return p + q - (p*q); }
    pdd pdd_manager::mk_xor(pdd const& p, pdd const& q) { if (m_semantics == mod2_e) return p + q; return (p*q*2) - p - q; }
    pdd pdd_manager::mk_xor(pdd const& p, unsigned x) { pdd q(mk_val(x)); if (m_semantics == mod2_e) return p + q; return (p*q*2) - p - q; }
    pdd pdd_manager::mk_not(pdd const& p) { return 1 - p; }

    pdd pdd_manager::subst_val(pdd const& p, vector<std::pair<unsigned, rational>> const& _s) {
        typedef std::pair<unsigned, rational> pr;
        vector<pr> s(_s);        
        std::function<bool (pr const&, pr const&)> compare_level = 
            [&](pr const& a, pr const& b) { return m_var2level[a.first] < m_var2level[b.first]; };
        std::sort(s.begin(), s.end(), compare_level);
        pdd r(one());
        for (auto const& q : s) {
            r = (r*mk_var(q.first)) + q.second;            
        }
        return pdd(apply(p.root, r.root, pdd_subst_val_op), this);
    }

    pdd_manager::PDD pdd_manager::apply(PDD arg1, PDD arg2, pdd_op op) {
        bool first = true;
        SASSERT(well_formed());
        scoped_push _sp(*this);
        while (true) {
            try {
                return apply_rec(arg1, arg2, op);
            }
            catch (const mem_out &) {
                try_gc();
                if (!first) throw;
                first = false;
            }
        }
        SASSERT(well_formed());
        return null_pdd;
    }

    bool pdd_manager::check_result(op_entry*& e1, op_entry const* e2, PDD a, PDD b, PDD c) {
        if (e1 != e2) {
            SASSERT(e2->m_result != null_pdd);
            push_entry(e1);
            e1 = nullptr;
            return true;            
        }
        else {
            e1->m_pdd1 = a;
            e1->m_pdd2 = b;
            e1->m_op = c;
            SASSERT(e1->m_result == null_pdd);
            return false;        
        }
    }

    pdd_manager::PDD pdd_manager::apply_rec(PDD p, PDD q, pdd_op op) {        
        switch (op) {
        case pdd_sub_op:
            if (is_zero(q)) return p;
            if (is_val(p) && is_val(q)) return imk_val(val(p) - val(q));
            if (m_semantics != mod2_e) break;
            op = pdd_add_op;
        case pdd_add_op:
            if (is_zero(p)) return q;
            if (is_zero(q)) return p;
            if (is_val(p) && is_val(q)) return imk_val(val(p) + val(q));
            if (is_val(p)) std::swap(p, q);
            else if (!is_val(q) && level(p) < level(q)) std::swap(p, q);            
            break;
        case pdd_mul_op:
            if (is_zero(p) || is_zero(q)) return zero_pdd;
            if (is_one(p)) return q;
            if (is_one(q)) return p;
            if (is_val(p) && is_val(q)) return imk_val(val(p) * val(q));
            if (is_val(p)) std::swap(p, q);
            else if (!is_val(q) && level(p) < level(q)) std::swap(p, q);            
            break;
        case pdd_reduce_op:
            if (is_zero(q)) return p;
            if (is_val(p)) return p;
            if (degree(p) < degree(q)) return p; 
            if (level(first_leading(q)) > level(p)) return p;
            break;
        case pdd_subst_val_op:
            while (!is_val(q) && !is_val(p)) {
                if (level(p) == level(q)) break;
                if (level(p) < level(q)) q = lo(q);
                else p = lo(p);
            }
            if (is_val(p) || is_val(q)) return p;            
            break;
        default:
            UNREACHABLE();
            break;
        }

        op_entry * e1 = pop_entry(p, q, op);
        op_entry const* e2 = m_op_cache.insert_if_not_there(e1);
        if (check_result(e1, e2, p, q, op)) {
            SASSERT(!m_free_nodes.contains(e2->m_result));
            return e2->m_result;
        }
        PDD r;
        unsigned level_p = level(p), level_q = level(q);
        unsigned npop = 2;
                
        switch (op) {
        case pdd_add_op:
            SASSERT(!is_val(p));
            if (is_val(q)) {
                push(apply_rec(lo(p), q, op));
                r = make_node(level_p, read(1), hi(p));
                npop = 1;
            }
            else if (level_p == level_q) {
                push(apply_rec(lo(p), lo(q), op));
                push(apply_rec(hi(p), hi(q), op));
                r = make_node(level_p, read(2), read(1));                           
            }
            else {
                SASSERT(level_p > level_q);
                push(apply_rec(lo(p), q, op));
                r = make_node(level_p, read(1), hi(p));
                npop = 1;
            }
            break;
        case pdd_sub_op:
            if (is_val(p) || (!is_val(q) && level_p < level_q)) {
                // p - (ax + b) = -ax + (p - b)
                push(apply_rec(p, lo(q), op));
                push(minus_rec(hi(q)));
                r = make_node(level_q, read(2), read(1));
            }
            else if (is_val(q) || (level_p > level_q)) {
                // (ax + b) - k = ax + (b - k)
                push(apply_rec(lo(p), q, op));
                r = make_node(level_p, read(1), hi(p));
                npop = 1;
            }
            else {
                SASSERT(level_p == level_q);
                // (ax + b) - (cx + d) = (a - c)x + (b - d)
                push(apply_rec(lo(p), lo(q), op));
                push(apply_rec(hi(p), hi(q), op));
                r = make_node(level_p, read(2), read(1));                           
            }
            break;
        case pdd_mul_op:
            SASSERT(!is_val(p));
            if (is_val(q)) {
                push(apply_rec(lo(p), q, op));
                push(apply_rec(hi(p), q, op));
                r = make_node(level_p, read(2), read(1));
            }
            else if (level_p == level_q) {
                if (m_semantics != free_e) {
                    //
                    // (xa+b)*(xc+d)  == x(ac+bc+ad) + bd
                    //                == x((a+b)(c+d)-bd) + bd
                    // because x*x = x
                    //
                    push(apply_rec(lo(p), lo(q), pdd_mul_op));
                    unsigned bd = read(1);
                    push(apply_rec(hi(p), lo(p), pdd_add_op));
                    push(apply_rec(hi(q), lo(q), pdd_add_op));
                    push(apply_rec(read(1), read(2), pdd_mul_op));
                    push(apply_rec(read(1), bd, pdd_sub_op));
                    r = make_node(level_p, bd, read(1));
                    npop = 5;
                }
                else {
                    /*
                      In this case the code should have checked if level(read(1)) == level_a,
                      Then it should have converted read(1) into e := hi(read(1)), f := lo(read(1)),                    
                      Such that read(1) stands for x*e+f.                      
                      The task is then to create the term:                      
                      x*(x*ac + x*e + f) + bd, which is the same as: x*(x*(ac + e) + f) + bd
                    */

                    push(apply_rec(hi(p), hi(q), op));
                    push(apply_rec(hi(p), lo(q), op));
                    push(apply_rec(lo(p), hi(q), op));
                    push(apply_rec(lo(p), lo(q), op));
                    unsigned ac = read(4), ad = read(3), bc = read(2), bd = read(1);
                    push(apply_rec(ad, bc, pdd_add_op));
                    unsigned n = read(1); // n = ad + bc
                    if (!is_val(n) && level(n) == level_p) {
                        push(apply_rec(ac, hi(n), pdd_add_op));
                        push(make_node(level_p, lo(n), read(1)));
                        r = make_node(level_p, bd, read(1));
                        npop = 7;
                    } else {
                        push(make_node(level_p, n, ac));
                        r = make_node(level_p, bd, read(1));
                        npop = 6;
                    }                         
                }
            }
            else {
                // (x*hi(p)+lo(p))*b = x*hi(p)*b + lo(p)*b
                SASSERT(level_p > level_q);
                push(apply_rec(lo(p), q, op));
                push(apply_rec(hi(p), q, op));
                r = make_node(level_p, read(2), read(1));
            }
            break;
        case pdd_reduce_op:
            if (level(first_leading(q)) < level_p) {
                push(apply_rec(lo(p), q, op));
                push(apply_rec(hi(p), q, op));
                PDD plo = read(2), phi = read(1);
                if (plo == lo(p) && phi == hi(p)) {
                    r = p;
                }
                else if (level(plo) < level_p && level(phi) <= level(p)) {
                    r = make_node(level_p, plo, phi);
                }
                else {
                    push(apply_rec(phi,     m_var2pdd[var(p)], pdd_mul_op));
                    push(apply_rec(read(1), plo, pdd_add_op));
                    r = read(1);
                    npop = 4;
                }                
            }
            else {
                SASSERT(level(first_leading(q)) == level_p);
                r = reduce_on_match(p, q);
                npop = 0;
            }
            break;
        case pdd_subst_val_op:
            SASSERT(!is_val(p));
            SASSERT(!is_val(q));
            SASSERT(level_p = level_q);
            push(apply_rec(lo(p), hi(q), pdd_subst_val_op));   // lo := subst(lo(p), s)
            push(apply_rec(hi(p), hi(q), pdd_subst_val_op));   // hi := subst(hi(p), s)
            push(apply_rec(lo(q), read(1), pdd_mul_op));       // hi := hi*s[var(p)]
            r = apply_rec(read(1), read(3), pdd_add_op);       // r := hi + lo := subst(lo(p),s) + s[var(p)]*subst(hi(p),s)
            npop = 3;
            break;
        default:
            r = null_pdd;
            UNREACHABLE();
            break;
        }
        pop(npop);
        e1->m_result = r;        
        SASSERT(!m_free_nodes.contains(r));
        return r;
    }

    pdd pdd_manager::minus(pdd const& a) {
        if (m_semantics == mod2_e) {
            return a;
        }
        bool first = true;
        SASSERT(well_formed());
        scoped_push _sp(*this);
        while (true) {
            try {
                return pdd(minus_rec(a.root), this);
            }
            catch (const mem_out &) {
                try_gc();
                if (!first) throw;
                first = false;
            }
        }
        SASSERT(well_formed());        
        return pdd(zero_pdd, this);
    }

    pdd_manager::PDD pdd_manager::minus_rec(PDD a) {
        SASSERT(m_semantics != mod2_e);
        if (is_zero(a)) return zero_pdd;
        if (is_val(a)) return imk_val(-val(a));
        op_entry* e1 = pop_entry(a, a, pdd_minus_op);
        op_entry const* e2 = m_op_cache.insert_if_not_there(e1);
        if (check_result(e1, e2, a, a, pdd_minus_op)) 
            return e2->m_result;
        push(minus_rec(lo(a)));
        push(minus_rec(hi(a)));
        PDD r = make_node(level(a), read(2), read(1));
        pop(2);
        e1->m_result = r;
        return r;
    }

    //
    // produce polynomial where a is reduced by b.
    // all monomials in a that are divisible by lm(b)
    // are replaced by (b - lt(b))/lm(b)
    //
    pdd_manager::PDD pdd_manager::reduce_on_match(PDD a, PDD b) {
        SASSERT(level(first_leading(b)) == level(a));
        SASSERT(!is_val(a) && !is_val(b));
        push(a);
        while (lm_occurs(b, a)) {           
            push(lt_quotient(b, a));
            push(apply_rec(read(1), b, pdd_mul_op));
            push(apply_rec(a, read(1), pdd_add_op));
            a = read(1);
            pop(4);
            push(a);
        }
        pop(1);
        return a;
    }

    // true if leading monomial of p divides a monomial of q
    bool pdd_manager::lm_occurs(PDD p, PDD q) const {
        p = first_leading(p);
        while (true) {
            if (is_val(p)) return true;
            if (is_val(q)) return false;
            if (level(p) > level(q)) {
                return false;
            }
            else if (level(p) == level(q)) {
                p = next_leading(p);
                q = hi(q);
            }
            else if (lm_occurs(p, hi(q))) {
                return true;
            }
            else {
                q = lo(q);
            }
        }
    }

    // return minus quotient -r, such that lt(p)*r
    // is a monomial in q.
    // assume lm_occurs(p, q)
    pdd_manager::PDD pdd_manager::lt_quotient(PDD p, PDD q) {
        SASSERT(lm_occurs(p, q));
        p = first_leading(p);
        SASSERT(is_val(p) || !is_val(q));

        while (!is_val(p)) {
            SASSERT(level(p) <= level(q));
            SASSERT(lm_occurs(p, q));
            if (level(p) == level(q)) {
                p = next_leading(p);
                q = lm_occurs(p, hi(q)) ? hi(q) : lo(q);
            }
            else if (lm_occurs(p, hi(q))) {
                return lt_quotient_hi(p, q);
            }
            else {            
                q = lo(q);
            }
        }
        SASSERT(!is_zero(p));
        if (is_val(q)) {
            return imk_val(-val(q) / val(p));
        }
        else {
            return lt_quotient_hi(p, q);
        }                               
    }

    pdd_manager::PDD pdd_manager::lt_quotient_hi(PDD p, PDD q) {
        SASSERT(lm_occurs(p, hi(q)));
        push(lt_quotient(p, hi(q)));
        PDD r = apply_rec(m_var2pdd[var(q)], read(1), pdd_mul_op);
        pop(1);
        return r;  
    }

    //
    // p = lcm(lm(a),lm(b))/lm(a), q = lcm(lm(a),lm(b))/lm(b)
    // pc = coeff(lt(a)) qc = coeff(lt(b))
    // compute a*q*qc - b*p*pc
    //
    bool pdd_manager::try_spoly(pdd const& a, pdd const& b, pdd& r) {
        return common_factors(a, b, m_p, m_q, m_pc, m_qc) && (r = spoly(a, b, m_p, m_q, m_pc, m_qc), true);
    }

    pdd pdd_manager::spoly(pdd const& a, pdd const& b, unsigned_vector const& p, unsigned_vector const& q, rational const& pc, rational const& qc) { 
        pdd r1 = mk_val(qc);  
        for (unsigned i = q.size(); i-- > 0; ) r1 *= mk_var(q[i]);
        pdd r2 = mk_val(-pc);
        for (unsigned i = p.size(); i-- > 0; ) r2 *= mk_var(p[i]);
        return (r1*a) + (r2*b);
    }

    bool pdd_manager::common_factors(pdd const& a, pdd const& b, unsigned_vector& p, unsigned_vector& q, rational& pc, rational& qc) { 
        p.reset(); q.reset(); 
        PDD x = first_leading(a.root), y = first_leading(b.root);
        bool has_common = false;
        while (true) {
            if (is_val(x) || is_val(y)) {
                if (!has_common) return false;
                while (!is_val(y)) q.push_back(var(y)), y = next_leading(y);
                while (!is_val(x)) p.push_back(var(x)), x = next_leading(x);
                pc = val(x);
                qc = val(y);
                if (m_semantics != mod2_e && pc.is_int() && qc.is_int()) {
                    rational g = gcd(pc, qc);
                    pc /= g;
                    qc /= g;
                }
                return true;
            }
            if (level(x) == level(y)) {
                has_common = true;
                x = next_leading(x);
                y = next_leading(y);
            }
            else if (level(x) > level(y)) {
                p.push_back(var(x));
                x = next_leading(x);
            }
            else {
                q.push_back(var(y));
                y = next_leading(y);
            }
        }
    }

    /*.
     * compare pdds based on leading monomials
     */
    bool pdd_manager::lex_lt(pdd const& a, pdd const& b) {
        PDD x = a.root;
        PDD y = b.root;
        if (x == y) return false;
        while (true) {
            SASSERT(x != y);
            if (is_val(x)) 
                return !is_val(y) || val(x) < val(y);
            if (is_val(y)) 
                return false;
            if (level(x) == level(y)) {
                if (hi(x) == hi(y)) {
                    x = lo(x);
                    y = lo(y);
                }
                else {
                    x = hi(x);
                    y = hi(y);
                }
            }
            else {
                return level(x) > level(y);
            }
        }
    }

    bool pdd_manager::lm_lt(pdd const& a, pdd const& b) {
        PDD x = first_leading(a.root);
        PDD y = first_leading(b.root);
        while (true) {
            if (x == y) break;
            if (is_val(x) && is_val(y)) break;
            if (is_val(x)) return true;
            if (is_val(y)) return false;
            if (level(x) == level(y)) {
                x = next_leading(x);
                y = next_leading(y);
            }
            else {
                return level(x) < level(y);
            }
        }
        vector<unsigned_vector> ma, mb;
        for (auto const& m : a) {
            ma.push_back(m.vars);
        }
        for (auto const& m : b) {
            mb.push_back(m.vars);
        }
        std::function<bool (unsigned_vector const& a, unsigned_vector const& b)> degree_lex_gt = 
            [this](unsigned_vector const& a, unsigned_vector const& b) {
            unsigned i = 0;
            if (a.size() > b.size()) return true;
            if (a.size() < b.size()) return false;
            for (; i < a.size() && a[i] == b[i]; ++i) {};
            return i < a.size() && m_var2level[a[i]] > m_var2level[b[i]];
        };
        std::sort(ma.begin(), ma.end(), degree_lex_gt);
        std::sort(mb.begin(), mb.end(), degree_lex_gt);
        auto ita = ma.begin();
        auto itb = mb.begin();
        for (; ita != ma.end() && itb != mb.end(); ++ita, ++itb) {
            if (degree_lex_gt(*itb, *ita)) return true;
            if (degree_lex_gt(*ita, *itb)) return false;
        }
        return ita == ma.end() && itb != mb.end();
    }

    /**
       Compare leading terms of pdds
     */
    bool pdd_manager::different_leading_term(pdd const& a, pdd const& b) {
        PDD x = first_leading(a.root);
        PDD y = first_leading(b.root);
        while (true) {
            if (x == y) return false;
            if (is_val(x) || is_val(y)) return true;
            if (level(x) == level(y)) {
                x = next_leading(x);
                y = next_leading(y);
            }
            else {
                return true;
            }
        }
    }

    /**
     * The assumption is that var(p) is part of the leading monomial.
     * Then the next leading monomial that uses var(p) has to be under hi(p)
     * because lo(p) does not use var(p).
     */
    pdd_manager::PDD pdd_manager::next_leading(PDD p) const {
        SASSERT(!is_val(p));
        return first_leading(hi(p));
    }

    /**
     * The first node that contains a term from the leading monomial
     * is a node of highest degree and highest variable.
     * Thus, when the degree of hi(p) + 1 is not dominated by degree of lo(p).
     */
    pdd_manager::PDD pdd_manager::first_leading(PDD p) const {
        while (!is_val(p) && degree(hi(p)) + 1 < degree(lo(p))) {
            p = lo(p);
        }
        return p;
    }

    bool pdd_manager::is_linear(pdd const& p) { 
        return is_linear(p.root); 
    }

    /*
      Determine whether p is a binary polynomials 
      of the form v1, x*v1 + v2, or x*v1 + y*v2 + v3
      where v1, v2 are values.      
     */
    bool pdd_manager::is_binary(PDD p) {
        return is_val(p) || (is_val(hi(p)) && (is_val(lo(p)) || (is_val(hi(lo(p))) && is_val(lo(lo(p))))));
    }

    bool pdd_manager::is_binary(pdd const& p) { 
        return is_binary(p.root); 
    }

    /**
       Determine if p is a monomial.
    */
    bool pdd_manager::is_monomial(PDD p) {
        while (true) {
            if (is_val(p)) return true;
            if (!is_zero(lo(p))) return false;
            p = hi(p);
        }
    }

    /*
      \brief determine if v occurs as a leaf variable.
     */
    bool pdd_manager::var_is_leaf(PDD p, unsigned v) {
        init_mark();
        m_todo.push_back(p);
        while (!m_todo.empty()) {
            PDD r = m_todo.back();
            m_todo.pop_back();
            if (is_val(r) || is_marked(r)) continue;
            set_mark(r);
            if (var(r) == v) {
                if (!is_val(lo(r)) || !is_val(hi(r))) {
                    m_todo.reset();
                    return false;
                }
                continue;
            }
            if (!is_marked(lo(r))) m_todo.push_back(lo(r));
            if (!is_marked(hi(r))) m_todo.push_back(hi(r));
        }
        return true;
    }

    void pdd_manager::push(PDD b) {
        m_pdd_stack.push_back(b);
    }

    void pdd_manager::pop(unsigned num_scopes) {
        m_pdd_stack.shrink(m_pdd_stack.size() - num_scopes);
    }

    pdd_manager::PDD pdd_manager::read(unsigned index) {
        return m_pdd_stack[m_pdd_stack.size() - index];
    }

    pdd_manager::op_entry* pdd_manager::pop_entry(PDD l, PDD r, PDD op) {
        op_entry* result = nullptr;
        if (m_spare_entry) {
            result = m_spare_entry;
            m_spare_entry = nullptr;
            result->m_pdd1 = l;
            result->m_pdd2 = r;
            result->m_op = op;
        }
        else {
            void * mem = m_alloc.allocate(sizeof(op_entry));
            result = new (mem) op_entry(l, r, op);
        }
        result->m_result = null_pdd;
        return result;
    }

    void pdd_manager::push_entry(op_entry* e) {
        SASSERT(!m_spare_entry);
        m_spare_entry = e;
    }

    pdd_manager::PDD pdd_manager::imk_val(rational const& r) {
        if (r.is_zero()) return zero_pdd;
        if (r.is_one()) return one_pdd;
        if (m_semantics == mod2_e) return imk_val(mod(r, rational(2)));
        const_info info;
        if (!m_mpq_table.find(r, info)) {
            init_value(info, r);
        }      
        return info.m_node_index;
    }

    void pdd_manager::init_value(const_info& info, rational const& r) {
        unsigned vi = 0;
        if (m_free_values.empty()) {
            vi = m_values.size();
            m_values.push_back(r);
        }
        else {
            vi = m_free_values.back();
            m_free_values.pop_back();
            m_values[vi] = r;
        }

        m_freeze_value = r;
        node n(vi);
        info.m_value_index = vi;        
        info.m_node_index = insert_node(n);
        m_mpq_table.insert(r, info);
    }

    void pdd_manager::init_value(rational const& v, unsigned node_index) {
        const_info info;
        m_nodes[node_index].m_hi = 0;
        m_nodes[node_index].m_lo = node_index;
        info.m_value_index = m_values.size();
        info.m_node_index = node_index;
        m_mpq_table.insert(v, info);
        m_values.push_back(v);
    }

    pdd_manager::PDD pdd_manager::make_node(unsigned lvl, PDD l, PDD h) {
        m_is_new_node = false;
        if (is_zero(h)) return l;
        SASSERT(is_val(l) || level(l) < lvl);
        SASSERT(is_val(h) || level(h) <= lvl);
        node n(lvl, l, h);
        return insert_node(n);
    }

    pdd_manager::PDD pdd_manager::insert_node(node const& n) {
        node_table::entry* e = m_node_table.insert_if_not_there2(n);
        if (e->get_data().m_index != 0) {
            unsigned result = e->get_data().m_index;
            SASSERT(well_formed(e->get_data()));
            return result;
        }
        e->get_data().m_refcount = 0;
        bool do_gc = m_free_nodes.empty();
        if (do_gc && !m_disable_gc) {
            gc();
            e = m_node_table.insert_if_not_there2(n);
            e->get_data().m_refcount = 0;      
        }
        if (do_gc) {
            if (m_nodes.size() > m_max_num_nodes) {
                throw mem_out();
            }
            alloc_free_nodes(m_nodes.size()/2);
        }
        SASSERT(e->get_data().m_lo == n.m_lo);
        SASSERT(e->get_data().m_hi == n.m_hi);
        SASSERT(e->get_data().m_level == n.m_level);
        SASSERT(!m_free_nodes.empty());
        unsigned result = m_free_nodes.back();
        m_free_nodes.pop_back();
        e->get_data().m_index = result;
        m_nodes[result] = e->get_data();
        SASSERT(well_formed(m_nodes[result]));
        m_is_new_node = true;        
        SASSERT(!m_free_nodes.contains(result));
        SASSERT(m_nodes[result].m_index == result); 
        return result;
    }

    void pdd_manager::try_gc() {
        gc();        
        reset_op_cache();
        SASSERT(m_op_cache.empty());
        SASSERT(well_formed());
    }

    void pdd_manager::reserve_var(unsigned i) {
        while (m_var2level.size() <= i) {
            unsigned v = m_var2level.size();
            m_var2pdd.push_back(make_node(v, zero_pdd, one_pdd));
            m_nodes[m_var2pdd[v]].m_refcount = max_rc;
            m_var2level.push_back(v);
            m_level2var.push_back(v);
        }
    }

    pdd pdd_manager::mk_var(unsigned i) {
        reserve_var(i);
        return pdd(m_var2pdd[i], this);        
    }
    
    unsigned pdd_manager::dag_size(pdd const& b) {
        init_mark();
        set_mark(0);
        set_mark(1);
        unsigned sz = 0;
        m_todo.push_back(b.root);
        while (!m_todo.empty()) {
            PDD r = m_todo.back();
            m_todo.pop_back();
            if (is_marked(r)) {
                continue;
            }
            ++sz;
            set_mark(r);
            if (is_val(r)) {
                continue;
            }
            if (!is_marked(lo(r))) {
                m_todo.push_back(lo(r));
            }
            if (!is_marked(hi(r))) {
                m_todo.push_back(hi(r));
            }
        }
        return sz;
    }

    void pdd_manager::init_dmark() {
        m_dmark.resize(m_nodes.size());
        m_degree.reserve(m_nodes.size());
        ++m_dmark_level;
        if (m_dmark_level == 0) {
            m_dmark.fill(0);
            ++m_dmark_level;
        }
    }

    unsigned pdd_manager::degree(pdd const& b) const {
        return degree(b.root);
    }

    unsigned pdd_manager::degree(PDD p) const {
        if (p == zero_pdd || p == one_pdd) {
            return 0;
        }
        if (is_dmarked(p)) {
            return m_degree[p];
        }        
        m_todo.push_back(p);
        while (!m_todo.empty()) {
            PDD r = m_todo.back();
            if (is_dmarked(r)) {
                m_todo.pop_back();
            }
            else if (is_val(r)) {
                m_degree[r] = 0;
                set_dmark(r);
            }
            else if (!is_dmarked(lo(r)) || !is_dmarked(hi(r))) {
                m_todo.push_back(lo(r));
                m_todo.push_back(hi(r));
            }
            else {
                m_degree[r] = std::max(m_degree[lo(r)], m_degree[hi(r)]+1); 
                set_dmark(r);
            }
        }
        return m_degree[p];
    }


    double pdd_manager::tree_size(pdd const& p) {
        init_mark();
        m_tree_size.reserve(m_nodes.size());
        m_todo.push_back(p.root);
        while (!m_todo.empty()) {
            PDD r = m_todo.back();
            if (is_marked(r)) {
                m_todo.pop_back();
            }
            else if (is_val(r)) {
                m_tree_size[r] = 1;
                set_mark(r);
            }
            else if (!is_marked(lo(r)) || !is_marked(hi(r))) {
                m_todo.push_back(lo(r));
                m_todo.push_back(hi(r));
            }
            else {
                m_tree_size[r] = 1 + m_tree_size[lo(r)] + m_tree_size[hi(r)]; 
                set_mark(r);
            }
        }
        return m_tree_size[p.root];
    }

    unsigned_vector const& pdd_manager::free_vars(pdd const& p) { 
        init_mark();
        m_free_vars.reset();
        m_todo.push_back(p.root);
        while (!m_todo.empty()) {
            PDD r = m_todo.back();
            m_todo.pop_back();
            if (is_val(r) || is_marked(r)) continue;
            PDD v = m_var2pdd[var(r)];
            if (!is_marked(v)) m_free_vars.push_back(var(r));
            set_mark(r);
            set_mark(v);
            if (!is_marked(lo(r))) m_todo.push_back(lo(r));
            if (!is_marked(hi(r))) m_todo.push_back(hi(r));
        }
        return m_free_vars;
    }

    void pdd_manager::alloc_free_nodes(unsigned n) {
        for (unsigned i = 0; i < n; ++i) {
            m_free_nodes.push_back(m_nodes.size());
            m_nodes.push_back(node());
            m_nodes.back().m_index = m_nodes.size() - 1;
        }        
        std::sort(m_free_nodes.begin(), m_free_nodes.end());
        m_free_nodes.reverse();
        init_dmark();
    }

    bool pdd_manager::is_reachable(PDD p) {
        svector<bool> reachable(m_nodes.size(), false);
        compute_reachable(reachable);
        return reachable[p];
    }

    void pdd_manager::compute_reachable(svector<bool>& reachable) {
        for (unsigned i = m_pdd_stack.size(); i-- > 0; ) {
            reachable[m_pdd_stack[i]] = true;
            m_todo.push_back(m_pdd_stack[i]);
        }
        for (unsigned i = pdd_no_op; i-- > 0; ) {
            reachable[i] = true;
        }
        for (unsigned i = m_nodes.size(); i-- > pdd_no_op; ) {
            if (m_nodes[i].m_refcount > 0) {
                reachable[i] = true;
                m_todo.push_back(i);
            }
        }
        while (!m_todo.empty()) {
            PDD p = m_todo.back();
            m_todo.pop_back();
            SASSERT(reachable[p]);
            if (is_val(p)) { 
                continue;
            }
            if (!reachable[lo(p)]) {
                reachable[lo(p)] = true;
                m_todo.push_back(lo(p));
            }
            if (!reachable[hi(p)]) {
                reachable[hi(p)] = true;
                m_todo.push_back(hi(p));
            }
        }
    }

    void pdd_manager::gc() {
        init_dmark();
        m_free_nodes.reset();
        SASSERT(well_formed());
        IF_VERBOSE(13, verbose_stream() << "(pdd :gc " << m_nodes.size() << ")\n";);
        svector<bool> reachable(m_nodes.size(), false);
        compute_reachable(reachable);
        for (unsigned i = m_nodes.size(); i-- > pdd_no_op; ) {
            if (!reachable[i]) {
                if (is_val(i)) {
                    if (m_freeze_value == val(i)) continue;
                    m_free_values.push_back(m_mpq_table.find(val(i)).m_value_index);
                    m_mpq_table.remove(val(i));  
                }
                m_nodes[i].set_internal();
                SASSERT(m_nodes[i].m_refcount == 0);
                m_free_nodes.push_back(i);       
            }
        }
        // sort free nodes so that adjacent nodes are picked in order of use
        std::sort(m_free_nodes.begin(), m_free_nodes.end());
        m_free_nodes.reverse();

        ptr_vector<op_entry> to_delete, to_keep;
        for (auto* e : m_op_cache) {            
            if (e->m_result != null_pdd) {
                to_delete.push_back(e);
            }
            else {
                to_keep.push_back(e);
            }
        }
        m_op_cache.reset();
        for (op_entry* e : to_delete) {
            m_alloc.deallocate(sizeof(*e), e);
        }
        for (op_entry* e : to_keep) {
            m_op_cache.insert(e);
        }

        m_node_table.reset();
        // re-populate node cache
        for (unsigned i = m_nodes.size(); i-- > 2; ) {
            if (reachable[i]) {
                SASSERT(m_nodes[i].m_index == i);
                m_node_table.insert(m_nodes[i]);
            }
        }
        SASSERT(well_formed());
    }

    void pdd_manager::init_mark() {
        m_mark.resize(m_nodes.size());
        ++m_mark_level;
        if (m_mark_level == 0) {
            m_mark.fill(0);
            ++m_mark_level;
        }
    }

    pdd_manager::monomials_t pdd_manager::to_monomials(pdd const& p) {
        if (p.is_val()) {
            std::pair<rational, unsigned_vector> m;
            m.first = p.val();
            monomials_t mons;
            if (!m.first.is_zero()) {
                mons.push_back(m);
            }
            return mons;
        }
        else {
            monomials_t mons = to_monomials(p.hi());
            for (auto & m : mons) {
                m.second.push_back(p.var());
            }
            mons.append(to_monomials(p.lo()));
            return mons;
        }
    }

    std::ostream& pdd_manager::display(std::ostream& out, pdd const& b) {
        auto mons = to_monomials(b);
        bool first = true;
        for (auto& m : mons) {
            if (!first) {
                if (m.first.is_neg()) out << " - ";
                else out << " + ";
            }
            else {
                if (m.first.is_neg()) out << "- ";
            }
            first = false;
            rational c = abs(m.first);
            m.second.reverse();
            if (!c.is_one() || m.second.empty()) {
                out << c;
                if (!m.second.empty()) out << "*";
            }
            bool f = true;
            for (unsigned v : m.second) {
                if (!f) out << "*";
                f = false;
                out << "v" << v;
            }
        }
        if (first) out << "0";
        return out;
    }

    bool pdd_manager::well_formed() {
        bool ok = true;
        for (unsigned n : m_free_nodes) {
            ok &= (lo(n) == 0 && hi(n) == 0 && m_nodes[n].m_refcount == 0);
            if (!ok) {
                IF_VERBOSE(0, 
                           verbose_stream() << "free node is not internal " << n << " " 
                           << lo(n) << " " << hi(n) << " " << m_nodes[n].m_refcount << "\n";
                           display(verbose_stream()););
                UNREACHABLE();
                return false;
            }
        }
        for (node const& n : m_nodes) {
            if (!well_formed(n)) {
                IF_VERBOSE(0, display(verbose_stream() << n.m_index << " lo " << n.m_lo << " hi " << n.m_hi << "\n"););
                UNREACHABLE();
                return false;
            }
        }
        return ok;
    }

    bool pdd_manager::well_formed(node const& n) {
        PDD lo = n.m_lo;
        PDD hi = n.m_hi;        
        if (n.is_internal() || hi == 0) return true;
        bool oklo = is_val(lo) || (level(lo) < n.m_level  && !m_nodes[lo].is_internal());
        bool okhi = is_val(hi) || (level(hi) <= n.m_level && !m_nodes[hi].is_internal());
        return oklo && okhi;
    }

    std::ostream& pdd_manager::display(std::ostream& out) {
        for (unsigned i = 0; i < m_nodes.size(); ++i) {
            node const& n = m_nodes[i];
            if (i != 0 && n.is_internal()) {
                continue;
            }
            else if (is_val(i)) {
                out << i << " : " << val(i) << "\n";
            }
            else {
                out << i << " : v" << m_level2var[n.m_level] << " " << n.m_lo << " " << n.m_hi << "\n";
            }
        }
        return out;
    }

    pdd& pdd::operator=(pdd const& other) { 
        unsigned r1 = root; 
        root = other.root; 
        m.inc_ref(root); 
        m.dec_ref(r1); 
        return *this; 
    }

    std::ostream& operator<<(std::ostream& out, pdd const& b) { return b.display(out); }

    void pdd_iterator::next() {
        auto& m = m_pdd.m;
        while (!m_nodes.empty()) {
            auto& p = m_nodes.back();
            if (p.first && !m.is_val(p.second)) {
                p.first = false;
                m_mono.vars.pop_back();
                unsigned n = m.lo(p.second);
                if (m.is_val(n) && m.val(n).is_zero()) {
                    m_nodes.pop_back();
                    continue;
                }
                while (!m.is_val(n)) {
                    m_nodes.push_back(std::make_pair(true, n));
                    m_mono.vars.push_back(m.var(n));
                    n = m.hi(n);
                }
                m_mono.coeff = m.val(n);
                break;
            }
            else {
                m_nodes.pop_back();
            }
        }
    }

    void pdd_iterator::first() {
        unsigned n = m_pdd.root;
        auto& m = m_pdd.m;
        while (!m.is_val(n)) {
            m_nodes.push_back(std::make_pair(true, n));
            m_mono.vars.push_back(m.var(n));
            n = m.hi(n);
        }
        m_mono.coeff = m.val(n);
    }

    pdd_iterator pdd::begin() const { return pdd_iterator(*this, true); }
    pdd_iterator pdd::end() const { return pdd_iterator(*this, false); }

    std::ostream& operator<<(std::ostream& out, pdd_monomial const& m) {
        if (!m.coeff.is_one()) {
            out << m.coeff;
            if (!m.vars.empty()) out << "*";
        }
        bool first = true;
        for (auto v : m.vars) {
            if (first) first = false; else out << "*";
            out << "v" << v;
        }
        return out;
    }


}
