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

    pdd_manager::pdd_manager(unsigned num_vars, semantics s, unsigned power_of_2) {
        m_spare_entry = nullptr;
        m_max_num_nodes = 1 << 24; // up to 16M nodes
        m_mark_level = 0;
        m_dmark_level = 0;
        m_disable_gc = false;
        m_is_new_node = false;
        if (s == mod2N_e && power_of_2 == 1)
            s = mod2_e;
        m_semantics = s;
        m_mod2N = rational::power_of_two(power_of_2);
        m_max_value = m_mod2N - 1;
        m_power_of_2 = power_of_2;
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
        m_factor_cache.reset();
        m_node_table.reset();
        m_nodes.reset();
        m_free_nodes.reset();
        m_pdd_stack.reset();
        m_values.reset();
        m_free_values.reset();
        m_mpq_table.reset();  
        init_nodes(level2var);
    }

    void pdd_manager::set_max_num_nodes(unsigned n) {        
        m_max_num_nodes = n + m_level2var.size();
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

    // NOTE: bit-wise AND cannot be expressed in mod2N_e semantics with the existing operations.
    pdd pdd_manager::mk_and(pdd const& p, pdd const& q) {
        VERIFY(m_semantics == mod2_e || m_semantics == zero_one_vars_e);
        return p * q;
    }

    pdd pdd_manager::mk_or(pdd const& p, pdd const& q) {
        return p + q - mk_and(p, q);
    }

    pdd pdd_manager::mk_xor(pdd const& p, pdd const& q) {
        if (m_semantics == mod2_e)
            return p + q;
        return p + q - 2*mk_and(p, q);
    }

    pdd pdd_manager::mk_xor(pdd const& p, unsigned x) { 
        pdd q(mk_val(x)); 
        return mk_xor(p, q); 
    }

    pdd pdd_manager::mk_not(pdd const& p) {
        if (m_semantics == mod2N_e)
            return -p - 1;
        VERIFY(m_semantics == mod2_e || m_semantics == zero_one_vars_e);
        return 1 - p;
    }

    pdd pdd_manager::subst_val(pdd const& p, unsigned v, rational const& val) {
        pdd r = mk_var(v) + val;
        return pdd(apply(p.root, r.root, pdd_subst_val_op), this);
    }


    /**
     * A polynomial is non-zero if the constant coefficient
     * is a power of two such that none of the coefficients to
     * non-constant monomials divide it.
     * Example: 2^4*x + 2 is non-zero for every x.
     */

    bool pdd_manager::is_never_zero(PDD p) {
        if (is_val(p))
            return !is_zero(p);
        if (m_semantics != mod2N_e)
            return false;
        PDD q = p;
        while (!is_val(q))
            q = lo(q);
        auto const& v = val(q);
        if (v.is_zero())
            return false;
        unsigned p2 = v.trailing_zeros();
        init_mark();
        SASSERT(m_todo.empty());
        m_todo.push_back(hi(p));
        while (!is_val(lo(p))) {
            p = lo(p);
            m_todo.push_back(hi(p));
        }
        while (!m_todo.empty()) {
            PDD r = m_todo.back();
            m_todo.pop_back();
            if (is_marked(r)) 
                continue;
            set_mark(r);
            if (!is_val(r)) {
                m_todo.push_back(lo(r));
                m_todo.push_back(hi(r));
            }
            else if (val(r).trailing_zeros() <= p2) {
                m_todo.reset();
                return false;
            }
        }
        return true;
    }

    unsigned pdd_manager::min_parity(PDD p) {
        if (m_semantics != mod2N_e)
            return 0;

        if (is_val(p))
            return val(p).parity(m_power_of_2);
        init_mark();
        PDD q = p;
        m_todo.push_back(hi(q));
        while (!is_val(q)) {
            q = lo(q);
            m_todo.push_back(hi(q));
        }
        unsigned parity = val(q).parity(m_power_of_2);
        init_mark();
        while (parity != 0 && !m_todo.empty()) {
            PDD r = m_todo.back();
            m_todo.pop_back();
            if (is_marked(r))
                continue;
            set_mark(r);
            if (!is_val(r)) {
                m_todo.push_back(lo(r));
                m_todo.push_back(hi(r));
            }
            else if (val(r).is_zero())
                continue;
            else
                parity = std::min(parity, val(r).trailing_zeros());
        }
        m_todo.reset();
        return parity;
    }

    pdd pdd_manager::subst_val(pdd const& p, pdd const& s) {
        return pdd(apply(p.root, s.root, pdd_subst_val_op), this);
    }

    pdd pdd_manager::subst_val0(pdd const& p, vector<std::pair<unsigned, rational>> const& _s) {
        typedef std::pair<unsigned, rational> pr;
        vector<pr> s(_s);        
        std::function<bool (pr const&, pr const&)> compare_level = 
            [&](pr const& a, pr const& b) { return m_var2level[a.first] < m_var2level[b.first]; };
        std::sort(s.begin(), s.end(), compare_level);
        pdd r(one());
        for (auto const& q : s) 
            r = (r * mk_var(q.first)) + q.second;
        return subst_val(p, r);
    }

    pdd pdd_manager::subst_add(pdd const& s, unsigned v, rational const& val) {
        pdd v_val = mk_var(v) + val;
        return pdd(apply(s.root, v_val.root, pdd_subst_add_op), this);
    }

    bool pdd_manager::subst_get(pdd const& s, unsigned v, rational& out_val) {
        unsigned level_v = m_var2level[v];
        PDD p = s.root;
        while (/* !is_val(p) && */ level(p) > level_v) {
            SASSERT(is_val(lo(p)));
            p = hi(p);
        }
        if (!is_val(p) && level(p) == level_v) {
            out_val = val(lo(p));
            return true;
        }
        return false;
    }

    pdd_manager::PDD pdd_manager::apply(PDD arg1, PDD arg2, pdd_op op) {
        unsigned count = 0;
        SASSERT(well_formed());
        scoped_push _sp(*this);
        while (true) {
            try {
                return apply_rec(arg1, arg2, op);
            }
            catch (const mem_out &) {
                try_gc();
                if (count > 0)
                    m_max_num_nodes *= 2;
                count++;
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
            Z3_fallthrough;
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
                if (level(p) < level(q)) q = hi(q);
                else break;
            }
            if (is_val(p) || is_val(q)) return p;            
            break;
        case pdd_subst_add_op:
            if (is_one(p)) return q;
            SASSERT(!is_val(p));
            SASSERT(!is_val(q));
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
                if (m_semantics != free_e && m_semantics != mod2N_e) {
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
                    } 
                    else {
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
            SASSERT(level_p >= level_q);
            push(apply_rec(lo(p), q, pdd_subst_val_op));   // lo := subst(lo(p), s)
            push(apply_rec(hi(p), q, pdd_subst_val_op));   // hi := subst(hi(p), s)

            if (level_p > level_q) {
                r = make_node(level_p, read(2), read(1));
                npop = 2;
            }
            else {
                push(apply_rec(lo(q), read(1), pdd_mul_op));       // hi := hi*s[var(p)]
                r = apply_rec(read(1), read(3), pdd_add_op);       // r := hi + lo := subst(lo(p),s) + s[var(p)]*subst(hi(p),s)
                npop = 3;
            }
            break;
        case pdd_subst_add_op:
            SASSERT(!is_val(p));
            SASSERT(!is_val(q));
            SASSERT(level_p != level_q);
            if (level_p < level_q) {
                r = make_node(level_q, lo(q), p);                 // p*hi(q) + lo(q)
                npop = 0;
            }
            else {
                push(apply_rec(hi(p), q, pdd_subst_add_op));       // hi := add_subst(hi(p), q)
                r = make_node(level_p, lo(p), read(1));            // r := hi*var(p) + lo(p)
                npop = 1;
            }
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
        unsigned count = 0;
        SASSERT(well_formed());
        scoped_push _sp(*this);
        while (true) {
            try {
                return pdd(minus_rec(a.root), this);
            }
            catch (const mem_out &) {
                try_gc();
                if (count > 0)
                    m_max_num_nodes *= 2;
                ++count;                
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

    /**
     * Divide PDD by a constant value.
     *
     * IMPORTANT: Performs regular numerical division.
     * For semantics 'mod2N_e', this means that 'c' must be an integer
     * and all coefficients of 'a' must be divisible by 'c'.
     *
     * NOTE: Why do we not just use 'mul(a, inv(c))' instead?
     * In case of semantics 'mod2N_e', an invariant is that all PDDs have integer coefficients.
     * But such a multiplication would create nodes with non-integral coefficients.
     */
    pdd pdd_manager::div(pdd const& a, rational const& c) {
        pdd res(zero_pdd, this);
        VERIFY(try_div(a, c, res));
        return res;
    }

    bool pdd_manager::try_div(pdd const& a, rational const& c, pdd& out_result) {
        if (m_semantics == free_e) {
            // Don't cache separately for the free semantics;
            // use 'mul' so we can share results for a/c and a*(1/c).
            out_result = mul(inv(c), a);
            return true;
        }
        SASSERT(c.is_int());
        unsigned count = 0;
        SASSERT(well_formed());
        scoped_push _sp(*this);
        while (true) {
            try {
                PDD res = div_rec(a.root, c, null_pdd);
                if (res != null_pdd)
                    out_result = pdd(res, this);
                SASSERT(well_formed());
                return res != null_pdd;
            }
            catch (const mem_out &) {
                try_gc();
                if (count > 0)
                    m_max_num_nodes *= 2;
                ++count;
            }
        }
    }

    /// Returns null_pdd if one of the coefficients is not divisible by c.
    pdd_manager::PDD pdd_manager::div_rec(PDD a, rational const& c, PDD c_pdd) {
        SASSERT(m_semantics != free_e);
        SASSERT(c.is_int());
        if (is_zero(a))
            return zero_pdd;
        if (is_val(a)) {
            rational r = val(a) / c;
            if (r.is_int())
                return imk_val(r);
            else
                return null_pdd;
        }
        if (c_pdd == null_pdd)
            c_pdd = imk_val(c);
        op_entry* e1 = pop_entry(a, c_pdd, pdd_div_const_op);
        op_entry const* e2 = m_op_cache.insert_if_not_there(e1);
        if (check_result(e1, e2, a, c_pdd, pdd_div_const_op))
            return e2->m_result;
        push(div_rec(lo(a), c, c_pdd));
        push(div_rec(hi(a), c, c_pdd));
        PDD l = read(2);
        PDD h = read(1);
        PDD res = null_pdd;
        if (l != null_pdd && h != null_pdd)
            res = make_node(level(a), l, h);
        pop(2);
        e1->m_result = res;
        return res;
    }

    pdd pdd_manager::pow(pdd const &p, unsigned j) {
        return pdd(pow(p.root, j), this);
    }

    pdd_manager::PDD pdd_manager::pow(PDD p, unsigned j) {
        if (j == 0)
            return one_pdd;
        else if (j == 1)
            return p;
        else if (is_zero(p))
            return zero_pdd;
        else if (is_one(p))
            return one_pdd;
        else if (is_val(p))
            return imk_val(power(val(p), j));
        else
            return pow_rec(p, j);
    }

    pdd_manager::PDD pdd_manager::pow_rec(PDD p, unsigned j) {
        SASSERT(j > 0);
        if (j == 1)
            return p;
        // j even: pow(p,2*j')   =   pow(p*p,j')
        // j odd:  pow(p,2*j'+1) = p*pow(p*p,j')
        PDD q = pow_rec(apply(p, p, pdd_mul_op), j / 2);
        if (j & 1) {
            q = apply(q, p, pdd_mul_op);
        }
        return q;
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

    /**
     * factor p into lc*v^degree + rest
     * such that degree(rest, v) < degree
     * Initial implementation is very naive
     */
    void pdd_manager::factor(pdd const& p, unsigned v, unsigned degree, pdd& lc, pdd& rest) {
        unsigned level_v = m_var2level[v];
        if (degree == 0) {
            lc = zero();
            rest = p;
            return;
        }
        if (level(p.root) < level_v) {
            lc = zero();
            rest = p;
            return;
        }
        // Memoize nontrivial cases
        auto* et = m_factor_cache.insert_if_not_there2({p.root, v, degree});
        factor_entry* e = &et->get_data();
        if (e->is_valid()) {
            lc = pdd(e->m_lc, this);
            rest = pdd(e->m_rest, this);
            return;
        }

        if (level(p.root) > level_v) {
            pdd lc1 = zero(), rest1 = zero();
            pdd vv = mk_var(p.var());
            factor(p.hi(), v, degree, lc,  rest);
            factor(p.lo(), v, degree, lc1, rest1);
            lc   *= vv;
            rest *= vv;
            lc   += lc1;
            rest += rest1;
        }
        else {
            unsigned d = 0;
            pdd r = p;
            while (d < degree && !r.is_val() && level(r.root) == level_v) {
                d++;
                r = r.hi();
            }
            if (d == degree) {
                lc = r;
                r = p;
                rest = zero();
                pdd pow = one();
                for (unsigned i = 0; i < degree; r = r.hi(), pow *= mk_var(v), ++i) 
                    rest += pow * r.lo();
            }
            else {
                lc = zero();
                rest = p;
            }
        }
        et = m_factor_cache.insert_if_not_there2({p.root, v, degree});
        e = &et->get_data();        
        e->m_lc = lc.root;
        e->m_rest = rest.root;
    }

    bool pdd_manager::factor(pdd const& p, unsigned v, unsigned degree, pdd& lc) {
        pdd rest = lc;
        factor(p, v, degree, lc, rest);
        return rest.is_zero();
     }

    /**
     * Apply function f to all coefficients of the polynomial.
     * The function should be of type
     *      rational const& -> rational
     *      rational const& -> unsigned
     * and should always return integers.
     *
     * NOTE: the operation is not cached.
     */
    template <class Fn>
    pdd pdd_manager::map_coefficients(pdd const& p, Fn f) {
        if (p.is_val()) {
            return mk_val(rational(f(p.val())));
        } else {
            pdd x = mk_var(p.var());
            pdd lo = map_coefficients(p.lo(), f);
            pdd hi = map_coefficients(p.hi(), f);
            return x*hi + lo;
        }
    }

    /**
     * Perform S-polynomial reduction on p by q,
     * treating monomial with v as leading.
     *
     * p = a v^l + b = a' 2^j v^l + b
     * q = c v^m + d = c' 2^j v^m + d
     * such that
     *      deg(v, p) = l, i.e., v does not divide a and there is no v^l in b
     *      deg(v, q) = m, i.e., v does not divide c and there is no v^m in d
     *      l >= m
     *      j maximal, i.e., not both of a', c' are divisible by 2
     *
     * Then we reduce p by q:
     *
     *      r = c' p - a' v^(l-m) q
     *        = b c' - a' d v^(l-m)
     */
    bool pdd_manager::resolve(unsigned v, pdd const& p, pdd const& q, pdd& r) {
        unsigned const l = p.degree(v);
        unsigned const m = q.degree(v);
        // no reduction
        if (l < m || m == 0)
            return false;
               
        pdd a = zero();
        pdd b = zero();
        pdd c = zero();
        pdd d = zero();
        p.factor(v, l, a, b);
        q.factor(v, m, c, d);
        unsigned const j = std::min(max_pow2_divisor(a), max_pow2_divisor(c));
        SASSERT(j != UINT_MAX);  // should only be possible when both l and m are 0
        rational const pow2j = rational::power_of_two(j);
        pdd const aa = div(a, pow2j);
        pdd const cc = div(c, pow2j);
        pdd vv = pow(mk_var(v), l - m);
        r = b * cc - aa * d * vv;
        return true;
    }

    /**
    * Reduce polynomial a with respect to b by eliminating terms using v
    * 
    * a := a1*v^l + a2
    * b := b1*v^m + b2
    * l >= m
    * q, r := quot_rem(a1, b1) 
    * that is:
    *     q * b1 + r = a1
    * r = 0
    * result := reduce(v, q*b2*v^{l-m}, b) + reduce(v, a2, b)
    */
    pdd pdd_manager::reduce(unsigned v, pdd const& a, pdd const& b) {
        unsigned const m = b.degree(v);
        // no reduction
        if (m == 0)
            return a;
                    
        pdd b1 = zero();
        pdd b2 = zero();
        b.factor(v, m, b1, b2);

        // TODO - generalize this case to when leading coefficient is not a value
        if (m_semantics == mod2N_e && b1.is_val() && b1.val().is_odd() && !b1.is_one()) {
            rational b_inv;
            VERIFY(b1.val().mult_inverse(m_power_of_2, b_inv));
            b1 = 1;
            b2 *= b_inv;
        }

        return reduce(v, a, m, b1, b2);
    }

    pdd pdd_manager::reduce(unsigned v, pdd const& a, unsigned m, pdd const& b1, pdd const& b2) {
        SASSERT(m > 0);
        unsigned const l = a.degree(v);
        if (l < m)
            return a;

        pdd a1 = zero();
        pdd a2 = zero();
        pdd q = zero();
        pdd r = zero();
        a.factor(v, l, a1, a2);

        quot_rem(a1, b1, q, r);
        if (r.is_zero()) {
            SASSERT(q * b1 == a1);
            a1 = -q * b2;
            if (l > m)
                a1 = reduce(v, a1 * pow(mk_var(v), l - m), m, b1, b2);
        }
        else
            a1 = a1 * pow(mk_var(v), l);
        a2 = reduce(v, a2, m, b1, b2);

        return a1 + a2;
    }

    /**
    * quotient/remainder of 'a' divided by 'b'  
    * a := x*hi + lo
    * x > level(b):
    *    hi = q1*b + r1
    *    lo = q2*b + r2
    *    x*hi + lo = (x*q1 + q2)*b + (x*r1 + r2)
    *    q := x*q1 + q2
    *    r := x*r1 + r2
    *  Some special cases.
    *  General multi-variable polynomial division is TBD.
    */
    void pdd_manager::quot_rem(pdd const& a, pdd const& b, pdd& q, pdd& r) {
        if (level(a.root) > level(b.root)) {
            pdd q1(*this), q2(*this), r1(*this), r2(*this);
            quot_rem(a.hi(), b, q1, r1);
            quot_rem(a.lo(), b, q2, r2);
            q = mk_var(a.var()) * q1 + q2;
            r = mk_var(a.var()) * r1 + r2;
        }
        else if (level(a.root) < level(b.root)) {
            q = zero();
            r = a;
        }
        else if (a == b) {
            q = one();
            r = zero();
        }
        else if (a.is_val() && b.is_val() && divides(b.val(), a.val())) {
            q = mk_val(a.val() / b.val());
            r = zero();
        }
        else if (a.is_val() || b.is_val()) {
            q = zero();
            r = a;
        }
        else {
            SASSERT(level(a.root) == level(b.root));
            pdd q1(*this), q2(*this), r1(*this), r2(*this);
            quot_rem(a.hi(), b.hi(), q1, r1);
            quot_rem(a.lo(), b.lo(), q2, r2);
            if (q1 == q2 && r1.is_zero() && r2.is_zero()) {
                q = q1;
                r = zero();
            }
            else {
                q = zero();
                r = a;
            }
        }
    }

    /**
     * Returns the largest j such that 2^j divides p.
     */
    unsigned pdd_manager::max_pow2_divisor(PDD p) {
        init_mark();
        unsigned min_j = UINT_MAX;
        SASSERT(m_todo.empty());
        m_todo.push_back(p);
        while (!m_todo.empty()) {
            PDD r = m_todo.back();
            m_todo.pop_back();
            if (is_marked(r)) {
                continue;
            }
            set_mark(r);
            if (is_zero(r)) {
                // skip
            }
            else if (is_val(r)) {
                rational const& c = val(r);
                if (c.is_odd()) {
                    m_todo.reset();
                    return 0;
                } else {
                    unsigned j = c.trailing_zeros();
                    min_j = std::min(j, min_j);
                }
            }
            else {
                m_todo.push_back(lo(r));
                m_todo.push_back(hi(r));
            }
        }
        return min_j;
    }

    unsigned pdd_manager::max_pow2_divisor(pdd const& p) {
        return max_pow2_divisor(p.root);
    }

    bool pdd_manager::is_linear(pdd const& p) { 
        return is_linear(p.root); 
    }

    /*
      Determine whether p is a binary polynomial 
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

    /** Determine whether p contains at most one variable. */
    bool pdd_manager::is_univariate(PDD p) {
        unsigned const lvl = level(p);
        while (!is_val(p)) {
            if (!is_val(lo(p)))
                return false;
            if (level(p) != lvl)
                return false;
            p = hi(p);
        }
        return true;
    }

    /** Return true iff p contains no variables other than v. */
    bool pdd_manager::is_univariate_in(PDD p, unsigned v) {
        return (is_val(p) || var(p) == v) && is_univariate(p);
    }

    /**
     * Push coefficients of univariate polynomial in order of ascending degree.
     * Example:     a*x^2 + b*x + c    ==>    [ c, b, a ]
     */
    void pdd_manager::get_univariate_coefficients(PDD p, vector<rational>& coeff) {
        SASSERT(is_univariate(p));
        while (!is_val(p)) {
            coeff.push_back(val(lo(p)));
            p = hi(p);
        }
        coeff.push_back(val(p));
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
        if (r.is_zero()) 
            return zero_pdd;
        if (r.is_one()) 
            return one_pdd;
        if (m_semantics == mod2_e) 
            return imk_val(mod(r, rational(2)));
        if (m_semantics == mod2N_e && (r < 0 || r >= m_mod2N)) 
            return imk_val(mod(r, m_mod2N));
        const_info info;
        if (!m_mpq_table.find(r, info)) 
            init_value(info, r);
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
            if (m_nodes.size() > m_max_num_nodes) 
                throw mem_out();            
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

    unsigned pdd_manager::degree(PDD p, unsigned v) {
        init_mark();
        unsigned level_v = m_var2level[v];
        unsigned max_d = 0, d = 0;
        m_todo.push_back(p);
        while (!m_todo.empty()) {
            PDD r = m_todo.back();
            if (is_marked(r))
                m_todo.pop_back();
            else if (is_val(r))
                m_todo.pop_back();
            else if (level(r) < level_v)
                m_todo.pop_back();
            else if (level(r) == level_v) {
                d = 0;
                do {
                    ++d;
                    set_mark(r);
                    r = hi(r);
                } while (!is_val(r) && level(r) == level_v);
                max_d = std::max(d, max_d);
                m_todo.pop_back();
            }
            else {
                set_mark(r);
                m_todo.push_back(lo(r));
                m_todo.push_back(hi(r));
            }
        }
        return max_d;
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
        bool_vector reachable(m_nodes.size(), false);
        compute_reachable(reachable);
        return reachable[p];
    }

    void pdd_manager::compute_reachable(bool_vector& reachable) {
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
        bool_vector reachable(m_nodes.size(), false);
        compute_reachable(reachable);
        for (unsigned i = m_nodes.size(); i-- > pdd_no_op; ) {
            if (!reachable[i]) {
                if (is_val(i)) {
                    if (m_freeze_value == val(i)) 
                        continue;
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
            if (e->m_result != null_pdd)
                to_delete.push_back(e);            
            else 
                to_keep.push_back(e);            
        }
        m_op_cache.reset();
        for (op_entry* e : to_delete) 
            m_alloc.deallocate(sizeof(*e), e);
        
        for (op_entry* e : to_keep) 
            m_op_cache.insert(e);        

        m_factor_cache.reset();

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
        for (auto& [a, vs] : mons) {
            if (!first)
                out << " ";
            if (a.is_neg())
                out << "- ";
            else if (!first)
                out << "+ ";
            first = false;
            rational c = abs(a);
            vs.reverse();
            if (!c.is_one() || vs.empty()) {
                if (m_semantics == mod2N_e)
                    out << val_pp(*this, c, !vs.empty());
                else
                    out << c;
                if (!vs.empty()) out << "*";
            }
            unsigned v_prev = UINT_MAX;
            unsigned pow = 0;
            for (unsigned v : vs) {
                if (v == v_prev) {
                    pow++;
                    continue;
                }
                if (v_prev != UINT_MAX) {
                    out << "v" << v_prev;
                    if (pow > 1)
                        out << "^" << pow;
                    out << "*";
                }
                pow = 1;
                v_prev = v;
            }
            if (v_prev != UINT_MAX) {
                out << "v" << v_prev;
                if (pow > 1)
                    out << "^" << pow;
            }
        }
        if (first) out << "0";
        return out;
    }

    std::ostream& val_pp::display(std::ostream& out) const {
        if (m.get_semantics() != pdd_manager::mod2N_e)
            return out << val;
        unsigned pow;
        if (val.is_power_of_two(pow) && pow > 10)
            return out << "2^" << pow;
        for (int offset : {-2, -1, 1, 2})
            if (val < m.max_value() && (val - offset).is_power_of_two(pow) && pow > 10 && pow < m.power_of_2())
                return out << lparen() << "2^" << pow << (offset >= 0 ? "+" : "") << offset << rparen();
        rational neg_val = mod(-val, m.two_to_N());
        if (neg_val < val) {  // keep this condition so we don't suddenly print negative values where we wouldn't otherwise
            if (neg_val.is_power_of_two(pow) && pow > 10)
                return out << "-2^" << pow;
        }
        return out << m.normalize(val);
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
        if (m != other.m) {
            verbose_stream() << "pdd manager confusion: " << *this << " (mod 2^" << power_of_2() << ") := " << other << " (mod 2^" << other.power_of_2() << ")\n";
            UNREACHABLE();
            // TODO: in the end, this operator should probably be changed to also update the manager. But for now I want to detect such confusions.
            reset(*other.m);
        }
        SASSERT_EQ(power_of_2(), other.power_of_2());
        VERIFY_EQ(power_of_2(), other.power_of_2());
        VERIFY_EQ(m, other.m);
        unsigned r1 = root; 
        root = other.root; 
        m->inc_ref(root); 
        m->dec_ref(r1); 
        return *this; 
    }

    pdd& pdd::operator=(unsigned k) {
        m->dec_ref(root);
        root = m->mk_val(k).root;
        m->inc_ref(root);
        return *this;
    }

    pdd& pdd::operator=(rational const& k) {
        m->dec_ref(root);
        root = m->mk_val(k).root;
        m->inc_ref(root);
        return *this;
    }

    /* Reset pdd to 0. Allows re-assigning the pdd manager. */
    void pdd::reset(pdd_manager& new_m) {
        m->dec_ref(root);
        root = 0;
        m = &new_m;
        SASSERT(is_zero());
    }

    rational const& pdd::leading_coefficient() const {
        pdd p = *this;
        while (!p.is_val())
            p = p.hi();
        return p.val();
    }

    rational const& pdd_manager::offset(PDD p) const {
        while (!is_val(p))
            p = lo(p);
        return val(p);
    }

    pdd pdd::shl(unsigned n) const {
        return (*this) * rational::power_of_two(n);
    }

    /**
     * \brief substitute variable v by r.
     * This base line implementation is simplistic and does not use operator caching.
     */
    pdd pdd::subst_pdd(unsigned v, pdd const& r) const {
        if (is_val())
            return *this;
        if (m->m_var2level[var()] < m->m_var2level[v])
            return *this;
        pdd l = lo().subst_pdd(v, r);
        pdd h = hi().subst_pdd(v, r);
        if (var() == v) 
            return r*h + l;
        else if (l == lo() && h == hi())
            return *this;
        else
            return m->mk_var(var())*h + l;
    }

    std::pair<unsigned_vector, pdd> pdd::var_factors() const {
        if (is_val())
            return { unsigned_vector(), *this };
        unsigned v = var();
        if (lo().is_val()) {
            if (!lo().is_zero())
                return { unsigned_vector(), *this };
            auto [vars, p] = hi().var_factors();
            vars.push_back(v);
            return {vars, p};
        }
        auto [lo_vars, q] = lo().var_factors();
        if (lo_vars.empty())
            return { unsigned_vector(), *this };
        
        unsigned_vector lo_and_hi;
        auto merge = [&](unsigned_vector& lo_vars, unsigned_vector& hi_vars) {
            unsigned ir = 0, jr = 0;
            for (unsigned i = 0, j = 0; i < lo_vars.size() || j < hi_vars.size(); ) {
                if (i == lo_vars.size()) 
                    hi_vars[jr++] = hi_vars[j++];
                else if (j == hi_vars.size()) 
                    lo_vars[ir++] = lo_vars[i++];
                else if (lo_vars[i] == hi_vars[j]) {
                    lo_and_hi.push_back(lo_vars[i]);
                    ++i;
                    ++j;
                }
                else if (m->m_var2level[lo_vars[i]] > m->m_var2level[hi_vars[j]]) 
                    hi_vars[jr++] = hi_vars[j++];
                else 
                    lo_vars[ir++] = lo_vars[i++];
            }
            lo_vars.shrink(ir);
            hi_vars.shrink(jr);
        };

        auto mul = [&](unsigned_vector const& vars, pdd p) {
            for (auto v : vars)
                p *= m->mk_var(v);
            return p;
        };

        auto [hi_vars, p] = hi().var_factors();
        if (lo_vars.back() == v) {
            lo_vars.pop_back();
            merge(lo_vars, hi_vars);
            lo_and_hi.push_back(v);
            return { lo_and_hi, mul(lo_vars, q) + mul(hi_vars, p) };
        }
        if (hi_vars.empty())
            return { unsigned_vector(), *this };
        
        merge(lo_vars, hi_vars);
        hi_vars.push_back(v);
        if (lo_and_hi.empty())
            return { unsigned_vector(), *this };
        else 
            return { lo_and_hi, mul(lo_vars, q) + mul(hi_vars, p) };                
    }


    std::ostream& operator<<(std::ostream& out, pdd const& b) { return b.display(out); }

    void pdd_iterator::next() {
        auto& m = m_pdd.manager();
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
        auto& m = m_pdd.manager();
        while (!m.is_val(n)) {
            m_nodes.push_back(std::make_pair(true, n));
            m_mono.vars.push_back(m.var(n));
            n = m.hi(n);
        }
        m_mono.coeff = m.val(n);
        // if m_pdd is constant and non-zero, the iterator should return a single monomial
        if (m_nodes.empty() && !m_mono.coeff.is_zero())
            m_nodes.push_back(std::make_pair(false, n));
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

    void pdd_linear_iterator::first() {
        m_next = m_pdd.root;
        next();
    }

    void pdd_linear_iterator::next() {
        SASSERT(m_next != pdd_manager::null_pdd);
        auto& m = m_pdd.manager();
        while (!m.is_val(m_next)) {
            unsigned const var = m.var(m_next);
            rational const val = m.offset(m.hi(m_next));
            m_next = m.lo(m_next);
            if (!val.is_zero()) {
                m_mono = {val, var};
                return;
            }
        }
        m_next = pdd_manager::null_pdd;
    }

    pdd_linear_iterator pdd::pdd_linear_monomials::begin() const {
        return pdd_linear_iterator(m_pdd, true);
    }

    pdd_linear_iterator pdd::pdd_linear_monomials::end() const {
        return pdd_linear_iterator(m_pdd, false);
    }

}  // namespace dd
