/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    polynomial.cpp

Abstract:

    Goodies for creating and handling polynomials.

Author:

    Leonardo (leonardo) 2011-11-15

Notes:

--*/
#include"polynomial.h"
#include"vector.h"
#include"chashtable.h"
#include"small_object_allocator.h"
#include"id_gen.h"
#include"buffer.h"
#include"scoped_ptr_vector.h"
#include"cooperate.h"
#include"upolynomial_factorization.h"
#include"polynomial_factorization.h"
#include"polynomial_primes.h"
#include"permutation.h"
#include"algebraic_numbers.h"
#include"mpzzp.h"
#include"timeit.h"
#include"linear_eq_solver.h"
#include"scoped_numeral_buffer.h"
#include"ref_buffer.h"

namespace polynomial {

    factor_params::factor_params():
        m_max_p(UINT_MAX),
        m_p_trials(1),
        m_max_search_size(UINT_MAX) {
    }

    factor_params::factor_params(unsigned max_p, unsigned p_trials, unsigned max_search_size):
        m_max_p(max_p),
        m_p_trials(p_trials),
        m_max_search_size(max_search_size) {
    }
    
    void factor_params::updt_params(params_ref const & p) {
        m_max_p    = p.get_uint("max_prime", UINT_MAX);
        m_p_trials = p.get_uint("num_primes", 1);
        m_max_search_size = p.get_uint("max_search_size", UINT_MAX);
    }
    
    void factor_params::get_param_descrs(param_descrs & r) {
        r.insert("max_search_size", CPK_UINT, "(default: infty) Z3 polynomial factorization is composed of three steps: factorization in GF(p), lifting and search. This parameter can be used to limit the search space."); 
        r.insert("max_prime", CPK_UINT, "(default: infty) Z3 polynomial factorization is composed of three steps: factorization in GF(p), lifting and search. This parameter limits the maximum prime number p to be used in the first step.");
        r.insert("num_primes", CPK_UINT, "(default: 1) Z3 polynomial factorization is composed of three steps: factorization in GF(p), lifting and search. The search space may be reduced by factoring the polynomial in different GF(p)'s. This parameter specify the maximum number of finite factorizations to be considered, before lifiting and searching.");
    }

    typedef ptr_vector<monomial> monomial_vector;
    
    void var2degree::display(std::ostream & out) const {
        bool first = true;
        out << "[";
        for (unsigned i = 0; i < m_var2degree.size(); ++ i) {
            if (m_var2degree.size() > 0) {
                if (!first) {
                    out << ",";
                }
                out << "x" << i << "^" << m_var2degree[i];
                if (first) {
                    first = false;
                }
            }
        }
        out << "]";
    }

    // -----------------------------------
    //
    // Monomials
    //
    // -----------------------------------
    
    /**
       \brief power: var + exponent
    */
    class power : public std::pair<var, unsigned> {
    public:
        power():std::pair<var, unsigned>() {}
        power(var v, unsigned d):std::pair<var, unsigned>(v, d) {}
        var get_var() const { return first; }
        unsigned degree() const { return second; }
        unsigned & degree() { return second; }
        void set_var(var x) { first = x; }
        
        struct lt_var {
            bool operator()(power const & p1, power const & p2) {                
                // CMW: The assertion below does not hold on OSX, because 
                // their implementation of std::sort will try to compare
                // two items at the same index instead of comparing
                // the indices directly. I suspect that the purpose of
                // this assertion was to make sure that there are 
                // no duplicates, so I replaced it with a new assertion at
                // the end of var_degrees(...).

                // SASSERT(p1.get_var() != p2.get_var());

                return p1.get_var() < p2.get_var();
            }
        };

        struct lt_degree {
            bool operator()(power const & p1, power const & p2) {
                return p1.degree() < p2.degree();
            }
        };
    };


    std::ostream & operator<<(std::ostream & out, power const & p) {
        out << "x" << p.get_var();
        if (p.degree() != 1)
            out << "^" << p.degree();
        return out;
    }

    /**
       \brief Return true if the variables in pws are sorted in increasing order and are distinct.
    */
    bool is_valid_power_product(unsigned sz, power const * pws) {
        for (unsigned i = 1; i < sz; i++) {
            if (pws[i-1].get_var() >= pws[i].get_var())
                return false;
        }
        return true;
    }
    
    /**
       \brief Return total degree of the given power product.
    */
    unsigned power_product_total_degree(unsigned sz, power const * pws) {
        unsigned r = 0;
        for (unsigned i = 0; i < sz; i++)
            r += pws[i].degree();
        return r;
    }

        
    /**
       \brief Monomials (power products)
    */
    class monomial {
        unsigned  m_ref_count;
        unsigned  m_id;           //!< unique id
        unsigned  m_total_degree; //!< total degree of the monomial
        unsigned  m_size;         //!< number of powers
        unsigned  m_hash;
        power     m_powers[0];
        friend class tmp_monomial;

        void sort() {
            std::sort(m_powers, m_powers + m_size, power::lt_var());
        }
    public:
        static unsigned hash_core(unsigned sz, power const * pws) {
            return string_hash(reinterpret_cast<char*>(const_cast<power*>(pws)), sz*sizeof(power), 11);
        }

        struct hash_proc {
            unsigned operator()(monomial const * m) const {
                return m->m_hash; 
            }
        };
        
        struct eq_proc {
            bool operator()(monomial const * m1, monomial const * m2) const {
                if (m1->size() != m2->size() || m1->hash() != m2->hash())
                    return false;
                // m_total_degree must not be used as a filter, because it is not updated in temporary monomials.
                for (unsigned i = 0; i < m1->m_size; i++) {
                    if (m1->get_power(i) != m2->get_power(i))
                        return false;
                }
                
                return true;
            }
        };

        static unsigned get_obj_size(unsigned sz) { return sizeof(monomial) + sz * sizeof(power); }
        
        monomial(unsigned id, unsigned sz, power const * pws, unsigned h):
            m_ref_count(0),
            m_id(id),
            m_total_degree(0),
            m_size(sz),
            m_hash(h) {
            for (unsigned i = 0; i < sz; i ++) {
                power const & pw = pws[i];
                m_powers[i] = pw;
                SASSERT(i == 0 || get_var(i) > get_var(i-1));
                SASSERT(degree(i) > 0);
                m_total_degree += degree(i); 
            }
        }

        unsigned hash() const { return m_hash; }

        unsigned ref_count() const { return m_ref_count; }
        
        void inc_ref() { m_ref_count++; }
        
        void dec_ref() { SASSERT(m_ref_count > 0); m_ref_count--; }

        bool is_valid() const {
            return is_valid_power_product(m_size, m_powers) && power_product_total_degree(m_size, m_powers) == m_total_degree;
        }

        unsigned id() const { return m_id; }
        
        unsigned size() const { return m_size; }
        
        unsigned total_degree() const { return m_total_degree; }
        
        power const & get_power(unsigned idx) const { SASSERT(idx < size()); return m_powers[idx]; }
        
        power const * get_powers() const { return m_powers; }
        
        var get_var(unsigned idx) const { return get_power(idx).get_var(); }
        
        unsigned degree(unsigned idx) const { return get_power(idx).degree(); }

        var max_var() const {
            if (m_size == 0) 
                return null_var;
            return get_var(m_size - 1);
        }

        unsigned max_var_degree() const {
            if (m_size == 0)
                return 0;
            return degree(m_size - 1);
        }

#define SMALL_MONOMIAL 8

        unsigned index_of(var x) const {
            if (m_size == 0)
                return UINT_MAX;
            unsigned last = m_size - 1;
            if (get_var(last) == x)
                return last;
            if (m_size < SMALL_MONOMIAL) {
                // use linear search for small monomials
                // search backwards since we usually ask for the degree of "big" variables
                unsigned i = last;
                while (i > 0) {
                    --i;
                    if (get_var(i) == x)
                        return i;
                }
                return UINT_MAX;
            }
            else {
                // use binary search for big monomials
                int low  = 0;
                int high = last;
                while (true) {
                    int mid   = low + ((high - low)/2);
                    var x_mid = get_var(mid);
                    if (x > x_mid) {
                        low = mid + 1;
                    }
                    else if (x < x_mid) {
                        high = mid - 1;
                    }
                    else {
                        return mid;
                    }
                    if (low > high)
                        return UINT_MAX;
                }
            }
        }

        unsigned degree_of(var x) const {
            unsigned pos = index_of(x);
            if (pos == UINT_MAX)
                return 0;
            return degree(pos);
        }


        // Given the subset S of variables that are smaller than x,
        // then return the maximal one.
        var max_smaller_than_core(var x) const {
            if (m_size == 0)
                return null_var;
            if (m_size < SMALL_MONOMIAL) {
                // use linear search for small monomials
                // search backwards since we usually ask for the degree of "big" variables
                unsigned i = m_size;
                while (i > 0) {
                    --i;
                    if (get_var(i) < x)
                        return get_var(i);
                }
                return null_var;
            }
            else {
                // use binary search for big monomials
                int low  = 0;
                int high = m_size-1;
                if (x <= get_var(low)) {
                    return null_var;
                }
                if (x > get_var(high)) {
                    return get_var(high);
                }
                if (x == get_var(high)) {
                    SASSERT(high > 0);
                    return get_var(high-1);
                }
                while (true) {
                    SASSERT(0 <= low && high < static_cast<int>(m_size));
                    SASSERT(get_var(low) < x);
                    SASSERT(x < get_var(high));
                    SASSERT(low < high);
                    if (high == low + 1) {
                        SASSERT(get_var(low) < x);
                        SASSERT(x < get_var(low+1));
                        return get_var(low);
                    }
                    SASSERT(high > low + 1);
                    int mid   = low + ((high - low)/2);
                    SASSERT(low < mid && mid < high);
                    var x_mid = get_var(mid);
                    if (x_mid == x) {
                        SASSERT(low < mid && mid < high && high < static_cast<int>(m_size));
                        SASSERT(get_var(mid-1) < x && x == get_var(mid));
                        return get_var(mid-1);
                    }
                    if (x < x_mid) {
                        high = mid;
                    }
                    else {
                        SASSERT(x_mid < x);
                        low  = mid;
                    }
                }
            }
        }

        var max_smaller_than(var x) const {
            SASSERT(x != null_var);
            var y = max_smaller_than_core(x);
            DEBUG_CODE({ 
                bool found = false;
                for (unsigned i = 0; i < m_size; i++) {
                    if (get_var(i) < x) {
                        CTRACE("poly_bug", !(y != null_var && get_var(i) <= y),
                               tout << "m: "; display(tout); tout << "\n";
                               tout << "x: " << x << "\n";
                               tout << "y: " << y << "\n";
                               tout << "i: " << i << "\n";
                               tout << "get_var(i): " << get_var(i) << "\n";);
                        SASSERT(y != null_var && get_var(i) <= y);
                    }
                    if (get_var(i) == y)
                        found = true;
                }
                SASSERT(y == null_var || (y < x && found));
            });
            return y;
        }
        
        void display(std::ostream & out, display_var_proc const & proc = display_var_proc(), bool use_star = false) const {
            if (m_size == 0) {
                out << "1";
                return;
            }
            for (unsigned i = 0; i < m_size; i++) {
                if (i > 0) {
                    if (use_star)
                        out << "*";
                    else
                        out << " ";
                }
                proc(out, get_var(i));
                if (degree(i) > 1)
                    out << "^" << degree(i);
            }
        }

        void display_smt2(std::ostream & out, display_var_proc const & proc = display_var_proc()) const {
            if (m_size == 0) {
                out << "1";
            }
            else if (m_size == 1 && degree(0) == 1) {
                proc(out, get_var(0));
            }
            else {
                out << "(*";
                for (unsigned i = 0; i < m_size; i++) {
                    var x = get_var(i);
                    unsigned k = degree(i);
                    SASSERT(k > 0);
                    for (unsigned j = 0; j < k; j++) {
                        out << " ";
                        proc(out, x);
                    }
                }
            }
            out << ")";
        }
        
        bool is_unit() const { return m_size == 0; }

        /**
           \brief Return true if the degree of every variable is even.
        */
        bool is_power_of_two() const {
            for (unsigned i = 0; i < m_size; i++) {
                if (degree(i) % 2 == 1)
                    return false;
            }
            return true;
        }

        bool is_square() const {
            for (unsigned i = 0; i < m_size; i++) {
                if (degree(i) % 2 != 0)
                    return false;
            }
            return true;
        }

        void rename(unsigned sz, var const * xs) {
            for (unsigned i = 0; i < m_size; i++) {
                power & pw = m_powers[i];
                pw.set_var(xs[pw.get_var()]);
            }
            sort();
            m_hash = hash_core(m_size, m_powers);
        }
    };

    inline void swap(monomial * & m1, monomial * & m2) { std::swap(m1, m2); }

    typedef chashtable<monomial*, monomial::hash_proc, monomial::eq_proc> monomial_table;
    
    /**
       \brief Mapping from monomials to positions.
    */
    class monomial2pos {
        unsigned_vector          m_m2pos;
    public:
        unsigned get(monomial const * m) {
            unsigned id = m->id();
            m_m2pos.reserve(id+1, UINT_MAX);
            return m_m2pos[id];
        }

        void reset(monomial const * m) {
            unsigned id = m->id();
            SASSERT(id < m_m2pos.size());
            m_m2pos[id] = UINT_MAX;
        }
        
        void set(monomial const * m, unsigned pos) {
            unsigned id = m->id();
            m_m2pos.reserve(id+1, UINT_MAX);
            SASSERT(m_m2pos[id] == UINT_MAX);
            m_m2pos[id] = pos;
        }
        
        /**
           \brief Save the position of the monomials in p.
        */
        template<typename Poly>
        void set(Poly const * p) {
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                set(p->m(i), i);
            }
        }

        /**
           \brief Undo the effects of save_pos.
        */
        template<typename Poly>
        void reset(Poly const * p) {
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                reset(p->m(i));
            }
        }
    };


#define TMP_INITIAL_CAPACITY 128

    /**
       \brief Wrapper for temporary monomials.
    */
    class tmp_monomial {
        monomial *               m_ptr;
        unsigned                 m_capacity; //!< maximum number of arguments supported by m_ptr;
        
        monomial * allocate(unsigned capacity) {
            void * mem  = memory::allocate(monomial::get_obj_size(capacity));
            return new (mem) monomial(UINT_MAX, 0, 0, 0);
        }

        void deallocate(monomial * ptr, unsigned capacity) {
            memory::deallocate(ptr);
        }

        void increase_capacity(unsigned new_capacity) {
            SASSERT(new_capacity > m_capacity);
            deallocate(m_ptr, m_capacity);
            m_ptr = allocate(new_capacity);
            m_capacity = new_capacity;
        }

        void expand_capacity(unsigned new_capacity) {
            SASSERT(new_capacity > m_capacity);
            monomial * new_ptr  = allocate(new_capacity);
            new_ptr->m_size = m_ptr->m_size;
            memcpy(new_ptr->m_powers, m_ptr->m_powers, sizeof(power)*m_ptr->m_size);
            deallocate(m_ptr, m_capacity);
            m_ptr      = new_ptr;
            m_capacity = new_capacity;
        }
    public:
        tmp_monomial():
            m_ptr(allocate(TMP_INITIAL_CAPACITY)),
            m_capacity(TMP_INITIAL_CAPACITY) {
        }
      
        ~tmp_monomial() {
            deallocate(m_ptr, m_capacity);
        }
        
        void init(unsigned sz, power const * pws) {
            if (sz > m_capacity) 
                increase_capacity(sz * 2);
            SASSERT(sz < m_capacity);
            m_ptr->m_size = sz;
            if (sz == 0) return;
            memcpy(m_ptr->m_powers, pws, sizeof(power) * sz);
        }
        
        void reset() { 
            m_ptr->m_size = 0; 
        }

        unsigned size() const { 
            return m_ptr->m_size; 
        }
        
        void push_back(power const & pw) { 
            if (m_ptr->m_size >= m_capacity) 
                expand_capacity(m_ptr->m_size * 2);
            m_ptr->m_powers[m_ptr->m_size] = pw;
            m_ptr->m_size++;
        }
        
        monomial * get_ptr() { 
            unsigned sz = m_ptr->m_size;
            m_ptr->m_hash = monomial::hash_core(sz, m_ptr->m_powers);
            return m_ptr;
        }

        void reserve(unsigned capacity) {
            if (capacity > m_capacity)
                increase_capacity(capacity * 2);
        }

        void set_size(unsigned sz) {
            SASSERT(sz <= m_capacity);
            m_ptr->m_size = sz;
        }

        void set_power(unsigned idx, power const & pw) {
            SASSERT(idx < m_capacity);
            m_ptr->m_powers[idx] = pw;
        }

        power const & get_power(unsigned idx) const { return m_ptr->m_powers[idx]; }

        power const * get_powers() const { return m_ptr->m_powers; } 
    };

    /**
       \brief Compare m1 and m2 using a lexicographical order
       
       Return 
            -   -1  if m1 <_lex m2, 
            -   0   if m1 = m2,     
            -   1   if m1 >_lex m2

       The biggest variable dominates
       x3^3 > x3^2 x1^2 > x3 x2^2 x_1 > x1^3

       Remark: in out representation the biggest variable is in the last position.
    */
    int lex_compare(monomial const * m1, monomial const * m2) {
        if (m1 == m2)
            return 0;
        int sz1  = m1->size();
        int sz2  = m2->size();
        int idx1 = sz1 - 1;
        int idx2 = sz2 - 1;
        while (idx1 >= 0 && idx2 >= 0) {
            power const & pw1 = m1->get_power(idx1);
            power const & pw2 = m2->get_power(idx2);
            if (pw1.get_var() == pw2.get_var()) {
                if (pw1.degree() == pw2.degree()) {
                    idx1--;
                    idx2--;
                    continue;
                }
                return pw1.degree() < pw2.degree() ? -1 : 1;
            }
            return pw1.get_var() > pw2.get_var() ? 1 : -1;
        }
        SASSERT(idx1 >= 0 || idx2 >= 0);
        SASSERT(idx1 < 0  || idx2 < 0);
        return idx1 < 0 ? -1 : 1;
    }

    /**
       Similar to lex_compare, but min_var is assumed to be the minimal variable.
    */
    int lex_compare2(monomial const * m1, monomial const * m2, var min_var) {
        if (m1 == m2)
            return 0;
        int sz1  = m1->size();
        int sz2  = m2->size();
        int idx1 = sz1 - 1;
        int idx2 = sz2 - 1;
        unsigned min_var_degree1 = 0;
        unsigned min_var_degree2 = 0;
        while (idx1 >= 0 && idx2 >= 0) {
            power const & pw1 = m1->get_power(idx1);
            power const & pw2 = m2->get_power(idx2);
            if (pw1.get_var() == min_var) {
                min_var_degree1 = pw1.degree();
                idx1--;
                if (pw2.get_var() == min_var) {
                    min_var_degree2 = pw2.degree();
                    idx2--;
                }
                continue;
            }
            if (pw2.get_var() == min_var) {
                min_var_degree2 = pw2.degree();
                idx2--;
                continue;
            }
            if (pw1.get_var() == pw2.get_var()) {
                if (pw1.degree() == pw2.degree()) {
                    idx1--;
                    idx2--;
                    continue;
                }
                return pw1.degree() < pw2.degree() ? -1 : 1;
            }
            return pw1.get_var() > pw2.get_var() ? 1 : -1;
        }
        if (idx1 == idx2) {
            SASSERT(min_var_degree1 != min_var_degree2);
            return min_var_degree1 < min_var_degree2 ? -1 : 1; 
        }
        return idx1 < 0 ? -1 : 1;
    }

    struct lex_lt2 {
        var m_min;
        lex_lt2(var m):m_min(m) {}
        bool operator()(monomial * m1, monomial * m2) const { 
            TRACE("lex_bug", tout << "min: x" << m_min << "\n"; m1->display(tout); tout << "\n"; m2->display(tout); tout << "\n";);
            return lex_compare2(m1, m2, m_min) < 0; 
        }
    };

    /**
       \brief Compare m1 and m2 using a graded lexicographical order
       
       \see lex_compare
    */
    int graded_lex_compare(monomial const * m1, monomial const * m2) {
        unsigned t1 = m1->total_degree();
        unsigned t2 = m2->total_degree();
        if (t1 == t2)
            return lex_compare(m1, m2);
        else
            return t1 < t2 ? -1 : 1;
    }
    
    /**
       \brief Compare submonomials m1[start1, end1) and m2[start2, end2) using reverse lexicographical order
    */
    int rev_lex_compare(monomial const * m1, unsigned start1, unsigned end1, monomial const * m2, unsigned start2, unsigned end2) {
        SASSERT(end1 >= start1);
        SASSERT(end2 >= start2);
        unsigned idx1 = end1;
        unsigned idx2 = end2;
        while(idx1 > start1 && idx2 > start2) {
            --idx1;
            --idx2;
            power const & pw1 = m1->get_power(idx1);
            power const & pw2 = m2->get_power(idx2);
            if (pw1.get_var() == pw2.get_var()) {
                if (pw1.degree() == pw2.degree()) {
                    // Remark: the submonomials have the same total degree, but they are not equal. So, idx1 > 0 and idx2 > 0.
                    SASSERT(idx1 > start1 && idx2 > start2);
                    continue;
                }
                return pw1.degree() > pw2.degree() ? -1 : 1;
            }
            return pw1.get_var() > pw2.get_var() ? -1 : 1;
        }
        SASSERT(idx1 == start1 || idx2 == start2);
        if (idx1 == start1)
            return idx2 == start2 ? 0 : -1;
        SASSERT(idx2 == start2 && idx1 != start1);
        return 1;
    }
    
    /**
       \brief Compare m1 and m2 using reverse lexicographical order.

       \see lex_compare
    */
    int rev_lex_compare(monomial const * m1, monomial const * m2) {
        if (m1 == m2)
            return 0;
        return rev_lex_compare(m1, 0, m1->size(), m2, 0, m2->size());
    }

    /**
       \brief Compare m1 and m2 using graded reverse lexicographical order.

       \see lex_compare
    */
    int graded_rev_lex_compare(monomial const * m1, monomial const * m2) {
        unsigned t1 = m1->total_degree();
        unsigned t2 = m2->total_degree();
        if (t1 == t2)
            return rev_lex_compare(m1, m2);
        else
            return t1 < t2 ? -1 : 1;
    }

    struct graded_lex_gt {
        bool operator()(monomial const * m1, monomial const * m2) { return graded_lex_compare(m1, m2) < 0; }
    };

    /**
       \brief 
    */
    class monomial_manager {
        unsigned                 m_ref_count;
        small_object_allocator * m_allocator;
        bool                     m_own_allocator;
        monomial_table           m_monomials;
        id_gen                   m_mid_gen; // id generator for monomials
        unsigned                 m_next_var;
        monomial *               m_unit;
        tmp_monomial             m_mk_tmp;
        tmp_monomial             m_tmp1;
        tmp_monomial             m_tmp2;
        tmp_monomial             m_tmp3;
        svector<power>           m_powers_tmp;
    public:
        monomial_manager(small_object_allocator * a = 0) {
            m_ref_count = 0;
            m_next_var  = 0;
            if (a == 0) {
                m_allocator     = alloc(small_object_allocator, "polynomial");
                m_own_allocator = true;
            }
            else {
                m_allocator     = a;
                m_own_allocator = false;
            }
            m_unit = mk_monomial(0, static_cast<power const *>(0));
            inc_ref(m_unit);
        }

        ~monomial_manager() {
            dec_ref(m_unit);
            CTRACE("polynomial", !m_monomials.empty(), 
                   tout << "monomials leaked\n";
                   monomial_table::iterator it = m_monomials.begin(); monomial_table::iterator end = m_monomials.end();
                   for (; it != end; ++it) {
                       (*it)->display(tout); tout << "\n";
                   });
            SASSERT(m_monomials.empty());
            if (m_own_allocator)
                dealloc(m_allocator);
        }
        
        void inc_ref() {
            m_ref_count++;
        }

        void dec_ref() {
            SASSERT(m_ref_count > 0);
            m_ref_count--;
            if (m_ref_count == 0)
                dealloc(this);
        }

        small_object_allocator & allocator() { return *m_allocator; }
        
        var mk_var() {
            var r = m_next_var;
            m_next_var++;
            return r;
        }

        unsigned num_vars() const {
            return m_next_var;
        }

        bool is_valid(var x) const { 
            return x < m_next_var; 
        }

        void del(monomial * m) {
            unsigned obj_sz = monomial::get_obj_size(m->size());
            m_monomials.erase(m);
            m_mid_gen.recycle(m->id());
            m_allocator->deallocate(obj_sz, m);
        }

        void inc_ref(monomial * m) { 
            m->inc_ref();
        }
        
        void dec_ref(monomial * m) { 
            m->dec_ref();
            if (m->ref_count() == 0)
                del(m);
        }

        monomial * mk_unit() { return m_unit; }

        monomial * mk_monomial(tmp_monomial & tmp) {
            monomial * tmp_ptr = tmp.get_ptr();
            monomial * & m = m_monomials.insert_if_not_there(tmp_ptr);
            if (m != tmp_ptr)
                return m;
            void * mem   = m_allocator->allocate(monomial::get_obj_size(tmp_ptr->size()));
            unsigned id  = m_mid_gen.mk();
            monomial * r = new (mem) monomial(id, tmp_ptr->size(), tmp_ptr->get_powers(), tmp_ptr->hash());
            m            = r;
            SASSERT(m_monomials.contains(r));
            SASSERT(*(m_monomials.find_core(r)) == r);
            return r;
        }

        monomial * mk_monomial(unsigned sz, power const * pws) {
            SASSERT(is_valid_power_product(sz, pws));
            m_mk_tmp.init(sz, pws);
            return mk_monomial(m_mk_tmp);
        }

        monomial * convert(monomial const * src) {
            unsigned sz = src->size();
            for (unsigned i = 0; i < sz; i++) {
                var x = src->get_var(i);
                while (x >= num_vars()) {
                    mk_var();
                }
                SASSERT(x < num_vars());
            }
            return mk_monomial(src->size(), src->get_powers());
        }

        monomial * mk_monomial(var x) {
            SASSERT(is_valid(x));
            power pw(x, 1);
            return mk_monomial(1, &pw);
        }

        monomial * mk_monomial(var x, unsigned k) {
            if (k == 0)
                return m_unit;
            SASSERT(is_valid(x));
            power pw(x, k);
            return mk_monomial(1, &pw);
        }

        monomial * mk_monomial(unsigned sz, var * xs) {
            if (sz == 0)
                return m_unit;
            if (sz == 1)
                return mk_monomial(xs[0]);
            m_powers_tmp.reset();
            std::sort(xs, xs+sz);
            SASSERT(is_valid(xs[0]));
            m_powers_tmp.push_back(power(xs[0], 1));
            for (unsigned i = 1; i < sz; i++) {
                var x = xs[i];
                SASSERT(is_valid(x));
                power & last = m_powers_tmp.back();
                if (x == last.get_var())
                    last.degree()++;
                else
                    m_powers_tmp.push_back(power(x, 1));
            }
            return mk_monomial(m_powers_tmp.size(), m_powers_tmp.c_ptr());
        }

        monomial * mul(unsigned sz1, power const * pws1, unsigned sz2, power const * pws2) {
            SASSERT(is_valid_power_product(sz1, pws1));
            SASSERT(is_valid_power_product(sz2, pws2));
            tmp_monomial & product_tmp = m_tmp1;
            product_tmp.reserve(sz1 + sz2); // product has at most sz1 + sz2 powers
            unsigned i1 = 0, i2 = 0;
            unsigned j  = 0;
            while (true) {
                if (i1 == sz1) {
                    // copy 2
                    for (; i2 < sz2; i2++, j++)
                        product_tmp.set_power(j, pws2[i2]);
                    break;
                }
                if (i2 == sz2) {
                    // copy 1
                    for (; i1 < sz1; i1++, j++)
                        product_tmp.set_power(j, pws1[i1]);
                    break;
                }
                power const & pw1 = pws1[i1];
                power const & pw2 = pws2[i2];
                unsigned v1 = pw1.get_var();
                unsigned v2 = pw2.get_var();
                if (v1 == v2) {
                    product_tmp.set_power(j, power(v1, pw1.degree() + pw2.degree()));
                    i1++;
                    i2++;
                }
                else if (v1 < v2) {
                    product_tmp.set_power(j, pw1);
                    i1++;
                }
                else {
                    SASSERT(v1 > v2);
                    product_tmp.set_power(j, pw2);
                    i2++;
                }
                j++;
            }
            product_tmp.set_size(j);
            TRACE("monomial_mul_bug", 
                  tout << "before mk_monomial\n";
                  tout << "pws1: "; for (unsigned i = 0; i < sz1; i++) tout << pws1[i] << " "; tout << "\n";
                  tout << "pws2: "; for (unsigned i = 0; i < sz2; i++) tout << pws2[i] << " "; tout << "\n";
                  tout << "product_tmp: "; for (unsigned i = 0; i < product_tmp.size(); i++) tout << product_tmp.get_power(i) << " "; 
                  tout << "\n";);
            monomial * r = mk_monomial(product_tmp);
            TRACE("monomial_mul_bug", 
                  tout << "j: " << j << "\n";
                  tout << "r: "; r->display(tout); tout << "\n";
                  tout << "pws1: "; for (unsigned i = 0; i < sz1; i++) tout << pws1[i] << " "; tout << "\n";
                  tout << "pws2: "; for (unsigned i = 0; i < sz2; i++) tout << pws2[i] << " "; tout << "\n";
                  tout << "product_tmp: "; for (unsigned i = 0; i < product_tmp.size(); i++) tout << product_tmp.get_power(i) << " "; 
                  tout << "\n";);
            SASSERT(r->is_valid());
            SASSERT(r->total_degree() == power_product_total_degree(sz1, pws1) + power_product_total_degree(sz2, pws2));
            return r;
        }
        
        monomial * mul(monomial const * m1, monomial const * m2) { 
            if (m1 == m_unit)
                return const_cast<monomial*>(m2);
            if (m2 == m_unit)
                return const_cast<monomial*>(m1);
            return mul(m1->size(), m1->get_powers(), m2->size(), m2->get_powers());
        }


        template<bool STORE_RESULT>
        bool div_core(unsigned sz1, power const * pws1, unsigned sz2, power const * pws2, tmp_monomial & r) {
            if (STORE_RESULT)
                r.reserve(sz1); // r has at most sz1 arguments.
            unsigned i1  = 0;
            unsigned i2  = 0;
            unsigned j   = 0;
            if (sz1 < sz2) 
                return false; // pws2 does not divide pws1 
            while (true) {
                if (i2 == sz2) {
                    if (STORE_RESULT) {
                        for (; i1 < sz1; i1++, j++) 
                            r.set_power(j, pws1[i1]);
                        r.set_size(j);
                    }
                    return true;
                }
                if (i1 == sz1)
                    return false; // pws2 does not divide pws1
                power const & pw1 = pws1[i1];
                power const & pw2 = pws2[i2];
                unsigned v1 = pw1.get_var();
                unsigned v2 = pw2.get_var();
                if (v1 == v2) {
                    unsigned d1 = pw1.degree();
                    unsigned d2 = pw2.degree();
                    if (d1 < d2)
                        return false; // pws2 does not divide pws1
                    if (STORE_RESULT) {
                        if (d1 > d2) {
                            r.set_power(j, power(v1, d1 - d2));
                            j++;
                        }
                    }
                    i1++;
                    i2++;
                }
                else if (v1 < v2) {
                    if (STORE_RESULT) {
                        r.set_power(j, pw1);
                        j++;
                    }
                    i1++;
                }
                else {
                    SASSERT(v1 > v2);
                    return false; // pws2 does not divide pws1
                }
            }
        }

        bool div(monomial const * m1, monomial const * m2) {
            if (m1->total_degree() < m2->total_degree())
                return false;
            if (m1 == m2)
                return true;
            return div_core<false>(m1->size(), m1->get_powers(), m2->size(), m2->get_powers(), m_tmp1);
        }

        bool div(monomial const * m1, monomial const * m2, monomial * & r) {
            if (m1->total_degree() < m2->total_degree())
                return false;
            if (m1 == m2) {
                r = m_unit;
                return true;
            }
            tmp_monomial & div_tmp = m_tmp1;
            if (div_core<true>(m1->size(), m1->get_powers(), m2->size(), m2->get_powers(), div_tmp)) {
                r = mk_monomial(div_tmp);
                return true;
            }
            return false;
        }

        /** 
            \brief Compute the gcd of pws1 and pws2, store it in g, and pws1/g in r1, and pws2/g in r2
            Return true if the gcd is not 1. If the result is false, then g, r1 and r2 should not be used.
        */
        bool gcd_core(unsigned sz1, power const * pws1, unsigned sz2, power const * pws2, tmp_monomial & g, tmp_monomial & r1, tmp_monomial & r2) {
            g.reserve(std::min(sz1, sz2));
            r1.reserve(sz2); // r1 has at most num_args2 arguments
            r2.reserve(sz1); // r2 has at most num_args1 arguments
            bool found   = false;
            unsigned i1  = 0;
            unsigned i2  = 0;
            unsigned j1  = 0;
            unsigned j2  = 0;
            unsigned j3  = 0;
            while (true) {
                if (i1 == sz1) {
                    if (found) {
                        for (; i2 < sz2; i2++, j2++) 
                            r2.set_power(j2, pws2[i2]);
                        r1.set_size(j1);
                        r2.set_size(j2);
                        g.set_size(j3);
                        return true;
                    }
                    return false;
                }
                if (i2 == sz2) {
                    if (found) {
                        for (; i1 < sz1; i1++, j1++) 
                            r1.set_power(j1, pws1[i1]);
                        r1.set_size(j1);
                        r2.set_size(j2);
                        g.set_size(j3);
                        return true;
                    }
                    return false;
                }
                power const & pw1 = pws1[i1];
                power const & pw2 = pws2[i2];
                unsigned v1 = pw1.get_var();
                unsigned v2 = pw2.get_var();
                if (v1 == v2) {
                    found = true;
                    unsigned d1 = pw1.degree();
                    unsigned d2 = pw2.degree();
                    if (d1 > d2) {
                        r1.set_power(j1, power(v1, d1 - d2));
                        g.set_power(j3, pw2);
                        j1++;
                        j3++;
                    }
                    else if (d2 > d1) {
                        r2.set_power(j2, power(v2, d2 - d1));
                        g.set_power(j3, pw1);
                        j2++;
                        j3++;
                    }
                    else {
                        SASSERT(d1 == d2);
                        g.set_power(j3, pw1);
                        j3++;
                    }
                    i1++;
                    i2++;
                }
                else if (v1 < v2) {
                    r1.set_power(j1, pw1);
                    j1++;
                    i1++;
                }
                else {
                    SASSERT(v1 > v2);
                    r2.set_power(j2, pw2);
                    j2++;
                    i2++;
                }
            }
        }

        monomial * gcd(monomial const * m1, monomial const * m2, monomial * & q1, monomial * & q2) {
            if (gcd_core(m1->size(), m1->get_powers(), m2->size(), m2->get_powers(), m_tmp1, m_tmp2, m_tmp3)) {
                q1 = mk_monomial(m_tmp2);
                q2 = mk_monomial(m_tmp3);
                return mk_monomial(m_tmp1);
            }
            else {
                // gcd is one
                q1 = const_cast<monomial*>(m2);
                q2 = const_cast<monomial*>(m1);
                return m_unit;
            }
        }

        bool unify(monomial const * m1, monomial const * m2, monomial * & q1, monomial * & q2) {
            if (gcd_core(m1->size(), m1->get_powers(), m2->size(), m2->get_powers(), m_tmp1, m_tmp2, m_tmp3)) {
                q1 = mk_monomial(m_tmp2);
                q2 = mk_monomial(m_tmp3);
                return true;
            }
            return false;
        }

        monomial * pw(monomial const * m, unsigned k) {
            if (k == 0)
                return m_unit;
            if (k == 1)
                return const_cast<monomial*>(m);
            unsigned sz = m->size();
            tmp_monomial & pw_tmp = m_tmp1; 
            pw_tmp.reserve(sz);
            for (unsigned i = 0; i < sz; i++)
                pw_tmp.set_power(i, power(m->get_var(i), m->degree(i)*k));
            pw_tmp.set_size(sz);
            return mk_monomial(pw_tmp);
        }

        monomial * sqrt(monomial const * m) {
            SASSERT(m_unit != 0);
            if (m == m_unit)
                return m_unit;
            unsigned sz = m->size();
            tmp_monomial & sqrt_tmp = m_tmp1;
            sqrt_tmp.reserve(sz);
            for (unsigned i = 0; i < sz; i++) {
                if (m->degree(i) % 2 == 1)
                    return 0;
                sqrt_tmp.set_power(i, power(m->get_var(i), m->degree(i) / 2));
            }
            sqrt_tmp.set_size(sz);
            return mk_monomial(sqrt_tmp);
        }

        /**
           \brief Return m/x^k
        */
        monomial * div_x_k(monomial const * m, var x, unsigned k) {
            SASSERT(is_valid(x));
            unsigned sz = m->size();
            tmp_monomial & elim_tmp = m_tmp1;
            elim_tmp.reserve(sz);
            unsigned j = 0;
            for (unsigned i = 0; i < sz; i++) {
                power const & pw = m->get_power(i);
                var y = pw.get_var();
                if (x != y) {
                    elim_tmp.set_power(j, pw);
                    j++;
                }
                else {
                    SASSERT(k <= pw.degree());
                    unsigned d = pw.degree();
                    if (k < d) {
                        elim_tmp.set_power(j, power(y, d - k));
                        j++;
                    }
                }
            }
            elim_tmp.set_size(j);
            return mk_monomial(elim_tmp);
        }
        
        /**
           \brief Return m/x^n  where n == m->degree_of(x)  
        */
        monomial * div_x(monomial const * m, var x) {
            SASSERT(is_valid(x));
            unsigned sz = m->size();
            tmp_monomial & elim_tmp = m_tmp1;
            elim_tmp.reserve(sz);
            unsigned j = 0;
            for (unsigned i = 0; i < sz; i++) {
                power const & pw = m->get_power(i);
                var y = pw.get_var();
                if (x != y) {
                    elim_tmp.set_power(j, pw);
                    j++;
                }
            }
            elim_tmp.set_size(j);
            return mk_monomial(elim_tmp);
        }

        monomial * derivative(monomial const * m, var x) {
            SASSERT(is_valid(x));
            unsigned sz = m->size();
            tmp_monomial & derivative_tmp = m_tmp1;
            derivative_tmp.reserve(sz);
            unsigned j = 0;
            for (unsigned i = 0; i < sz; i++) {
                power const & pw = m->get_power(i);
                var y = pw.get_var();
                if (x == y) {
                    unsigned d = pw.degree();
                    if (d > 1) {
                        derivative_tmp.set_power(j, power(y, d-1));
                        j++;
                    }
                }
                else {
                    derivative_tmp.set_power(j, pw);
                    j++;
                }
            }
            derivative_tmp.set_size(j);
            return mk_monomial(derivative_tmp);
        }

        void rename(unsigned sz, var const * xs) {
            SASSERT(m_ref_count <= 1);
            SASSERT(sz == num_vars());
            DEBUG_CODE({
                // check whether xs is really a permutation
                svector<bool> found;
                found.resize(num_vars(), false);
                for (unsigned i = 0; i < sz; i++) {
                    SASSERT(xs[i] < num_vars());
                    SASSERT(!found[xs[i]]);
                    found[xs[i]] = true;
                }
            });
            monomial_table new_table;
            monomial_table::iterator it  = m_monomials.begin();
            monomial_table::iterator end = m_monomials.end();
            for (; it != end; ++it) {
                monomial * m = *it;
                m->rename(sz, xs);
                SASSERT(!new_table.contains(m));
                new_table.insert(m);
            }
            m_monomials.swap(new_table);
        }
        
    };

   
    /**
       We maintain the following invariant:
       The first monomial m of every non-zero polynomial p contains:
          1) the maximal variable x of p,
          2) and the degree of x in m is maximal in p.
    */
    class polynomial {
    public:
        typedef manager::numeral    numeral;
    private:
        unsigned     m_ref_count;
        unsigned     m_id:31;
        unsigned     m_lex_sorted:1;
        unsigned     m_size;
        numeral *    m_as;
        monomial **  m_ms;

        void lex_sort(unsigned start, unsigned end, var x, vector<unsigned_vector> & buckets, unsigned_vector & p) {
            SASSERT(end > start);
            unsigned max_degree = 0;
            for (unsigned i = start, j = 0; i < end; i++, j++) {
                monomial * m = m_ms[i];
                unsigned d = m->degree_of(x);
                buckets.reserve(d+1);
                buckets[d].push_back(j);
                if (d > max_degree)
                    max_degree = d;
            }
            p.reset();
            unsigned i = max_degree + 1;
            while (i > 0) {
                --i;
                p.append(buckets[i]);
                buckets[i].reset();
            }
            SASSERT(p.size() == end - start);
            apply_permutation(p.size(), m_as + start, p.c_ptr());
            apply_permutation_core(p.size(), m_ms + start, p.c_ptr()); // p is not needed anymore after this command
            i = start;
            while (i < end) {
                monomial * m = m_ms[i];
                unsigned d   = m->degree_of(x);
                if (d == 0) {
                    // x does not occur in m
                    // since we sorted, x should not in the rest
                    // we should find the maximal variable variable smaller than x in [i, end)
                    var y = max_smaller_than(i, end, x);
                    if (y != null_var)
                        lex_sort(i, end, y, buckets, p);
                    return;
                }
                unsigned j = i + 1;
                for (; j < end; j++) {
                    unsigned d_j   = m_ms[j]->degree_of(x);
                    SASSERT(d_j <= d); // it is sorted
                    if (d_j < d)
                        break;
                }
                SASSERT(j == end || m_ms[j]->degree_of(x) < d);
                // sort interval [i, j) using the maximal variable y smaller than x
                if (j > i + 1) {
                    // only need to sort if the interval has more than one element.
                    var y = max_smaller_than(i, j, x);
                    if (y != null_var)
                        lex_sort(i, j, y, buckets, p);
                }
                i = j;
            }
        }

    public:
        unsigned ref_count() const { return m_ref_count; }
        void inc_ref() { m_ref_count++; }
        void dec_ref() { SASSERT(m_ref_count > 0); m_ref_count--; }

        static unsigned get_obj_size(unsigned n) { return sizeof(polynomial) + n * (sizeof(numeral) + sizeof(monomial*)); }
        
        /**
           \brief Partial order used to implement the polynomial invariant that guarantees
           that the first monomial contains the maximal variable in the polynomial, and it
           occurs with maximal degree.
           
           Return true if m1 > m2 in this partial order.
        */
        static bool po_gt(monomial const * m1, monomial const * m2) {
            if (m1->size() == 0)
                return false;
            if (m2->size() == 0)
                return true;
            if (m1->max_var() < m2->max_var())
                return false;
            if (m1->max_var() > m2->max_var())
                return true;
            SASSERT(m1->max_var() == m2->max_var());
            return m1->max_var_degree() > m2->max_var_degree();
        }

        // swap monomials at positions 0 and pos
        void swap_0_pos(unsigned pos) {
            if (pos != 0) {
                swap(m_as[0], m_as[pos]);
                std::swap(m_ms[0], m_ms[pos]);
            }
        }

        polynomial(mpzzp_manager & nm, unsigned id, unsigned sz, numeral * as, monomial * const * ms, numeral * as_mem, monomial ** ms_mem):
            m_ref_count(0),
            m_id(id),
            m_lex_sorted(false),
            m_size(sz),
            m_as(as_mem),
            m_ms(ms_mem) {
            if (sz > 0) {
                unsigned max_pos = 0;
                for (unsigned i = 0; i < sz; i++) {
                    new (m_as + i) numeral(); // initialize the big number at m_as[i]
                    swap(m_as[i], as[i]);
                    SASSERT(ms[i]->ref_count() > 0);
                    m_ms[i] = ms[i];
                    if (i > 0 && po_gt(m_ms[i], m_ms[max_pos]))
                        max_pos = i;
                }
                swap_0_pos(max_pos);
            }
        }

        // Return the maximal variable y occuring in [m_ms + start, m_ms + end) that is smaller than x
        var max_smaller_than(unsigned start, unsigned end, var x) {
            var max = null_var;
            for (unsigned i = start; i < end; i++) {
                var y = m_ms[i]->max_smaller_than(x);
                if (y != null_var && (max == null_var || y > max))
                    max = y;
            }
            return max;
        }

        bool lex_sorted() const { 
            return m_lex_sorted;
        }

        // Put monomials in lexicographical order
        void lex_sort(vector<unsigned_vector> & buckets, unsigned_vector & p, mpzzp_manager & nm) {
            if (m_lex_sorted)
                return;
            if (size() <= 1) {
                m_lex_sorted = true;
                return;
            }
            lex_sort(0, size(), m(0)->max_var(), buckets, p);
            m_lex_sorted = true;
            DEBUG_CODE({
                for (unsigned i = 0; i < m_size - 1; i++) {
                    CTRACE("poly_bug", lex_compare(m_ms[i], m_ms[i+1]) <= 0,
                           tout << "i: " << i << "\npoly: "; display(tout, nm); tout << "\n";);
                    SASSERT(lex_compare(m_ms[i], m_ms[i+1]) > 0);
                }
            });
        }

        /**
           \brief Make sure that the first monomial contains the maximal variable x occuring in the polynomial,
           and x occurs with maximal degree.
        */
        void make_first_maximal() {
            if (m_size <= 1)
                return;
            unsigned max_pos = 0;
            for (unsigned i = 1; i < m_size; i++) {
                if (po_gt(m_ms[i], m_ms[max_pos]))
                    max_pos = i;
            }
            swap_0_pos(max_pos);
            m_lex_sorted = false;
        }

        /**
           \brief Return the position of the maximal monomial with
           respect to graded lexicographical order.  Return UINT_MAX
           if polynomial is zero.
        */
        unsigned graded_lex_max_pos() const {
            if (m_size == 0)
                return UINT_MAX;
            unsigned max_pos = 0;
            for (unsigned i = 1; i < m_size; i++) {
                if (graded_lex_compare(m_ms[i], m_ms[max_pos]) > 0)
                    max_pos = i;
            }
            return max_pos;
        }

        /**
           \brief Return the position of the minimal monomial with
           respect to graded lexicographical order.  Return UINT_MAX
           if polynomial is zero.
        */
        unsigned graded_lex_min_pos() const {
            if (m_size == 0)
                return UINT_MAX;
            unsigned min_pos = 0;
            for (unsigned i = 1; i < m_size; i++) {
                if (graded_lex_compare(m_ms[i], m_ms[min_pos]) < 0)
                    min_pos = i;
            }
            return min_pos;
        }

        unsigned id() const { return m_id; }
        unsigned size() const { return m_size; }
        monomial * m(unsigned idx) const { SASSERT(idx < size()); return m_ms[idx]; }
        numeral const & a(unsigned idx) const { SASSERT(idx < size()); return m_as[idx]; }
        numeral & a(unsigned idx) { SASSERT(idx < size()); return m_as[idx]; }
        numeral const * as() const { return m_as; }

        bool is_zero() const { return m_size == 0; }

        void display(std::ostream & out, mpzzp_manager & nm, display_var_proc const & proc = display_var_proc(), bool use_star = false) const {
            if (is_zero()) {
                out << "0";
                return;
            }

            for (unsigned i = 0; i < m_size; i++) {
                numeral const & a_i = a(i);
                _scoped_numeral<mpzzp_manager> abs_a_i(nm);
                nm.set(abs_a_i, a_i);
                nm.abs(abs_a_i);
                
                numeral const & a_prime = abs_a_i;
                if (i > 0) {
                    if (nm.is_neg(a_i))
                        out << " - ";
                    else
                        out << " + ";
                }
                else {
                    if (nm.is_neg(a_i))
                        out << "- ";
                }
                
                if (m(i)->is_unit()) {
                    out << nm.to_string(a_prime);
                }
                else if (nm.is_one(a_prime)) {
                    m(i)->display(out, proc, use_star);
                }
                else {
                    out << nm.to_string(a_prime);
                    if (use_star)
                        out << "*";
                    else
                        out << " ";
                    m(i)->display(out, proc, use_star);
                }
            }
        }

        static void display_num_smt2(std::ostream & out, mpzzp_manager & nm, numeral const & a) {
            if (nm.is_neg(a)) {
                out << "(- ";
                _scoped_numeral<mpzzp_manager> abs_a(nm);
                nm.set(abs_a, a);
                nm.neg(abs_a);
                nm.display(out, abs_a);
                out << ")";
            }
            else {
                nm.display(out, a);
            }
        }
        
        void display_mon_smt2(std::ostream & out, mpzzp_manager & nm, display_var_proc const & proc, unsigned i) const {
            SASSERT(i < m_size);
            monomial const * m_i = m(i);
            numeral const &  a_i = a(i);
            if (m_i->size() == 0) {
                display_num_smt2(out, nm, a_i);
            }
            else if (nm.is_one(a_i)) {
                m_i->display(out, proc);
            }
            else {
                out << "(* ";
                display_num_smt2(out, nm, a_i);
                m_i->display(out, proc);
                out << ")";
            }
        }

        void display_smt2(std::ostream & out, mpzzp_manager & nm, display_var_proc const & proc = display_var_proc()) const {
            if (m_size == 0) {
                out << "0";
            }
            else if (m_size == 1) {
                display_mon_smt2(out, nm, proc, 0);
            }
            else {
                out << "(+";
                for (unsigned i = 0; i < m_size; i++) {
                    out << " ";
                    display_mon_smt2(out, nm, proc, i);
                }
                out << ")";
            }
        }

        void display(std::ostream & out, mpzzp_manager & nm, bool use_star) const {
            display(out, nm, display_var_proc(), use_star);
        }

    };

    manager::factors::factors(manager & _m):m_manager(_m), m_total_factors(0) { 
        m().m().set(m_constant, 1); 
    }
    
    manager::factors::~factors() {
        reset();
        m().m().del(m_constant);
    }

    void manager::factors::reset() {
        for (unsigned i = 0; i < m_factors.size(); ++ i) {
            m().dec_ref(m_factors[i]);
        }
        m_factors.reset();
        m_degrees.reset();
        m_total_factors = 0;
        m().m().set(m_constant, 1); 
    }
    
    void manager::factors::push_back(polynomial * p, unsigned degree) {
        SASSERT(p != 0 && degree > 0);
        m_factors.push_back(p);
        m_degrees.push_back(degree);
        m_total_factors += degree;
        m().inc_ref(p);
    }
    
    void manager::factors::multiply(polynomial_ref & out) const {
        if (m_factors.empty()) {
            out = m().mk_const(m_constant);
        }
        else {
            // multiply the factors
            for (unsigned i = 0; i < m_factors.size(); ++ i) {
                polynomial_ref current(m_factors[i], m());
                if (m_degrees[i] > 1) {
                    m().pw(current, m_degrees[i], current);
                } 
                if (i == 0) {
                    out = current;
                } else {
                    out = m().mul(out, current);            
                }
            }
            // multiply the constant
            out = m().mul(m_constant, out);
        }
    }
    
    void manager::factors::display(std::ostream & out) const {
        out << m().m().to_string(get_constant());
        for (unsigned i = 0; i < m_factors.size(); ++ i) {
            out << " * (";
            m_manager.display(out, m_factors[i]);
            out << ")^" << m_degrees[i];
        }
    }

    void manager::factors::set_constant(numeral const & constant) { 
        m().m().set(m_constant, constant); 
    } 
    
    void manager::factors::set_degree(unsigned i, unsigned degree) { 
        SASSERT(i > 0); 
        m_total_factors -= m_degrees[i];              
        m_total_factors += m_degrees[i] = degree; 
    }

    polynomial_ref manager::factors::operator[](unsigned i) const { 
        return polynomial_ref(m_factors[i], m()); 
    }                
    
    unsigned manager::id(monomial const * m) {
        return m->id();
    }

    unsigned manager::id(polynomial const * p) {
        return p->id();
    }
    
    bool manager::is_unit(monomial const * m) {
        return m->size() == 0;
    }

    bool manager::is_zero(polynomial const * p) {
        return p->size() == 0;
    }
    
    bool manager::is_const(polynomial const * p) {
        return is_zero(p) || (p->size() == 1 && is_unit(p->m(0)));
    }

    bool manager::is_univariate(monomial const * m) {
        return m->size() <= 1;
    }

    bool manager::is_univariate(polynomial const * p) {
        unsigned sz = p->size();
        if (is_const(p))
            return true;
        monomial * m = p->m(0);
        var x = max_var(p);
        for (unsigned i = 0; i < sz; i++) {
            m = p->m(i);
            if (m->size() == 1 && m->get_var(0) == x)
                continue;
            if (m->size() == 0)
                continue;
            return false;
        }
        return true;
    }
    
    unsigned manager::size(polynomial const * p) {
        return p->size();
    }

    polynomial::numeral const & manager::coeff(polynomial const * p, unsigned i) {
        return p->a(i);
    }

    polynomial::numeral const & manager::univ_coeff(polynomial const * p, unsigned k) {
        static numeral zero(0);
        SASSERT(is_univariate(p));
        unsigned sz = p->size();
        for (unsigned i = 0; i < sz; i++) {
            if (p->m(i)->total_degree() == k)
                return p->a(i);
        }
        return zero;
    }

    monomial * manager::get_monomial(polynomial const * p, unsigned i) {
        return p->m(i);
    }

    unsigned manager::total_degree(monomial const * m) {
        return m->total_degree();
    }

    unsigned manager::size(monomial const * m) {
        return m->size();
    }
        
    var manager::get_var(monomial const * m, unsigned i) {
        return m->get_var(i);
    }
        
    unsigned manager::degree(monomial const * m, unsigned i) {
        return m->degree(i);
    }

    unsigned manager::degree_of(monomial const * m, var x) {
        return m->degree_of(x);
    }

    bool manager::is_linear(monomial const * m) {
        return m->size() == 0 || (m->size() == 1 && m->degree(0) == 1);
    }

    bool manager::is_linear(polynomial const * p) {
        unsigned sz = p->size();
        for (unsigned i = 0; i < sz; i++) {
            if (!is_linear(p->m(0)))
                return false;
        }
        return true;
    }

    unsigned manager::degree(polynomial const * p, var x) {
        unsigned sz = p->size();
        if (sz == 0)
            return 0;
        monomial * m  = p->m(0);
        unsigned msz = m->size();
        if (msz == 0)
            return 0; // see polynomial invariant.
        if (m->get_var(msz - 1) == x) {
            // x is the maximal variable in p
            return m->degree(msz - 1);
        }
        unsigned r = 0;
        // use slow (linear) scan.
        for (unsigned i = 0; i < sz; i++) {
            unsigned d = p->m(i)->degree_of(x);
            if (d > r)
                r = d;
        }
        return r;
    }
    
    var manager::max_var(polynomial const * p) {
        if (p->size() == 0)
            return null_var;
        monomial * m  = p->m(0);
        return m->max_var();
    }

    unsigned manager::total_degree(polynomial const * p) {
        // use linear scan... if it turns out to be too slow, I should cache total_degree in polynomial
        unsigned r = 0;
        unsigned sz = p->size();
        for (unsigned i = 0; i < sz; i++) {
            unsigned t = p->m(i)->total_degree();
            if (t > r)
                r = t;
        }
        return r;
    }

    struct manager::imp {
        typedef upolynomial::manager up_manager;
        typedef mpzzp_manager    numeral_manager; // refine numeral_manager

        typedef _scoped_numeral<numeral_manager> scoped_numeral;
        typedef _scoped_numeral_vector<numeral_manager> scoped_numeral_vector;

        manager &                m_wrapper;
        numeral_manager          m_manager;
        up_manager               m_upm;
        monomial_manager *       m_monomial_manager;
        polynomial_vector        m_polynomials;
        id_gen                   m_pid_gen; // id generator for polynomials
        del_eh *                 m_del_eh;
        polynomial *             m_zero;
        numeral                  m_zero_numeral;
        polynomial *             m_unit_poly;
        monomial2pos             m_m2pos;
        tmp_monomial             m_tmp1;
        numeral_vector           m_rat2numeral;
        numeral_vector           m_tmp_linear_as;
        monomial_vector          m_tmp_linear_ms;
        unsigned_vector          m_degree2pos;
        bool                     m_use_sparse_gcd;
        bool                     m_use_prs_gcd;
        volatile bool            m_cancel;

        // Debugging method: check if the coefficients of p are in the numeral_manager.
        bool consistent_coeffs(polynomial const * p) {
            scoped_numeral a(m_manager);
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                m_manager.set(a, p->a(i));
                SASSERT(m_manager.eq(a, p->a(i)));
            }
            return true;
        }
    
         /**
            \brief Divide as by the GCD of as.
            Return true, if the GCD is not 1.
         */
         static bool normalize_numerals(numeral_manager & m, numeral_vector & as) {
             unsigned sz = as.size();
             if (sz == 0)
                 return false;
             scoped_numeral g(m);
             m.gcd(as.size(), as.c_ptr(), g);
             if (m.is_one(g))
                 return false;
             SASSERT(m.is_pos(g));
             for (unsigned i = 0; i < sz; i++) {
                 m.div(as[i], g, as[i]);
             }
             return true;
         }

        /**
           \brief Som-of-monomials buffer.
           This a temporary datastructure for building polynomials.
           
           The following idiom should be used:
           Invoke add(...), addmul(...) several times, and then invoke mk() to obtain the final polynomial.
        */
        class som_buffer {
            imp *              m_owner;
            monomial2pos       m_m2pos;
            numeral_vector     m_tmp_as;
            monomial_vector    m_tmp_ms;

            /**
               \brief Remove zeros from m_tmp_as & m_tmp_ms.
               The reference counters of eliminated m_tmp_ms are decremented.
               m_m2pos is reset. That is for every m in m_tmp_ms, m_m2pos[m->id()] == UINT_MAX
            */
            void remove_zeros(bool normalize) {
                numeral_manager & mng = m_owner->m_manager;
                SASSERT(m_tmp_ms.size() == m_tmp_as.size());
                unsigned sz = m_tmp_ms.size();
                unsigned j = 0;
                for (unsigned i = 0; i < sz; i++) {
                    monomial * m = m_tmp_ms[i];
                    m_m2pos.reset(m);
                    if (mng.is_zero(m_tmp_as[i])) {
                        mng.reset(m_tmp_as[i]);
                        m_owner->dec_ref(m_tmp_ms[i]);
                    }
                    else {
                        if (i != j) {
                            SASSERT(m_tmp_ms[j] != m);
                            m_tmp_ms[j] = m;
                            swap(m_tmp_as[j], m_tmp_as[i]);
                        }
                        j++;
                    }
                }
                DEBUG_CODE({
                    for (unsigned i = j; i < sz; i++) {
                        SASSERT(mng.is_zero(m_tmp_as[i]));
                    }
                });
                m_tmp_as.shrink(j);
                m_tmp_ms.shrink(j);
                if (normalize) {
                    normalize_numerals(mng, m_tmp_as);
                }
            }

        public:
            som_buffer():m_owner(0) {}

            void reset() {
                if (empty())
                    return;
                numeral_manager & mng = m_owner->m_manager;
                SASSERT(m_tmp_ms.size() == m_tmp_as.size());
                unsigned sz = m_tmp_ms.size();
                for (unsigned i = 0; i < sz; i++) {
                    monomial * m = m_tmp_ms[i];
                    m_m2pos.reset(m);
                    mng.reset(m_tmp_as[i]);
                    m_owner->dec_ref(m_tmp_ms[i]);
                }
                m_tmp_as.reset();
                m_tmp_ms.reset();
            }

            void set_owner(imp * o) { m_owner = o; }

            unsigned size() const { return m_tmp_ms.size(); }

            bool empty() const { return m_tmp_ms.empty(); }

            monomial * m(unsigned i) const { return m_tmp_ms[i]; }
            
            numeral const & a(unsigned i) const { return m_tmp_as[i]; }

            /**
               \brief Return the position of the maximal monomial with
               respect to graded lexicographical order.

               Return UINT_MAX if empty.
            */
            unsigned graded_lex_max_pos() const {
                numeral_manager & mng = m_owner->m_manager;
                unsigned max_pos = UINT_MAX;
                unsigned sz = m_tmp_as.size();
                for (unsigned i = 0; i < sz; i++) {
                    if (!mng.is_zero(m_tmp_as[i])) {
                        if (max_pos == UINT_MAX) {
                            max_pos = i;
                        }
                        else {
                            if (graded_lex_compare(m_tmp_ms[i], m_tmp_ms[max_pos]) > 0)
                                max_pos = i;
                        }
                    }
                }
                return max_pos;
            }

            /**
               \brief Store a*m*p into the buffer.
               m_m2pos is updated with the position of the monomials in m_tmp_ms.
               
               The reference counter of new monomials added into the buffer is increased.
            */
            template<typename PolyType, bool CheckZeros>
            void addmul_core(numeral const & a, monomial const * m, PolyType const * p) {
                numeral_manager & mng = m_owner->m_manager;
                if (mng.is_zero(a))
                    return;
                unsigned sz = p->size();
                for (unsigned i = 0; i < sz; i++) {
                    if (CheckZeros && mng.is_zero(p->a(i)))
                        continue;
                    monomial * m2 = p->m(i);
                    m2 = m_owner->mul(m, m2);
                    unsigned pos  = m_m2pos.get(m2);
                    if (pos == UINT_MAX) {
                        m_m2pos.set(m2, m_tmp_ms.size());
                        m_tmp_ms.push_back(m2);
                        m_owner->inc_ref(m2);
                        m_tmp_as.push_back(numeral());
                        mng.mul(a, p->a(i), m_tmp_as.back());
                    }
                    else {
                        mng.addmul(m_tmp_as[pos], a, p->a(i), m_tmp_as[pos]);
                    }
                }
            }

            void addmul(numeral const & a, monomial const * m, polynomial const * p) {
                return addmul_core<polynomial, false>(a, m, p);
            }

            void addmul(numeral const & a, monomial const * m, som_buffer const * p) {
                return addmul_core<som_buffer, false>(a, m, p);
            }

            void addmul(numeral const & a, monomial const * m, som_buffer const & p) {
                return addmul(a, m, &p);
            }
            
            void addmul(numeral const & a, som_buffer const * p) {
                return addmul(a, m_owner->mk_unit(), p);
            }

            void addmul(numeral const & a, som_buffer const & p) {
                return addmul(a, &p);
            }

            void addmul(monomial const * m, som_buffer const * p) {
                numeral one(1);
                return addmul(one, m, p);
            }

            void addmul(monomial const * m, som_buffer const & p) {
                return addmul(m, &p);
            }

            /**
               \brief Store p into the buffer.
               m_m2pos is updated with the position of the monomials in m_tmp_ms.
               
               The reference counter of new monomials added into the buffer is increased.
            */
            void add(polynomial const * p) {
                numeral_manager & mng = m_owner->m_manager;
                unsigned sz = p->size();
                for (unsigned i = 0; i < sz; i++) {
                    monomial * m2 = p->m(i);
                    unsigned pos  = m_m2pos.get(m2);
                    if (pos == UINT_MAX) {
                        m_m2pos.set(m2, m_tmp_ms.size());
                        m_tmp_ms.push_back(m2);
                        m_owner->inc_ref(m2);
                        m_tmp_as.push_back(numeral());
                        mng.set(m_tmp_as.back(), p->a(i));
                    }
                    else {
                        mng.add(m_tmp_as[pos], p->a(i), m_tmp_as[pos]);
                    }
                }
            }
            
            /**
               \brief Add 'a*m' into m_tmp_as and m_tmp_ms.
               m_m2pos is updated with the position of the monomials in m_tmp_ms.
               
               The reference counter of m is increased.
            */
            void add(numeral const & a, monomial * m) {
                numeral_manager & mng = m_owner->m_manager;
                if (mng.is_zero(a))
                    return;
                unsigned pos  = m_m2pos.get(m);
                if (pos == UINT_MAX) {
                    m_m2pos.set(m, m_tmp_ms.size());
                    m_owner->inc_ref(m);
                    m_tmp_ms.push_back(m);
                    m_tmp_as.push_back(numeral());
                    mng.set(m_tmp_as.back(), a);
                }
                else {
                    mng.add(m_tmp_as[pos], a, m_tmp_as[pos]);
                }
            }
            
            /**
               \brief Add 'a' (that is, a*m_unit) into m_tmp_as and m_tmp_ms. 
               m_m2pos is updated with the position of the monomials in m_tmp_ms.
               
               The reference counter of m_unit is increased.
            */
            void add(numeral const & a) {
                add(a, m_owner->mk_unit());
            }

            void sort_graded_lex() {
                std::sort(m_tmp_ms.begin(), m_tmp_ms.end(), graded_lex_gt());
                numeral_vector new_as;
                unsigned sz = m_tmp_ms.size();
                for (unsigned i = 0; i < sz; i++) {
                    monomial * m = m_tmp_ms[i];
                    unsigned pos = m_m2pos.get(m);
                    new_as.push_back(numeral());
                    swap(new_as.back(), m_tmp_as[pos]);
                    m_m2pos.reset(m);
                    m_m2pos.set(m, i);
                }
                m_tmp_as.swap(new_as);
            }

            // For each monomial m
            //   If m contains x^k and k >= x2d[x] and x2d[x] != 0, then set coefficient of m to 0.
            void mod_d(var2degree const & x2d) {
                numeral_manager & mng = m_owner->m_manager;
                unsigned sz = m_tmp_ms.size();
                for (unsigned i = 0; i < sz; i++) {
                    if (mng.is_zero(m_tmp_as[i]))
                        continue;
                    monomial * m = m_tmp_ms[i];
                    unsigned msz = m->size();
                    unsigned j;
                    for (j = 0; j < msz; j++) {
                        var x = m->get_var(j);
                        unsigned dx = x2d.degree(x);
                        if (dx == 0)
                            continue;
                        if (m->degree(j) >= dx)
                            break;
                    }
                    if (j < msz) {
                        mng.reset(m_tmp_as[i]);
                    }
                }
            }

            polynomial * mk(bool normalize = false) {
                remove_zeros(normalize);
                polynomial * p = m_owner->mk_polynomial_core(m_tmp_as.size(), m_tmp_as.c_ptr(), m_tmp_ms.c_ptr());
                m_tmp_as.reset();
                m_tmp_ms.reset();
                return p;
            }

            void display(std::ostream & out) const {
                SASSERT(m_tmp_ms.size() == m_tmp_as.size());
                numeral_manager & mng = m_owner->m_manager;
                for (unsigned i = 0; i < m_tmp_as.size(); i++) {
                    if (i > 0) out << " + ";
                    out << mng.to_string(m_tmp_as[i]) << "*"; m_tmp_ms[i]->display(out);
                }
                out << "\n";
            }
        };

        class som_buffer_vector {
            imp *                  m_owner;
            ptr_vector<som_buffer> m_buffers;

            void ensure_capacity(unsigned sz) {
                unsigned old_sz = m_buffers.size();
                for (unsigned i = old_sz; i < sz; i++) {
                    som_buffer * new_buffer = alloc(som_buffer);
                    if (m_owner)
                        new_buffer->set_owner(m_owner);
                    m_buffers.push_back(new_buffer);
                }
                SASSERT(m_buffers.size() >= sz);
            }

        public:
            som_buffer_vector() {
                m_owner = 0;
            }

            ~som_buffer_vector() {
                unsigned sz = m_buffers.size();
                for (unsigned i = 0; i < sz; i++) {
                    dealloc(m_buffers[i]);
                }
            }

            void set_owner(imp * owner) {
                SASSERT(m_owner == owner || m_owner == 0);
                if (m_owner == 0) {
                    m_owner = owner;
                    unsigned sz = m_buffers.size();
                    for (unsigned i = 0; i < sz; i++) {
                        m_buffers[i]->set_owner(m_owner);
                    }
                }
            }

            som_buffer * operator[](unsigned idx) {
                ensure_capacity(idx+1);
                return m_buffers[idx];
            }

            void reset(unsigned sz) {
                if (sz > m_buffers.size())
                    sz = m_buffers.size();
                for (unsigned i = 0; i < sz; i++) {
                    m_buffers[i]->reset();
                }
            }                

            void reset() {
                reset(m_buffers.size());
            }

        };

        /**
           \brief Cheap version of som_buffer.
           In this buffer, each monomial can be added at most once.
        */
        class cheap_som_buffer {
            imp *              m_owner;
            numeral_vector     m_tmp_as;
            monomial_vector    m_tmp_ms;
        public:
            cheap_som_buffer():m_owner(0) {}

            void set_owner(imp * o) { m_owner = o; }
            bool empty() const { return m_tmp_ms.empty(); }

            /**
               \brief Add a*m to the buffer, the content of a is reset.
            */
            void add_reset(numeral & a, monomial * m) {
                SASSERT(std::find(m_tmp_ms.begin(), m_tmp_ms.end(), m) == m_tmp_ms.end());
                numeral_manager & mng = m_owner->m_manager;
                if (mng.is_zero(a))
                    return;
                m_tmp_as.push_back(numeral());
                swap(m_tmp_as.back(), a);
                m_owner->inc_ref(m);
                m_tmp_ms.push_back(m);
            }

            /**
               \brief Add a*m to the buffer.
            */
            void add(numeral const & a, monomial * m) {
                SASSERT(std::find(m_tmp_ms.begin(), m_tmp_ms.end(), m) == m_tmp_ms.end());
                numeral_manager & mng = m_owner->m_manager;
                if (mng.is_zero(a))
                    return;
                m_tmp_as.push_back(numeral());
                mng.set(m_tmp_as.back(), a);
                m_owner->inc_ref(m);
                m_tmp_ms.push_back(m);
            }

            /**
               \brief Add a*m*p to the buffer.
            */
            void addmul(numeral const & a, monomial const * m, polynomial const * p) {
                numeral_manager & mng = m_owner->m_manager;
                if (mng.is_zero(a))
                    return;
                unsigned sz = p->size();
                for (unsigned i = 0; i < sz; i++) {
                    monomial * m2 = p->m(i);
                    m2 = m_owner->mul(m, m2);
                    // m2 is not in m_tmp_ms
                    SASSERT(std::find(m_tmp_ms.begin(), m_tmp_ms.end(), m2) == m_tmp_ms.end());
                    m_owner->inc_ref(m2);
                    m_tmp_ms.push_back(m2);
                    m_tmp_as.push_back(numeral());
                    mng.mul(a, p->a(i), m_tmp_as.back());
                }
            }

            bool normalize() {
                return normalize_numerals(m_owner->m_manager, m_tmp_as);
            }

            void reset() {
                if (empty())
                    return;
                numeral_manager & mng = m_owner->m_manager;
                unsigned sz = m_tmp_ms.size();
                for (unsigned i = 0; i < sz; i++) {
                    mng.del(m_tmp_as[i]);
                    m_owner->dec_ref(m_tmp_ms[i]);
                }
                m_tmp_as.reset();
                m_tmp_ms.reset();
            }

            polynomial * mk() {
                polynomial * new_p = m_owner->mk_polynomial_core(m_tmp_as.size(), m_tmp_as.c_ptr(), m_tmp_ms.c_ptr());
                m_tmp_as.reset();
                m_tmp_ms.reset();
                return new_p;
            }
        };

        som_buffer       m_som_buffer;
        som_buffer       m_som_buffer2;
        cheap_som_buffer m_cheap_som_buffer;
        cheap_som_buffer m_cheap_som_buffer2;

        void init() {
            m_del_eh = 0;
            m_som_buffer.set_owner(this);
            m_som_buffer2.set_owner(this);
            m_cheap_som_buffer.set_owner(this);
            m_cheap_som_buffer2.set_owner(this);
            m_zero = mk_polynomial_core(0, 0, 0);
            m().set(m_zero_numeral, 0);
            inc_ref(m_zero);
            numeral one(1);
            m_unit_poly = mk_const_core(one);
            inc_ref(m_unit_poly);
            m_use_sparse_gcd = true;
            m_use_prs_gcd = false;
            m_cancel = false;
        }

        imp(manager & w, unsynch_mpz_manager & m, monomial_manager * mm):
            m_wrapper(w),
            m_manager(m),
            m_upm(m) {
            if (mm == 0)
                mm = alloc(monomial_manager);
            m_monomial_manager = mm;
            m_monomial_manager->inc_ref();
            init();
        }

        imp(manager & w, unsynch_mpz_manager & m, small_object_allocator * a):
            m_wrapper(w),
            m_manager(m),
            m_upm(m) {
            m_monomial_manager = alloc(monomial_manager, a);
            m_monomial_manager->inc_ref();
            init();
        }

        ~imp() {
            dec_ref(m_zero);
            dec_ref(m_unit_poly);
            m_som_buffer.reset();
            m_som_buffer2.reset();
            m_cheap_som_buffer.reset();
            m_cheap_som_buffer2.reset();
            m_manager.del(m_zero_numeral);
            m_mgcd_iterpolators.flush();
            m_mgcd_skeletons.reset();
            DEBUG_CODE({
                TRACE("polynomial", 
                      tout << "leaked polynomials\n";
                      for (unsigned i = 0; i < m_polynomials.size(); i++) {
                          if (m_polynomials[i] != 0) {
                              m_polynomials[i]->display(tout, m_manager);
                              tout << "\n";
                          }
                      });
                m_polynomials.reset();
            });
            SASSERT(m_polynomials.empty());
            m_monomial_manager->dec_ref();
        }

        void set_cancel(bool f) {
            m_cancel = f;
            m_upm.set_cancel(f);
        }

        void checkpoint() {
            if (m_cancel) {
                throw polynomial_exception("canceled");
            }
            cooperate("polynomial");
        }

        mpzzp_manager & m() const { return const_cast<imp*>(this)->m_manager; }
        manager & pm() const { return m_wrapper; } 
        up_manager & upm() { return m_upm; }
        monomial_manager & mm() const { return *m_monomial_manager; }

        var mk_var() {
            return mm().mk_var();
        }

        unsigned num_vars() const {
            return mm().num_vars();
        }

        bool is_valid(var x) const { 
            return mm().is_valid(x);
        }

        void add_del_eh(del_eh * eh) {
            eh->m_next = m_del_eh;
            m_del_eh = eh;
        }

        void remove_del_eh(del_eh * eh) {
            SASSERT(eh != 0);
            SASSERT(m_del_eh != 0);
            if (m_del_eh == eh) {
                m_del_eh = m_del_eh->m_next;
            }
            else {
                del_eh * curr = m_del_eh;
                while (curr) {
                    if (curr->m_next == eh) {
                        curr->m_next = curr->m_next->m_next;
                        return;
                    }
                    curr = curr->m_next;
                }
                UNREACHABLE();
            }
        }

        void del(polynomial * p) {
            TRACE("polynomial", tout << "deleting: "; p->display(tout, m_manager); tout << "\n";);
            if (m_del_eh != 0) {
                del_eh * curr = m_del_eh;
                do {
                    (*curr)(p);
                    curr = curr->m_next;
                }
                while (curr != 0);
            }
            unsigned sz     = p->size();
            unsigned obj_sz = polynomial::get_obj_size(sz);
            for (unsigned i = 0; i < sz; i++) {
                m_manager.del(p->a(i));
                dec_ref(p->m(i));
            }
            unsigned id = p->id();
            m_pid_gen.recycle(id);
            m_polynomials[id] = 0;
            mm().allocator().deallocate(obj_sz, p);
        }

        void inc_ref(monomial * m) { 
            mm().inc_ref(m);
        }
        
        void dec_ref(monomial * m) { 
            mm().dec_ref(m);
        }

        void inc_ref(polynomial * p) {
            p->inc_ref();
        }

        void dec_ref(polynomial * p) {
            p->dec_ref();
            if (p->ref_count() == 0)
                del(p);
        }
        
        vector<unsigned_vector> m_lex_sort_buckets;
        unsigned_vector         m_lex_sort_permutation;
        void lex_sort(polynomial const * p) {
            const_cast<polynomial*>(p)->lex_sort(m_lex_sort_buckets, m_lex_sort_permutation, m_manager);
        }

        struct poly_khasher { unsigned operator()(polynomial const * p) const { return 17; } };

        struct poly_chasher { 
            unsigned operator()(polynomial const * p, unsigned idx) const { 
                return hash_u_u(p->m(idx)->hash(), numeral_manager::hash(p->a(idx)));
            }
        };
        
        unsigned hash(polynomial const * p) {
            if (p->size() == 0)
                return 31;
            lex_sort(const_cast<polynomial*>(p));
            return get_composite_hash(p, p->size(), poly_khasher(), poly_chasher());
        }

        polynomial * mk_polynomial_core(unsigned sz, numeral * as, monomial * const * ms) {
            unsigned obj_sz = polynomial::get_obj_size(sz);
            void * mem      = mm().allocator().allocate(obj_sz);
            void * as_mem   = static_cast<char*>(mem) + sizeof(polynomial);
            void * ms_mem   = static_cast<char*>(as_mem) + sizeof(numeral)*sz;
            unsigned id     = m_pid_gen.mk();
            polynomial * p  = new (mem) polynomial(m_manager, id, sz, as, ms, static_cast<numeral*>(as_mem), static_cast<monomial**>(ms_mem));
            m_polynomials.reserve(id+1);
            SASSERT(m_polynomials[id] == 0);
            m_polynomials[id] = p;
            return p;
        }

        polynomial * mk_zero() {
            return m_zero;
        }

        polynomial * mk_one() {
            return m_unit_poly;
        }

        monomial * mk_unit() { return mm().mk_unit(); }

        monomial * mk_monomial(tmp_monomial & tmp) { return mm().mk_monomial(tmp); }

        monomial * mk_monomial(var x) { return mm().mk_monomial(x); }

        monomial * mk_monomial(var x, unsigned k) { return mm().mk_monomial(x, k); }

        monomial * mk_monomial(unsigned sz, var * xs) { return mm().mk_monomial(sz, xs); }

        monomial * mk_monomial(unsigned sz, power const * pws) { return mm().mk_monomial(sz, pws); }
        
        monomial * convert(monomial const * src) { return mm().convert(src); }

        polynomial * mk_const_core(numeral & a) {
            monomial * u = mk_unit();
            inc_ref(u);
            return mk_polynomial_core(1, &a, &u);
        }
        
        polynomial * mk_const(numeral & a) {
            if (m_manager.is_zero(a))
                return mk_zero();
            if (m_manager.is_one(a))
                return mk_one();
            return mk_const_core(a);
        }

        polynomial * mk_const(rational const & a) {
            SASSERT(a.is_int());
            scoped_numeral tmp(m_manager);
            m_manager.set(tmp, a.to_mpq().numerator());
            polynomial * p = mk_const(tmp);
            return p;
        }

        polynomial * mk_polynomial(var x, unsigned k) {
            SASSERT(is_valid(x));
            numeral one(1);
            monomial * m = mk_monomial(x, k);
            inc_ref(m);
            return mk_polynomial_core(1, &one, &m);
        }

        polynomial * mk_polynomial(unsigned sz, numeral * as, monomial * const * ms) {
            m_som_buffer.reset();
            for (unsigned i = 0; i < sz; i++) {
                m_som_buffer.add(as[i], ms[i]);
            }
            return m_som_buffer.mk();
        }

        /**
           \brief Convert rationals into numerals at m_rat2numeral
        */
        void rational2numeral(unsigned sz, rational const * as) {
            SASSERT(m_rat2numeral.empty());
            for (unsigned i = 0; i < sz; i++) {
                SASSERT(as[i].is_int());
                m_rat2numeral.push_back(numeral());
                m_manager.set(m_rat2numeral.back(), as[i].to_mpq().numerator());
            }
        }

        void reset_tmp_as2() {
            DEBUG_CODE({
                for (unsigned i = 0; i < m_rat2numeral.size(); i++) {
                    SASSERT(m_manager.is_zero(m_rat2numeral[i]));
                }
            });
            m_rat2numeral.reset();
        }

        polynomial * mk_polynomial(unsigned sz, rational const * as, monomial * const * ms) {
            rational2numeral(sz, as);
            polynomial * p = mk_polynomial(sz, m_rat2numeral.c_ptr(), ms);
            reset_tmp_as2();
            return p;
        }

        polynomial * mk_univariate(var x, unsigned n, numeral * as) {
            SASSERT(m_cheap_som_buffer.empty());
            unsigned k = n+1;
            while (k > 0) {
                --k;
                if (m_manager.is_zero(as[k])) {
                    m_manager.del(as[k]);
                    continue;
                }
                m_cheap_som_buffer.add_reset(as[k], mk_monomial(x, k));
            }
            return m_cheap_som_buffer.mk();
        }

        polynomial * mk_univariate(var x, unsigned n, rational const * as) {
            SASSERT(is_valid(x));
            rational2numeral(n+1, as);
            polynomial * p = mk_univariate(x, n, m_rat2numeral.c_ptr());
            reset_tmp_as2();
            return p;
        }        

        polynomial * mk_linear(unsigned sz, numeral * as, var const * xs, numeral & c) {
            SASSERT(m_tmp_linear_as.empty());
            SASSERT(m_tmp_linear_ms.empty());
            for (unsigned i = 0; i < sz; i++) {
                if (m_manager.is_zero(as[i]))
                    continue;
                m_tmp_linear_as.push_back(numeral());
                swap(m_tmp_linear_as.back(), as[i]);
                m_tmp_linear_ms.push_back(mk_monomial(xs[i]));
            }
            if (!m_manager.is_zero(c)) {
                m_tmp_linear_as.push_back(numeral());
                swap(m_tmp_linear_as.back(), c);
                m_tmp_linear_ms.push_back(mk_unit());
            }
            polynomial * p = mk_polynomial(m_tmp_linear_as.size(), m_tmp_linear_as.c_ptr(), m_tmp_linear_ms.c_ptr());
            m_tmp_linear_as.reset();
            m_tmp_linear_ms.reset();
            return p;
        }

        polynomial * mk_linear(unsigned sz, rational const * as, var const * xs, rational const & c) {
            SASSERT(c.is_int());
            rational2numeral(sz, as);
            numeral tmp_c;
            m_manager.set(tmp_c, c.to_mpq().numerator());
            polynomial * p = mk_linear(sz, m_rat2numeral.c_ptr(), xs, tmp_c);
            SASSERT(m_manager.is_zero(tmp_c));
            reset_tmp_as2();
            return p;
        }
        
        
        monomial * mul(monomial const * m1, monomial const * m2) { 
            return mm().mul(m1, m2);
        }

        bool div(monomial const * m1, monomial const * m2) {
            return mm().div(m1, m2);
        }
        
        bool div(monomial const * m1, monomial const * m2, monomial * & r) {
            return mm().div(m1, m2, r);
        }

        monomial * gcd(monomial const * m1, monomial const * m2, monomial * & q1, monomial * & q2) {
            return mm().gcd(m1, m2, q1, q2);
        }

        bool unify(monomial const * m1, monomial const * m2, monomial * & q1, monomial * & q2) {
            return mm().unify(m1, m2, q1, q2);
        }

        monomial * pw(monomial const * m, unsigned k) {
            return mm().pw(m, k);
        }

        monomial * sqrt(monomial const * m) {
            return mm().sqrt(m);
        }

        polynomial * addmul(numeral const & a1, monomial const * m1, polynomial const * p1, numeral const & a2, monomial const * m2, polynomial const * p2) {
            m_som_buffer.reset();
            m_som_buffer.addmul(a1, m1, p1);
            m_som_buffer.addmul(a2, m2, p2);
            return m_som_buffer.mk();
        }

        polynomial * addmul(polynomial const * p1, numeral const & a2, monomial const * m2, polynomial const * p2) {
            numeral one(1);
            return addmul(one, mk_unit(), p1, a2, m2, p2);
        }

        polynomial * addmul(polynomial const * p1, numeral const & a2, polynomial const * p2) {
            return addmul(p1, a2, mk_unit(), p2);
        }
        
        polynomial * add(polynomial const * p1, polynomial const * p2) {
            numeral one(1);
            return addmul(one, mk_unit(), p1, one, mk_unit(), p2);
        }

        polynomial * sub(polynomial const * p1, polynomial const * p2) {
            numeral one(1);
            numeral minus_one; // It is incorrect to initialize with -1 when numeral_manager is GF_2
            m_manager.set(minus_one, -1);
            return addmul(one, mk_unit(), p1, minus_one, mk_unit(), p2);
        }

        /**
           \brief Return p1*p2 + a
        */
        polynomial * muladd(polynomial const * p1, polynomial const * p2, numeral const & a) {
            if (is_zero(p1) || is_zero(p2)) {
                return mk_const(a);
            }
            m_som_buffer.reset();
            unsigned sz1 = p1->size();
            for (unsigned i = 0; i < sz1; i++) {
                checkpoint(); 
                numeral const & a1 = p1->a(i);
                monomial * m1      = p1->m(i);
                m_som_buffer.addmul(a1, m1, p2);
            }
            m_som_buffer.add(a);
            return m_som_buffer.mk();
        }

        polynomial * mul(polynomial const * p1, polynomial const * p2) {
            numeral zero(0);
            return muladd(p1, p2, zero);
        }

        polynomial * mul(numeral const & a, monomial const * m, polynomial const * p) {
            if (m_manager.is_zero(a))
                return m_zero;
            if (m_manager.is_one(a) && m == mk_unit())
                return const_cast<polynomial*>(p);
            SASSERT(m_cheap_som_buffer.empty());
            m_cheap_som_buffer.addmul(a, m, p);
            return m_cheap_som_buffer.mk();
        }

        polynomial * mul(monomial const * m, polynomial const * p) {
            numeral one(1);
            return mul(one, m, p);
        }

        polynomial * mul(numeral const & a, polynomial const * p) {
            return mul(a, mk_unit(), p);
        }

        /**
           \brief Return a*p1*p2
        */
        polynomial * mul(numeral const & a, polynomial const * p1, polynomial const * p2) {
            if (m_manager.is_zero(a) || is_zero(p1) || is_zero(p2))
                return mk_zero();
            scoped_numeral new_a1(m_manager);
            m_som_buffer.reset();
            unsigned sz1 = p1->size();
            for (unsigned i = 0; i < sz1; i++) {
                checkpoint(); 
                numeral const & a1 = p1->a(i);
                m_manager.mul(a, a1, new_a1);
                monomial * m1      = p1->m(i);
                m_som_buffer.addmul(new_a1, m1, p2);
            }
            return m_som_buffer.mk();
        }
        
        // Divide coefficients of p by d.
        // This methods assumes that all coefficients of p are divisible by d.
        polynomial * div(polynomial * p, numeral const & d) {
            SASSERT(m_cheap_som_buffer.empty());
            unsigned sz = p->size();
            scoped_numeral a(m_manager);
            for (unsigned i = 0; i < sz; i++) {
                m_manager.div(p->a(i), d, a);
                m_cheap_som_buffer.add(a, p->m(i));
            }
            return m_cheap_som_buffer.mk();
        }

        polynomial * mul(rational const & a, polynomial const * p) {
            SASSERT(a.is_int());
            scoped_numeral tmp(m_manager);
            m_manager.set(tmp, a.to_mpq().numerator());
            polynomial * new_p = mul(tmp, p);
            return new_p;
        }
        
        /**
           \brief Return m/x^k
        */
        monomial * div_x_k(monomial const * m, var x, unsigned k) {
            return mm().div_x_k(m, x, k);
        }

        /**
           \brief Return m/x^n  where n == m->degree_of(x)  
        */
        monomial * div_x(monomial const * m, var x) {
            return mm().div_x(m, x);
        }

        bool is_p_normalized(polynomial const * p) const {
            for (unsigned i = 0; i < p->size(); i++) {
                SASSERT(m().is_p_normalized(p->a(i)));
            }
            return true;
        }

        /**
           \brief (Incremental) Newton interpolation for multivariate polynomials.
           Creates a polynomial on x of degree at most d with coefficients in Z[y1, ..., ym], 
           using d+1 sample points.
           Sample points are provided using the method add, and the interpolating polynomial
           is created using mk() method.

           \pre manager must be configured in Zp (modular) mode.
           We need this requeriment because we use the inverse operation.
        */
        class newton_interpolator {
            imp &                 pm;
            scoped_numeral_vector m_inputs;
            scoped_numeral_vector m_invs;
            polynomial_ref_vector m_vs;
            mpzzp_manager & m() const { return pm.m(); }
        public:
            newton_interpolator(imp & _pm):pm(_pm), m_inputs(m()), m_invs(m()), m_vs(pm.m_wrapper) {
                m_invs.push_back(numeral(0));
            }
            
            void reset() { 
                m_inputs.reset();
                m_invs.shrink(1); 
                m_vs.reset(); 
                SASSERT(m().is_zero(m_invs[0])); 
            }

            scoped_numeral_vector const & inputs() const { return m_inputs; }

            unsigned num_sample_points() const { return m_inputs.size(); }
            
            /**
               \brief Add a new datapoint
            */
            void add(numeral const & input, polynomial const * output) {
                TRACE("newton", tout << m().to_string(input) << " -> "; output->display(tout, m()); tout << "\n";);
                SASSERT(m().modular());
                unsigned sz = num_sample_points();
                if (sz > 0) {
                    unsigned k = sz;
                    // add new inverse
                    scoped_numeral product(m());
                    scoped_numeral aux(m());
                    SASSERT(!m().eq(input, m_inputs[0]));
                    m().sub(input, m_inputs[0], product);
                    for (unsigned i = 1; i <= k - 1; i++) {
                        SASSERT(!m().eq(input, m_inputs[i]));
                        m().sub(input, m_inputs[i], aux);
                        m().mul(product, aux, product);
                    }
                    m().inv(product);
                    m_inputs.push_back(input);
                    m_invs.push_back(product);
                    TRACE("newton", tout << "invs[" << k << "]: " << product << "\n";);
                    SASSERT(m().eq(m_inputs[k], input));
                    // Compute newton's coefficient
                    polynomial_ref temp(pm.m_wrapper);
                    polynomial_ref aux_poly(pm.m_wrapper);
                    temp = m_vs.get(k-1);
                    for (int j = k - 2; j >= 0; j--) {
                        // temp <- temp*(input - m_inputs[j]) + vs[j]
                        m().sub(input, m_inputs[j], aux);
                        SASSERT(m().is_p_normalized(aux));
                        aux_poly = pm.mul(aux, temp);
                        temp     = pm.add(aux_poly, m_vs.get(j));
                        SASSERT(pm.is_p_normalized(temp));
                    }
                    // new vs <- (output - temp)*invs[sz]
                    aux_poly = pm.sub(output, temp);
                    SASSERT(pm.is_p_normalized(aux_poly));
                    aux_poly = pm.mul(m_invs[sz], aux_poly);
                    SASSERT(pm.is_p_normalized(aux_poly));
                    m_vs.push_back(aux_poly);
                    TRACE("newton", tout << "vs[" << k << "]: " << aux_poly << "\n";);
                }
                else {
                    m_inputs.push_back(input);
                    m_vs.push_back(const_cast<polynomial*>(output));
                }
            }
               
            // Convert newton form to standard form
            void mk(var x, polynomial_ref & r) {
                SASSERT(m().modular());
                polynomial_ref u(pm.m_wrapper);
                polynomial_ref aux_poly(pm.m_wrapper);
                int num = num_sample_points();
                int d   = num - 1;
                SASSERT(num > 0);
                u = m_vs.get(d);
                scoped_numeral c(m());
                for (int k = d - 1; k >= 0; k--) {
                    TRACE("newton", tout << "u: " << u << "\n";);
                    // create polynomial (x - inputs[k])
                    m().set(c, m_inputs[k]);
                    m().neg(c);
                    numeral one(1);
                    aux_poly = pm.mk_linear(1, &one, &x, c);
                    TRACE("newton", tout << "(x - inputs[k]): " << aux_poly << "\n";);
                    // u <- u * (x - inputs[k]) + vs[k]
                    aux_poly = pm.mul(u, aux_poly);
                    u        = pm.add(aux_poly, m_vs.get(k));
                }
                TRACE("newton", tout << "result u: " << u << "\n";);
                r = u;
            }
        };
       
        /**
           \brief Newton interpolation for multivariate polynomials.
           Creates a polynomial on x of degree at most d with coefficients in Z[y1, ..., ym], 
           using d+1 sample points.
           The sample points are store in the vectors inputs and outputs. Both must have size d+1.
           
           \pre manager must be configured in Zp (modular) mode.
           We need this requeriment because we use the inverse operation.
        */
        void newton_interpolation(var x, unsigned d, numeral const * inputs, polynomial * const * outputs, polynomial_ref & r) {
            SASSERT(m().modular());
            newton_interpolator interpolator(*this);
            for (unsigned i = 0; i <= d; i++)
                interpolator.add(inputs[i], outputs[i]);
            interpolator.mk(x, r);
        }

        class newton_interpolator_vector {
            imp *                           m_imp;
            ptr_vector<newton_interpolator> m_data;
        public:
            newton_interpolator_vector():m_imp(0) {}

            ~newton_interpolator_vector() {
                flush();
            }

            void flush() {
                unsigned sz = m_data.size();
                for (unsigned i = 0; i < sz; i++)
                    dealloc(m_data[i]);
                m_data.reset();
            }

            void set_owner(imp * owner) {
                SASSERT(m_imp == 0 || m_imp == owner);
                m_imp = owner;
            }

            newton_interpolator & operator[](unsigned idx) {
                SASSERT(m_imp);
                while (idx >= m_data.size()) {
                    m_data.push_back(alloc(newton_interpolator, *m_imp));
                }
                return *(m_data[idx]);
            }
        };

        /**
           \brief Represents a polynomial skeleton of a multivariate polynomial Z[Y1, ..., Yn]
           with coefficients in Z[X]
        */
        struct skeleton {
            struct entry {
                monomial * m_monomial; // a monomial in Z[Y1, ..., Y1]
                unsigned   m_first_power_idx; // position (in m_powers) of the powers of X that are the coefficient of this monomial
                unsigned   m_num_powers; // size of the coefficient of this monomial.
                entry(monomial * m, unsigned first_idx):
                    m_monomial(m),
                    m_first_power_idx(first_idx),
                    m_num_powers(1) {
                }
                unsigned num_powers() const { return m_num_powers; }
                monomial * m() const { return m_monomial; }
            };
            imp &                pm;
            var                  m_x;
            svector<entry>       m_entries;     
            unsigned_vector      m_powers;
            ptr_vector<monomial> m_orig_monomials;
            unsigned             m_max_powers; // maximal number of powers associated with an entry 
            
            skeleton(imp & _pm, polynomial * p, var x):pm(_pm), m_x(x) {
                m_max_powers = 0;
                ptr_buffer<monomial, 128> ms;
                unsigned sz = p->size();
                for (unsigned i = 0; i < sz; i++) {
                    ms.push_back(p->m(i));
                }
                std::sort(ms.begin(), ms.end(), lex_lt2(x));
                monomial * prev = 0;
                for (unsigned i = 0; i < sz; i++) {
                    monomial * orig_m = ms[i];
                    monomial * m;
                    unsigned   k = orig_m->degree_of(x);
                    if (k > 0) 
                        m = pm.div_x(orig_m, x);
                    else
                        m = orig_m;
                    if (m == prev) {
                        unsigned & num_powers = m_entries.back().m_num_powers;
                        num_powers++;
                        if (num_powers > m_max_powers)
                            m_max_powers = num_powers;
                    }
                    else {
                        prev = m;
                        pm.inc_ref(m);
                        m_entries.push_back(entry(m, m_powers.size()));
                        if (m_max_powers == 0)
                            m_max_powers = 1;
                    }
                    pm.inc_ref(orig_m);
                    m_orig_monomials.push_back(orig_m);
                    m_powers.push_back(k);
                }
                TRACE("skeleton", 
                      tout << "x: x" << m_x << "\n";
                      tout << "max: " << m_max_powers << "\n";
                      tout << "p: "; p->display(tout, pm.m()); tout << "\n";
                      tout << "skeleton: "; display(tout); tout << "\n";);
                DEBUG_CODE({
                    unsigned sz = m_entries.size();
                    for (unsigned i = 1; i < sz; i++) {
                        SASSERT(lex_compare(m_entries[i-1].m_monomial, m_entries[i].m_monomial) < 0);
                    }
                });
            }

            ~skeleton() {
                unsigned sz = m_entries.size();
                for (unsigned i = 0; i < sz; i++) {
                    pm.dec_ref(m_entries[i].m_monomial);
                }
                sz = m_orig_monomials.size();
                for (unsigned i = 0; i < sz; i++) {
                    pm.dec_ref(m_orig_monomials[i]);
                }
            }

            unsigned get_entry_idx(monomial * m) {
                unsigned sz = m_entries.size();
                for (unsigned i = 0; i < sz; i++) {
                    if (m_entries[i].m_monomial == m)
                        return i;
                }
                return UINT_MAX;
            }

            unsigned num_entries() const { return m_entries.size(); }

            entry const & operator[](unsigned idx) const { return m_entries[idx]; }

            unsigned ith_power(entry const & e, unsigned i) const { SASSERT(i < e.m_num_powers); return m_powers[e.m_first_power_idx + i]; }
            
            monomial * ith_orig_monomial(entry const & e, unsigned i) const { SASSERT(i < e.m_num_powers); return m_orig_monomials[e.m_first_power_idx + i]; }

            unsigned max_num_powers() const { return m_max_powers; }

            void display(std::ostream & out) {
                unsigned sz = m_entries.size();
                for (unsigned i = 0; i < sz; i++) {
                    entry & e = m_entries[i];
                    if (i > 0) out << " ";
                    out << "(";
                    for (unsigned j = 0; j < e.m_num_powers; j++) {
                        if (j > 0) out << " ";
                        out << "x" << m_x << "^";
                        out << m_powers[e.m_first_power_idx + j];
                    }
                    out << ")*";
                    e.m_monomial->display(out);
                }
            }
        };

        class sparse_interpolator {
            skeleton *      m_skeleton;
            numeral_vector  m_inputs;
            numeral_vector  m_outputs;
        public:
            sparse_interpolator(skeleton * sk):m_skeleton(sk) {
                // reserve space output values associated with each entry
                if (sk) {
                    unsigned sz = sk->num_entries();
                    for (unsigned i = 0; i < sz; i++) {
                        unsigned num_powers = (*sk)[i].num_powers();
                        for (unsigned j = 0; j < num_powers; j++) {
                            m_outputs.push_back(numeral());
                        }
                    }
                }
            }
            
            ~sparse_interpolator() {
                if (m_skeleton) {
                    numeral_manager & m = m_skeleton->pm.m();
                    for (unsigned i = 0; i < m_inputs.size(); i++)
                        m.del(m_inputs[i]);
                    for (unsigned i = 0; i < m_outputs.size(); i++)
                        m.del(m_outputs[i]);
                }
            }
            
            void reset() {
                numeral_manager & m = m_skeleton->pm.m();
                for (unsigned i = 0; i < m_inputs.size(); i++) {
                    m.del(m_inputs[i]);
                }
                m_inputs.reset();
            }

            bool ready() const {
                return m_inputs.size() == m_skeleton->max_num_powers();
            }

            bool add(numeral const & in, polynomial const * q) {
                SASSERT(m_skeleton);
                SASSERT(m_inputs.size() < m_skeleton->max_num_powers());
                numeral_manager & m = m_skeleton->pm.m();
                unsigned input_idx = m_inputs.size();
                m_inputs.push_back(numeral());
                m.set(m_inputs.back(), in);
                unsigned sz = q->size();
                for (unsigned i = 0; i < sz; i++) {
                    monomial * mon = q->m(i);
                    unsigned entry_idx = m_skeleton->get_entry_idx(mon);
                    if (entry_idx == UINT_MAX)
                        return false;
                    skeleton::entry const & e = (*m_skeleton)[entry_idx];
                    if (input_idx >= e.num_powers())
                        continue;
                    unsigned output_idx = e.m_first_power_idx + input_idx;
                    m.set(m_outputs[output_idx], q->a(i));
                }
                return true;
            }
            
            bool mk(polynomial_ref & r) {
                SASSERT(m_skeleton);
                numeral_manager & m = m_skeleton->pm.m();
                scoped_numeral_vector           cs(m);
                scoped_numeral_vector           new_as(m);
                scoped_numeral_vector           as(m);
                ptr_buffer<monomial,128>        mons;
                scoped_numeral                  aux(m);
                linear_eq_solver<mpzzp_manager> solver(m);
                unsigned sz = m_skeleton->num_entries();
                for (unsigned k = 0; k < sz; k++) {
                    skeleton::entry const & e = (*m_skeleton)[k];
                    unsigned num_pws = e.num_powers();
                    solver.resize(num_pws);
                    new_as.resize(num_pws);
                    for (unsigned i = 0; i < num_pws; i++) {
                        numeral & in = m_inputs[i];
                        cs.reset();
                        for (unsigned j = 0; j < num_pws; j++) {
                            m.power(in, m_skeleton->ith_power(e, j), aux);
                            cs.push_back(aux);
                        }
                        unsigned output_idx = e.m_first_power_idx + i;
                        TRACE("sparse_interpolator", tout << "adding new equation:\n";
                              for (unsigned i = 0; i < num_pws; i++) {
                                  tout << m.to_string(cs[i]) << " ";
                              }
                              tout << "\n";);
                        solver.add(i, cs.c_ptr(), m_outputs[output_idx]);
                    }
                    TRACE("sparse_interpolator", 
                          tout << "find coefficients of:\n";
                          for (unsigned i = 0; i < num_pws; i++) {
                              m_skeleton->ith_orig_monomial(e, i)->display(tout); tout << "\n";
                          }
                          tout << "system of equations:\n";
                          solver.display(tout););
                    if (!solver.solve(new_as.c_ptr())) 
                        return false;
                    for (unsigned i = 0; i < num_pws; i++) {
                        if (!m.is_zero(new_as[i])) {
                            as.push_back(new_as[i]);
                            mons.push_back(m_skeleton->ith_orig_monomial(e, i));
                        }
                    }
                }
                r = m_skeleton->pm.mk_polynomial(as.size(), as.c_ptr(), mons.c_ptr());
                return true;
            }
        };

        svector<bool>  m_found_vars;
        void vars(polynomial const * p, var_vector & xs) {
            xs.reset();
            m_found_vars.reserve(num_vars(), false);
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                monomial * m = p->m(i);
                unsigned msz = m->size();
                for (unsigned j = 0; j < msz; j++) {
                    var x = m->get_var(j);
                    if (!m_found_vars[x]) {
                        m_found_vars[x] = true;
                        xs.push_back(x);
                    }
                }
            }
            // reset m_found_vars
            sz = xs.size();
            for (unsigned i = 0; i < sz; i++)
                m_found_vars[xs[i]] = false;
        }

        typedef sbuffer<power, 32>    power_buffer;
        typedef sbuffer<unsigned, 32> unsigned_buffer;
        typedef sbuffer<var, 32>      var_buffer;
        
        /**
           Store in pws the variables occuring in p and their (minimal or maximal) degrees.
        */
        unsigned_vector m_var_degrees_tmp;
        template<bool Max>
        void var_degrees(polynomial const * p, power_buffer & pws) {
            pws.reset();
            unsigned_vector & var2pos = m_var_degrees_tmp;
            var2pos.reserve(num_vars(), UINT_MAX);
            
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                monomial * m = p->m(i);
                unsigned msz = m->size();
                for (unsigned j = 0; j < msz; j++) {
                    var x        = m->get_var(j);
                    unsigned k   = m->degree(j);
                    unsigned pos = var2pos[x];
                    if (pos == UINT_MAX) {
                        var2pos[x] = pws.size();
                        pws.push_back(power(x, k));
                    }
                    else if (Max && k > pws[pos].degree()) {
                        pws[pos].degree() = k;
                    }
                    else if (!Max && k < pws[pos].degree()) {
                        pws[pos].degree() = k;
                    }
                }
            }
            
            sz = pws.size();
            for (unsigned i = 0; i < sz; i++) {
                SASSERT(var2pos[pws[i].get_var()] != UINT_MAX);
                var2pos[pws[i].get_var()] = UINT_MAX;
            }

            DEBUG_CODE({
                for (unsigned i = 0; i < pws.size(); i++) {
                    for (unsigned j = i + 1; j < pws.size(); j++)
                        SASSERT(pws[i].first != pws[j].first);
                }
            });
        }

        void var_max_degrees(polynomial const * p, power_buffer & pws) {
            var_degrees<true>(p, pws);
        }

        void var_min_degrees(polynomial const * p, power_buffer & pws) {
            var_degrees<false>(p, pws);
        }

        polynomial * coeff(polynomial const * p, var x, unsigned k) {
            SASSERT(is_valid(x));
            SASSERT(m_cheap_som_buffer.empty());
            TRACE("coeff_bug", tout << "p: "; p->display(tout, m_manager); tout << "\nx: " << x << ", k: " << k << "\n";);
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                monomial * m = p->m(i);
                unsigned   d = m->degree_of(x);
                if (d == k)
                    m_cheap_som_buffer.add(p->a(i), div_x(m, x));
            }
            return m_cheap_som_buffer.mk();
        }

        /**
           Let p be of the form q_k(yvec)*x^k +  ...+ q_0(yvec)
           Store the polynomials q_k(yvec), ..., q_0(yvec) in the som_buffer_vector.
        */
        void coeffs(polynomial const * p, var x, som_buffer_vector & cs) {
            cs.set_owner(this);
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                monomial * m   = p->m(i);
                unsigned     d = m->degree_of(x);
                som_buffer * c = cs[d]; 
                c->add(p->a(i), div_x(m, x));
            }
        }

        /**
           \brief Return a polynomial h that is the coefficient of x^k in p.
           Store the reduct (p - h x^k) into \c reduct.
        */
        polynomial * coeff(polynomial const * p, var x, unsigned k, polynomial_ref & reduct) {
            SASSERT(is_valid(x));
            SASSERT(m_cheap_som_buffer.empty());
            SASSERT(m_cheap_som_buffer2.empty());
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                monomial * m = p->m(i);
                unsigned   d = m->degree_of(x);
                if (d == k)
                    m_cheap_som_buffer.add(p->a(i), div_x(m, x));
                else
                    m_cheap_som_buffer2.add(p->a(i), m);
            }
            reduct = m_cheap_som_buffer2.mk();
            return m_cheap_som_buffer.mk();
        }
        
        /**
           \brief Return true if the coefficient of x^k is just a constant.
           Store it in c.
         */
        bool const_coeff(polynomial const * p, var x, unsigned k, numeral & c) {
            SASSERT(is_valid(x));
            m_manager.reset(c);
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                monomial * m = p->m(i);
                unsigned   d = m->degree_of(x);
                if (d == k) {
                    unsigned msz = m->size();
                    if ((k > 0 && msz > 1) || (k == 0 && msz > 0))
                        return false;
                    m_manager.set(c, p->a(i));
                }
            }
            return true;
        }

        bool nonzero_const_coeff(polynomial const * p, var x, unsigned k) {
            scoped_numeral c(m_manager);
            return const_coeff(p, x, k, c) && !m_manager.is_zero(c);
        }

        /**
           \brief Extract the integer content of p.
        */
        void ic(polynomial const * p, numeral & a) {
            if (is_zero(p)) {
                m_manager.reset(a);
                return;
            }
            if (is_const(p)) {
                m_manager.set(a, p->a(0));
                return;
            }
            m_manager.set(a, p->a(0));
            unsigned sz = p->size();
            for (unsigned i = 1; i < sz; i++) {
                if (m_manager.is_one(a))
                    return;
                m_manager.gcd(a, p->a(i), a);
            }
        }

        /**
           \brief Sum of the absolute values of the coefficients.
        */
        void abs_norm(polynomial const * p, numeral & norm) {
            m_manager.reset(norm);
            scoped_numeral tmp(m_manager);
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; ++ i) {
                m_manager.set(tmp, p->a(i));
                m_manager.abs(tmp);
                m_manager.add(norm, tmp, norm);
            }
        }

        /**
           \brief Arbitrary leading integer coefficient.
        */
        numeral const & numeral_lc(polynomial const * p, var x) {
            int sz = p->size();
            if (sz == 0) {
                return m_zero_numeral;
            } else {
                return p->a(0);
            }
        }

        numeral const & numeral_tc(polynomial const * p) {
            int sz = p->size();
            if (sz == 0) {
                return m_zero_numeral;
            } 
            else {
                monomial * u = mk_unit();
                for (int i = 0; i < sz; ++ i) {
                    if (p->m(i) == u)
                        return p->a(i);
                }
                return m_zero_numeral;
            }
        }

        /**
           \brief Extract the integer content of p.
           p = a*c s.t. the GCD of the coefficients of c is one.
        */
        void ic(polynomial const * p, numeral & a, polynomial_ref & c) {
            if (is_zero(p)) {
                m_manager.reset(a);
                c = const_cast<polynomial*>(p);
                return;
            }
            if (is_const(p)) {
                m_manager.set(a, p->a(0));
                c = mk_one();
                return;
            }
            unsigned sz = p->size();
            m_manager.gcd(sz, p->as(), a);
            if (m_manager.is_one(a)) {
                c = const_cast<polynomial*>(p);
                return;
            } 
            m_cheap_som_buffer.reset();
            scoped_numeral ai(m_manager);
            for (unsigned i = 0; i < sz; i++) {
                monomial * m = p->m(i);
                m_manager.div(p->a(i), a, ai);
                m_cheap_som_buffer.add_reset(ai, m);
            }
            c = m_cheap_som_buffer.mk();
        }

        // Flip the sign of p, if the leading monomial is negative
        polynomial * flip_sign_if_lm_neg_core(polynomial const * p) {
            if (is_zero(p))
                return const_cast<polynomial*>(p);
            unsigned glex_max_pos = p->graded_lex_max_pos();
            SASSERT(glex_max_pos != UINT_MAX);
            if (m_manager.is_neg(p->a(glex_max_pos)))
                return neg(p);
            else 
                return const_cast<polynomial*>(p);
        }

        void flip_sign_if_lm_neg(polynomial_ref & p) {
            p = flip_sign_if_lm_neg_core(p);
        }
        
        /**
           \brief Extract the integer content, content and primitive part of p with respect to
           variable x.
        */
        void iccp(polynomial const * p, var x, numeral & i, polynomial_ref & c, polynomial_ref & pp) {
            TRACE("polynomial", tout << "iccp x" << x << "\n"; p->display(tout, m_manager); tout << "\n";);
            if (is_zero(p)) {
                m_manager.set(i, 0);
                c  = mk_one();
                pp = const_cast<polynomial*>(p);
                return;
            }
            if (is_const(p)) {
                m_manager.set(i, p->a(0));
                c  = mk_one();
                pp = mk_one();
                return;
            }
            unsigned d = degree(p, x);
            if (d == 0) {
                ic(p, i, c);
                pp = mk_one();
                return;
            }
            // Apply filter and collect powers of x occuring in p
            // The quick filter is the following:
            //   If p contains a monomial x^k and no monomial of the form m*x^k m != 1, then
            //      c = m_unit_poly
            //   To detect that we use a map (iccp_powers) from k to counters.
            //   We traverse p and update the map using the following rules:
            //      - found monomial x^k then iccp_powers[k]++;
            //      - found monomial m*x^k then iccp_powers[k]+=2;
            //   If after traversing p, there is a k s.t. iccp_powers[k] == 1, we know c == 1
            // We store iccp_powers the powers of x occuring in p.
            sbuffer<unsigned, 128> iccp_filter;
            sbuffer<unsigned, 128> iccp_powers;
            iccp_filter.resize(d+1, 0);
            iccp_powers.reset();
            for (unsigned j = 0; j <= d; j++)
                iccp_filter[j] = 0; 
            unsigned sz = p->size();
            for (unsigned j = 0; j < sz; j++) {
                monomial * m = p->m(j);
                unsigned   k = m->degree_of(x);
                TRACE("polynomial", tout << "degree of x" << x << " at "; m->display(tout); tout << " is " << k << "\n";);
                if (iccp_filter[k] == 0)
                    iccp_powers.push_back(k);
                if (m->size() == (k > 0 ? 1 : 0)) 
                    iccp_filter[k]++;
                else
                    iccp_filter[k]+=2;
            }
            SASSERT(!iccp_powers.empty());
            unsigned num_powers = iccp_powers.size();
            for (unsigned j = 0; j < num_powers; j++) {
                SASSERT(iccp_filter[iccp_powers[j]] > 0);
                if (iccp_filter[iccp_powers[j]] == 1) {
                    ic(p, i, pp);
                    c = mk_one();
                    return;
                }
            }
            // Extract integer content
            ic(p, i, pp);
            TRACE("polynomial", tout << "p: "; p->display(tout, m_manager); tout << "\ni: " << m_manager.to_string(i) << "\npp: " << pp << "\n";);
            // Compute c using the gcd of coeffs of x^k for k's in iccp_powers            
            polynomial_ref ci(pm());
            c = coeff(pp, x, iccp_powers[0]);
            for (unsigned j = 1; j < num_powers; j++) {
                ci = coeff(pp, x, iccp_powers[j]);
                gcd(c, ci, c);
                if (is_const(c)) {
                    c = mk_one();
                    return;
                }
            }
            SASSERT(!is_const(c));
            // make sure the sign of the leading monomial is positive
            flip_sign_if_lm_neg(c);
            TRACE("polynomial", tout << "pp: " << pp << "\nc: " << c << "\n";);
            pp = exact_div(pp, c);
        }
        
        void iccp(polynomial const * p, numeral & i, polynomial_ref & c, polynomial_ref & pp) {
            iccp(p, max_var(p), i, c, pp);
        }

        void pp(polynomial const * p, var x, polynomial_ref & pp) {
            scoped_numeral i(m_manager);
            polynomial_ref c(pm());
            iccp(p, x, i, c, pp);
        }

        bool is_primitive(polynomial const * p, var x) {
            scoped_numeral i(m_manager);
            polynomial_ref c(pm());
            polynomial_ref pp(pm());
            iccp(p, x, i, c, pp);
            return eq(p, pp);
        }

        polynomial * lc(polynomial const * p, var x) {
            return coeff(p, x, degree(p, x));
        }

        void gcd_prs(polynomial const * u, polynomial const * v, var x, polynomial_ref & r) {
            TRACE("polynomial_gcd", tout << "gcd prs with x" << x << " for\nu: "; 
                  u->display(tout, m_manager); tout << "\nv: "; v->display(tout, m_manager); tout << "\n";);
            if (degree(u, x) < degree(v, x))
                std::swap(u, v);
            scoped_numeral i_u(m_manager), i_v(m_manager);
            polynomial_ref c_u(pm()), c_v(pm());
            polynomial_ref pp_u(pm()), pp_v(pm());
            scoped_numeral d_a(m_manager);
            polynomial_ref d_r(pm());
            polynomial_ref g(pm()), h(pm()), rem(pm()), new_h(pm());
            
            iccp(u, x, i_u, c_u, pp_u);
            iccp(v, x, i_v, c_v, pp_v);
            
            gcd(c_u, c_v, d_r);
            m_manager.gcd(i_u, i_v, d_a);
            TRACE("polynomial_gcd_detail", 
                  tout << "After GCD of the content\n";
                  tout << "u: "; u->display(tout, m_manager); tout << "\n";
                  tout << "v: "; v->display(tout, m_manager); tout << "\n";
                  tout << "i_u: " << i_u << "\n";
                  tout << "i_v: " << i_v << "\n";
                  tout << "c_u: " << c_u << "\n";
                  tout << "c_v: " << c_v << "\n";
                  tout << "pp_u: " << pp_u << "\n";
                  tout << "pp_v: " << pp_v << "\n";
                  tout << "d_r: " << d_r << "\nd_a: " << d_a << "\n";);
            
            g = mk_one();
            h = mk_one();
            
            unsigned counter = 0;
            while (true) {
                SASSERT(degree(pp_u, x) >= degree(pp_v, x));
                unsigned delta = degree(pp_u, x) - degree(pp_v, x);
                TRACE("polynomial_gcd_detail", 
                      tout << "iteration: " << counter << "\n";
                      tout << "gcd loop\npp_u: " << pp_u << "\npp_v: " << pp_v << "\ndelta: " << delta << "\n";);
                counter++;
                exact_pseudo_remainder(pp_u, pp_v, x, rem);
                if (is_zero(rem)) {
                    TRACE("polynomial", tout << "rem is zero...\npp_v: " << pp_v << "\n";);
                    flip_sign_if_lm_neg(pp_v);
                    pp(pp_v, x, r);
                    r = mul(d_a, d_r, r);
                    return;
                }
                if (is_const(rem)) {
                    TRACE("polynomial", tout << "rem is a constant: " << rem << "\nr: " << d_r << "\nd_a: " << d_a << "\n";);
                    r = mul(d_a, d_r);
                    return;
                }
                pp_u = pp_v;
                // pp_v <- rem/g*h^{delta}
                pp_v = exact_div(rem, g);
                // delta is usually a small number, so I do not compute h^delta
                for (unsigned i = 0; i < delta; i++)
                    pp_v = exact_div(pp_v, h);
                g   = lc(pp_u, x);
                // h <- h^{1-delta}*g^{delta}
                new_h = mk_one();
                for (unsigned i = 0; i < delta; i++)
                    new_h = mul(new_h, g);
                if (delta > 1) {
                    for (unsigned i = 0; i < delta - 1; i++)
                        new_h = exact_div(new_h, h);
                }
                h = new_h;
            }
        }            

        // Store in r <- gcd(content(u, x), v)
        void gcd_content(polynomial const * u, var x, polynomial const * v, polynomial_ref & r) {
            scoped_numeral i_u(m_manager);
            polynomial_ref c_u(pm());
            polynomial_ref pp_u(pm());
            
            iccp(u, x, i_u, c_u, pp_u);
            c_u = mul(i_u, c_u);
            gcd(c_u, v, r);
        }

        // TODO: implement euclid algorithm when m_manager in Zp mode
        void euclid_gcd(polynomial const * u, polynomial const * v, polynomial_ref & r) {
            SASSERT(m().modular());
            CTRACE("mgcd", !is_univariate(u) || !is_univariate(v),
                   tout << "euclid_gcd, polynomials are not univariate\n"; u->display(tout, m()); tout << "\n"; v->display(tout, m()); tout << "\n";);
            SASSERT(is_univariate(u));
            SASSERT(is_univariate(v));
            if (is_zero(u)) {
                r = const_cast<polynomial*>(v); 
                flip_sign_if_lm_neg(r);
                return;
            }
            if (is_zero(v)) {
                r = const_cast<polynomial*>(u);
                flip_sign_if_lm_neg(r);
                return;
            }
            if (u == v) {
                r = const_cast<polynomial*>(u);
                flip_sign_if_lm_neg(r);
                return;
            }
            if (is_const(u) || is_const(v)) { 
                scoped_numeral i_u(m_manager), i_v(m_manager);
                ic(v, i_v);
                ic(u, i_u);
                scoped_numeral a(m_manager);
                m_manager.gcd(i_v, i_u, a);
                r = mk_const(a);
                return;
            }
           // Maybe map it to univariate case
            gcd_prs(u, v, max_var(u), r);
        }

        // Combine two different modular images using Chinese Remainder theorem
        // The new bound is stored in b2
        void CRA_combine_images(polynomial const * C1, scoped_numeral const & b1, polynomial const * C2, scoped_numeral & b2, polynomial_ref & r) {
            lex_sort(C1);
            lex_sort(C2);
            TRACE("CRA", tout << "C1: "; C1->display(tout, m()); tout << "\nC2: "; C2->display(tout, m()); tout << "\n";);
            SASSERT(m_cheap_som_buffer.empty());
            SASSERT(!m().m().is_even(b1));
            SASSERT(!m().m().is_even(b2));
            cheap_som_buffer & R = m_cheap_som_buffer;
            scoped_numeral inv1(m());
            scoped_numeral inv2(m());
            scoped_numeral g(m());
            m().gcd(b1, b2, inv1, inv2, g);
            SASSERT(m().is_one(g));
            TRACE("CRA", tout << "b1: " << b1 << ", b2: " << b2 << ", inv1: " << inv1 << ", inv2: " << inv2 << "\n";);
            // b1*inv1 + b2.inv2 = 1
            // inv1 is the inverse of b1 mod b2
            // inv2 is the inverse of b2 mod b1
            m().m().mod(inv1, b2, inv1);
            m().m().mod(inv2, b1, inv2);
            TRACE("CRA", tout << "inv1: " << inv1 << ", inv2: " << inv2 << "\n";);
            scoped_numeral a1(m());
            scoped_numeral a2(m());
            m().mul(b2, inv2, a1); // a1 is the multiplicator for coefficients of C1
            m().mul(b1, inv1, a2); // a2 is the multiplicator for coefficients of C2 
            TRACE("CRA", tout << "a1: " << a1 << ", a2: " << a2 << "\n";);
            // new bound
            scoped_numeral new_bound(m());
            m().mul(b1, b2, new_bound);   
            scoped_numeral lower(m());
            scoped_numeral upper(m());
            scoped_numeral new_a(m()), tmp1(m()), tmp2(m()), tmp3(m());
            m().div(new_bound, 2, upper); 
            m().set(lower, upper);
            m().neg(lower);
            TRACE("CRA", tout << "lower: " << lower << ", upper: " << upper << "\n";);

            #define ADD(A1, A2, M) {                    \
                m().mul(A1, a1, tmp1);                  \
                m().mul(A2, a2, tmp2);                  \
                m().add(tmp1, tmp2, tmp3);              \
                m().m().mod(tmp3, new_bound, new_a);    \
                if (m().gt(new_a, upper))               \
                    m().sub(new_a, new_bound, new_a);   \
                R.add(new_a, M);                        \
            }
            
            numeral zero(0);
            unsigned i1  = 0;
            unsigned i2  = 0;
            unsigned sz1 = C1->size();
            unsigned sz2 = C2->size();
            while (true) {
                if (i1 == sz1) {
                    while (i2 < sz2) {
                        TRACE("CRA", tout << "adding C2 rest\n";);
                        ADD(zero, C2->a(i2), C2->m(i2));
                        i2++;
                    }
                    break;
                }
                if (i2 == sz2) {
                    while (i1 < sz1) {
                        TRACE("CRA", tout << "adding C1 rest\n";);
                        ADD(C1->a(i1), zero, C1->m(i1));
                        i1++;
                    }
                    break;
                }
                monomial * m1 = C1->m(i1);
                monomial * m2 = C2->m(i2);
                int s = lex_compare(m1, m2);
                if (s == 0) {
                    ADD(C1->a(i1), C2->a(i2), m1);
                    TRACE("CRA", 
                          tout << "C1->a(i1): " << m().to_string(C1->a(i1)) << ", C2->a(i2): " << m().to_string(C2->a(i2)) << ", new_a: " << new_a << "\n";
                          tout << "tmp1: " << tmp1 << ", tmp2: " << tmp2 << ", tmp3: " << tmp3 << "\n";);
                    i1++;
                    i2++;
                }
                else if (s > 0) {
                    TRACE("CRA", tout << "C1 mon biggerr, adding it...\n";);
                    ADD(C1->a(i1), zero, m1);
                    i1++;
                }
                else {
                    TRACE("CRA", tout << "C2 mon bigger, adding it...\n";);
                    ADD(zero, C2->a(i2), m2);
                    i2++;
                }
            }
            m().set(b2, new_bound);
            r  = R.mk();
        }

        void uni_mod_gcd(polynomial const * u, polynomial const * v, polynomial_ref & r) {
            TRACE("mgcd", tout << "univ_modular_gcd\nu: "; u->display(tout, m_manager); tout << "\nv: "; v->display(tout, m_manager); tout << "\n";);
            SASSERT(!m().modular());
            SASSERT(is_univariate(u));
            SASSERT(!is_const(u) && !is_const(v));
            SASSERT(max_var(u) == max_var(v));
            var x = max_var(u);
            scoped_numeral c_u(m()), c_v(m());
            polynomial_ref pp_u(pm()), pp_v(pm());
            ic(u, c_u, pp_u);
            ic(v, c_v, pp_v);
            
            scoped_numeral d_a(m());
            m_manager.gcd(c_u, c_v, d_a);
            
            scoped_numeral lc_u(m());
            scoped_numeral lc_v(m());
            unsigned d_u = degree(pp_u, x);
            unsigned d_v = degree(pp_v, x);
            lc_u = univ_coeff(pp_u, d_u);
            lc_v = univ_coeff(pp_v, d_v);
            scoped_numeral lc_g(m());
            m().gcd(lc_u, lc_v, lc_g);
            
            polynomial_ref u_Zp(m_wrapper);
            polynomial_ref v_Zp(m_wrapper);

            polynomial_ref C_star(m_wrapper);
            scoped_numeral bound(m());
            polynomial_ref q(m_wrapper);

            polynomial_ref candidate(m_wrapper);

            scoped_numeral p(m());
            for (unsigned i = 0; i < NUM_BIG_PRIMES; i++) {
                m().set(p, g_big_primes[i]);
                TRACE("mgcd", tout << "trying prime: " << p << "\n";);
                {
                    scoped_set_zp setZp(m_wrapper, p);
                    u_Zp = normalize(pp_u);
                    v_Zp = normalize(pp_v);
                    if (degree(u_Zp, x) < d_u) {
                        TRACE("mgcd", tout << "bad prime, leading coefficient vanished\n";);
                        continue; // bad prime
                    }
                    if (degree(v_Zp, x) < d_v) {
                        TRACE("mgcd", tout << "bad prime, leading coefficient vanished\n";);
                        continue; // bad prime
                    }
                    euclid_gcd(u_Zp, v_Zp, q);
                    // normalize so that lc_g is leading coefficient of q
                    q = mk_glex_monic(q);
                    scoped_numeral c(m());
                    m().set(c, lc_g);
                    q = mul(c, q);
                }
                TRACE("mgcd", tout << "new q:\n" << q << "\n";);
                if (is_const(q)) {
                    TRACE("mgcd", tout << "done, modular gcd is one\n";);
                    if (m().is_one(d_a))
                        r = q; // GCD is one
                    else
                        r = mk_const(d_a);
                    return;
                }
                if (C_star.get() == 0) {
                    C_star = q;
                    m().set(bound, p);
                }
                else {
                    if (degree(q, x) < degree(C_star, x)) {
                        // discard accumulated image, it was affected by unlucky primes
                        TRACE("mgcd", tout << "discarding image\n";);
                        C_star = q;
                        m().set(bound, p);
                    }
                    else {
                        CRA_combine_images(q, p, C_star, bound, C_star);
                        TRACE("mgcd", tout << "new combined:\n" << C_star << "\n";);
                    }
                }
                pp(C_star, x, candidate);
                TRACE("mgcd", tout << "candidate:\n" << candidate << "\n";);
                scoped_numeral lc_candidate(m());
                lc_candidate = univ_coeff(candidate, degree(candidate, x));
                if (m().divides(lc_candidate, lc_g) && 
                    divides(candidate, pp_u) && 
                    divides(candidate, pp_v)) {
                    TRACE("mgcd", tout << "found GCD\n";);
                    r = mul(d_a, candidate);
                    flip_sign_if_lm_neg(r);
                    TRACE("mgcd", tout << "r: " << r << "\n";);
                    return;
                }
            }
            // Oops, modular GCD failed, not enough primes
            // fallback to prs
            gcd_prs(u, v, x, r);
        }

        typedef ref_buffer<polynomial, manager> polynomial_ref_buffer;

        /**
           Compute the content and primitive parts of p, when p is viewed as a multivariate polynomial Zp[y_1, ..., y_n]
           with coefficients in Zp[x].
        */
        som_buffer_vector m_iccp_ZpX_buffers;
        void iccp_ZpX(polynomial const * p, var x, numeral & ci, polynomial_ref & c, polynomial_ref & pp) {
            SASSERT(m().modular());
            TRACE("mgcd_detail", tout << "iccp_ZpX, p: "; p->display(tout, m()); tout << "\nvar x" << x << "\n";);
            if (is_zero(p)) {
                TRACE("mgcd_detail", tout << "iccp_ZpX, p is zero\n";);
                m_manager.set(ci, 0);
                c  = mk_one();
                pp = const_cast<polynomial*>(p);
                return;
            }
            if (is_const(p)) {
                TRACE("mgcd_detail", tout << "iccp_ZpX, p is constant\n";);
                m_manager.set(ci, p->a(0));
                c  = mk_one();
                pp = mk_one();
                return;
            }
            unsigned d = degree(p, x);
            if (d == 0) {
                TRACE("mgcd_detail", tout << "iccp_ZpX, degree(p, x) == 0\n";);
                ic(p, ci, pp);
                c = mk_one();
                return;
            }
            // 1) traverse monomials of p, and mark the monomials that contain p, also compute the minimal degree of x in p.
            ref_buffer<monomial, manager> no_x_ms(m_wrapper); // monomials that do not contains x
            unsigned min_degree = UINT_MAX;    // min degree of x in p
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                monomial * m = p->m(i);
                unsigned   k = m->degree_of(x);
                if (k == 0) {
                    // if m is not marked
                    if (m_m2pos.get(m) == UINT_MAX) {
                        no_x_ms.push_back(m);
                        m_m2pos.set(m, 1); // it is just a mark
                    }
                }
                if (k < min_degree)
                    min_degree = k;
            }
            SASSERT(min_degree == 0 || no_x_ms.empty());
            if (min_degree > 0) {
                SASSERT(no_x_ms.empty());
                // nothing was marked.
                // divide by x^min_degree
                TRACE("mgcd_detail", tout << "iccp_ZpX, all monomials contain x" << x << ", dividing by x" << x << "^" << min_degree << "\n";);
                polynomial_ref xmin(m_wrapper);
                polynomial_ref new_p(m_wrapper);
                xmin  = mk_polynomial(x, min_degree);
                new_p = exact_div(p, xmin);
                iccp_ZpX(new_p, x, ci, c, pp);
                c     = mul(xmin, c);
                return;
            }
            // 2) if for some marked monomial m (i.e., the ones that do not contain x), there is no monomial m*x^k in p,
            //    then c = 1
            unsigned num_marked = no_x_ms.size();
            unsigned num_unmarked = 0;
            monomial_ref tmp_m(m_wrapper);
            for (unsigned i = 0; i < sz; i++) {
                monomial * m = p->m(i);
                unsigned   k = m->degree_of(x);
                if (k == 0) 
                    continue; 
                tmp_m = div_x(m, x);
                SASSERT(tmp_m != m); // since x is in m, but not in tmp_m
                if (m_m2pos.get(tmp_m) == 1) {
                    num_unmarked++;
                    m_m2pos.reset(tmp_m);
                    SASSERT(m_m2pos.get(tmp_m) == UINT_MAX);
                }
            }
            SASSERT(num_unmarked <= num_marked);
            if (num_unmarked < num_marked) {
                // reset remaining marks
                for (unsigned i = 0; i < num_marked; i++) 
                    m_m2pos.reset(no_x_ms[i]);
                TRACE("mgcd_detail", tout << "iccp_ZpX, cheap case... invoking ic\n";);
                ic(p, ci, pp);
                c  = mk_one();
                return;
            }
            // 3) expensive case
            // Basic idea: separate a*m*x^k into a*x^k and m, put a*x^k into the som_buffer associated with m.
            // The mapping between m is som_buffers is given by m_m2pos
            
            // Extract integer content
            ic(p, ci, pp);
            no_x_ms.reset();
            som_buffer_vector & som_buffers = m_iccp_ZpX_buffers;
            som_buffers.set_owner(this);
            for (unsigned i = 0; i < sz; i++) {
                monomial * m = pp->m(i);
                unsigned   k = m->degree_of(x);
                if (k != 0) {
                    tmp_m = div_x(m, x);
                    m = tmp_m.get();
                }
                unsigned pos = m_m2pos.get(m);
                if (pos == UINT_MAX) {
                    pos = no_x_ms.size();
                    no_x_ms.push_back(m);
                    m_m2pos.set(m, pos);
                }
                som_buffer * som = som_buffers[pos];
                som->add(pp->a(i), mk_monomial(x, k));
            }
            unsigned num_ms = no_x_ms.size();
            for (unsigned i = 0; i < num_ms; i++) 
                m_m2pos.reset(no_x_ms[i]);
            SASSERT(num_ms > 0);
            // Compute GCD of all som_buffers
            polynomial_ref g(m_wrapper);
            polynomial_ref new_g(m_wrapper);
            g = som_buffers[0]->mk();
            for (unsigned i = 1; i < num_ms; i++) {
                polynomial_ref a(m_wrapper);
                a = som_buffers[i]->mk();
                SASSERT(is_univariate(a));
                euclid_gcd(g, a, new_g);
                g = new_g;
                if (is_const(g)) 
                    break;
            }
            if (!is_const(g)) {
                CTRACE("content_bug", !divides(g, pp),
                       tout << "GF(" << m().m().to_string(m().p()) << ")\n";
                       tout << "pp: "; pp->display(tout, m()); tout << "\n"; tout << "var: x" << x << "\n";
                       tout << "content: " << g << "\n";);
                c  = g;
                pp = exact_div(pp, c);
            }
            else {
                c  = mk_one();
            }
            som_buffers.reset(num_ms);
        }

        // Return the leading coefficient (with respect to glex) of p when 
        // p is viewed as a multivariate polynomial Zp[y_1, ..., y_n] with coefficients in Zp[x].
        polynomial * lc_glex_ZpX(polynomial const * p, var x) {
            // collect a*x^k of maximal monomial with respect to glex
            m_som_buffer.reset();
            monomial_ref max_m(m_wrapper);
            monomial_ref tmp_m(m_wrapper);
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                monomial * m = p->m(i); 
                unsigned   k = m->degree_of(x);
                if (k != 0) {
                    tmp_m = div_x(m, x);
                    m = tmp_m.get();
                }
                if (max_m == 0 || graded_lex_compare(m, max_m) > 0) {
                    // found new maximal monomial
                    m_som_buffer.reset();
                    max_m = m;
                    m_som_buffer.add(p->a(i), mk_monomial(x, k));
                }
                else if (max_m == m) {
                    // found another a*x^k of max_m
                    m_som_buffer.add(p->a(i), mk_monomial(x, k));
                }
            }
            SASSERT(!m_som_buffer.empty());
            TRACE("mgcd_detail", tout << "maximal monomial: "; max_m->display(tout); tout << "\n";);
            return m_som_buffer.mk();
        }

        // Wrapper for iccp_ZpX
        void primitive_ZpX(polynomial const * p, var x, polynomial_ref & pp) {
            scoped_numeral ci(m());
            polynomial_ref c(m_wrapper);
            iccp_ZpX(p, x, ci, c, pp);
        }

        // select a new random value in GF(p) that is not in vals, and store it in r
        void peek_fresh(scoped_numeral_vector const & vals, unsigned p, scoped_numeral & r) {
            SASSERT(vals.size() < p); // otherwise we cant keep the fresh value
            unsigned sz = vals.size();
            while (true) {
                m().set(r, rand() % p);
                // check if fresh value...
                unsigned k = 0;
                for (; k < sz; k++) {
                    if (m().eq(vals[k], r))
                        break;
                }
                if (k == sz)
                    return; // value is fresh
            }
        }

        newton_interpolator_vector   m_mgcd_iterpolators;
        scoped_ptr_vector<skeleton>  m_mgcd_skeletons;
        
        struct sparse_mgcd_failed {};
        
        // Auxiliary recursive function used in multivariate modular GCD
        void mod_gcd_rec(polynomial const * u, polynomial const * v, unsigned p, 
                         unsigned idx, var_buffer const & vars, polynomial_ref & r) {
            TRACE("mgcd", tout << "mod_gcd_rec\nu: "; u->display(tout, m_manager, true); tout << "\nv: "; v->display(tout, m_manager, true); tout << "\n";);
            unsigned num_vars = vars.size();
            SASSERT(num_vars > 0);
            if (idx == num_vars - 1) {
                SASSERT(is_univariate(u));
                SASSERT(is_univariate(v));
                euclid_gcd(u, v, r);
                TRACE("mgcd", tout << "mod_gcd_rec result: "; r->display(tout, m_manager, true); tout << "\n";);
                return;
            }

            var x = vars[idx];
            scoped_numeral ci_u(m()), ci_v(m());
            polynomial_ref c_u(m_wrapper),  pp_u(m_wrapper), lc_u(m_wrapper);
            polynomial_ref c_v(m_wrapper),  pp_v(m_wrapper), lc_v(m_wrapper);
            iccp_ZpX(u, x, ci_u, c_u, pp_u);
            iccp_ZpX(v, x, ci_v, c_v, pp_v);
            lc_u = lc_glex_ZpX(pp_u, x);
            lc_v = lc_glex_ZpX(pp_v, x);
            scoped_numeral ci_g(m());
            polynomial_ref c_g(m_wrapper);
            polynomial_ref lc_g(m_wrapper);
            TRACE("mgcd_detail", 
                  tout << "idx: " << idx << "\n";
                  tout << "x" << x << "\n";
                  tout << "pp_u = "; pp_u->display(tout, m_manager, true); tout << "\n";
                  tout << "pp_v = "; pp_v->display(tout, m_manager, true); tout << "\n";
                  tout << "c_u = "; c_u->display(tout, m_manager, true); tout << "\n";
                  tout << "c_v = "; c_v->display(tout, m_manager, true); tout << "\n";
                  tout << "lc_u = "; lc_u->display(tout, m_manager, true); tout << "\n";
                  tout << "lc_v = "; lc_v->display(tout, m_manager, true); tout << "\n";
                  tout << "ci_u = " << ci_u << "\n";
                  tout << "ci_v = " << ci_v << "\n";);
            m().gcd(ci_u, ci_v, ci_g);
            euclid_gcd(c_u, c_v, c_g);
            euclid_gcd(lc_u, lc_v, lc_g);
            TRACE("mgcd_detail", 
                  tout << "c_g = "; c_g->display(tout, m_manager, true); tout << "\n";
                  tout << "lc_g = "; lc_g->display(tout, m_manager, true); tout << "\n";
                  tout << "ci_g = " << ci_g << "\n";);
            
            skeleton * sk = m_mgcd_skeletons[idx];

            // use dense interpolation if skeleton is not available
            newton_interpolator & interpolator = m_mgcd_iterpolators[idx];
            sparse_interpolator sinterpolator(sk);

            polynomial_ref u1(m_wrapper), v1(m_wrapper), q(m_wrapper);
            scoped_numeral val(m());
            scoped_numeral lc_g_val(m());
            polynomial_ref H(m_wrapper), C(m_wrapper);
            polynomial_ref lc_H(m_wrapper);
            unsigned min_deg_q = UINT_MAX;
            unsigned counter   = 0;

            for (;; counter++) {
                while (true) {
                    peek_fresh(interpolator.inputs(), p, val);
                    // the selected value must satisfy lc_g(val) != 0
                    univ_eval(lc_g, x, val, lc_g_val);
                    if (!m().is_zero(lc_g_val))
                        break;
                }
                TRACE("mgcd", tout << "x" << x << " -> " << val << "\n";);
                u1 = substitute(pp_u, 1, &x, &(val.get()));
                v1 = substitute(pp_v, 1, &x, &(val.get()));
                mod_gcd_rec(u1, v1, p, idx+1, vars, q);
                q = mk_glex_monic(q);
                q = mul(lc_g_val, q);
                var q_var      = max_var(q);
                unsigned deg_q = q_var == null_var ? 0 : degree(q, q_var);
                TRACE("mgcd_detail", tout << "counter: " << counter << "\nidx: " << idx << "\nq: " << q << "\ndeg_q: " << deg_q << "\nmin_deg_q: " << 
                      min_deg_q << "\nnext_x: x" << vars[idx+1] << "\nmax_var(q): " << q_var << "\n";);
                if (deg_q < min_deg_q) {
                    TRACE("mgcd_detail", tout << "reseting...\n";);                    
                    counter   = 0;
                    min_deg_q = deg_q;
                    // start from scratch
                    if (sk == 0) {
                        interpolator.reset();
                        interpolator.add(val, q); 
                    }
                    else {
                        sinterpolator.reset();
                        if (!sinterpolator.add(val, q))
                            throw sparse_mgcd_failed();
                    }
                }
                else if (deg_q == min_deg_q) {
                    TRACE("mgcd_detail", tout << "adding sample point...\n";);                    
                    if (sk == 0) {
                        interpolator.add(val, q); 
                    }
                    else {
                        if (!sinterpolator.add(val, q))
                            throw sparse_mgcd_failed();
                    }
                }
                else {
                    TRACE("mgcd", tout << "skipping q...\n";);
                    continue;
                }
                bool found_candidate = false;
                if (sk == 0) {
                    SASSERT(interpolator.num_sample_points() > 0);
                    interpolator.mk(x, H);
                    TRACE("mgcd_detail", tout << "idx: " << idx << "\ncandidate H: " << H << "\n";);
                    lc_H = lc_glex_ZpX(H, x);
                    TRACE("mgcd_detail", tout << "idx: " << idx << "\nlc_H: " << lc_H << "\nlc_g: " << lc_g << "\n";);
                    if (eq(lc_H, lc_g)) {
                        found_candidate = true;
                    }
                }
                else {
                    if (sinterpolator.ready()) {
                        if (!sinterpolator.mk(H))
                            throw sparse_mgcd_failed();
                        found_candidate = true;
                    }
                }
                
                bool done = false;
                if (found_candidate) {
                    if (degree(H, x) > 0) 
                        primitive_ZpX(H, x, C);
                    else
                        C = normalize(H);
                    TRACE("mgcd_detail", tout << "C: " << C << "\npp_u: " << pp_u << "\npp_v: " << pp_v << "\ndivides(C, pp_u): " <<
                          divides(C, pp_u) << "\ndivides(C, pp_v): " << divides(C, pp_v) << "\n";);
                    if (divides(C, pp_u) && divides(C, pp_v)) {
                        r = mul(c_g, C);
                        r = mul(ci_g, r);
                        done = true;
                    }
                    else if (min_deg_q == 0) {
                        r = c_g;
                        r = mul(ci_g, r);
                        done = true;
                    }
                    else if (sk != 0) {
                        throw sparse_mgcd_failed();
                    }
                }
                
                if (done) {
                    TRACE("mgcd", tout << "idx: " << idx << "\nresult: " << r << "\n";);
                    if (sk == 0 && m_use_sparse_gcd) {
                        // save skeleton
                        skeleton * new_sk = alloc(skeleton, *this, H, x);
                        m_mgcd_skeletons.set(idx, new_sk);
                    }
                    return;
                }
            }
        }

        // Multivariate modular GCD algorithm
        void mod_gcd(polynomial const * u, polynomial const * v, 
                     power_buffer const & u_var_degrees, power_buffer const & v_var_degrees, 
                     polynomial_ref & r) {
            m_mgcd_iterpolators.set_owner(this);
            TRACE("mgcd", tout << "mod_gcd\nu: "; u->display(tout, m_manager, true); tout << "\nv: "; v->display(tout, m_manager, true); tout << "\n";);
            TRACE("mgcd_call", tout << "mod_gcd\nu: "; u->display(tout, m_manager, true); tout << "\nv: "; v->display(tout, m_manager, true); tout << "\n";);
            SASSERT(!m().modular());
            // u and v contain the same set of variables
            SASSERT(u_var_degrees.size() == v_var_degrees.size());
            unsigned num_vars = u_var_degrees.size();
            SASSERT(num_vars > 1); // should use uni_mod_gcd if univariate
            var_buffer      vars;
            power_buffer var_min_degrees;
            for (unsigned i = 0; i < num_vars; i++) {
                SASSERT(u_var_degrees[i].get_var() == v_var_degrees[i].get_var());
                var x = u_var_degrees[i].get_var();
                unsigned d = std::min(u_var_degrees[i].degree(), v_var_degrees[i].degree());
                var_min_degrees.push_back(power(x, d));
            }
            std::sort(var_min_degrees.begin(), var_min_degrees.end(), power::lt_degree());
            m_mgcd_skeletons.reset();
            for (unsigned i = 0; i < num_vars; i++) {
                vars.push_back(var_min_degrees[i].get_var());
                m_mgcd_skeletons.push_back(0);
            }

            scoped_numeral c_u(m()), c_v(m());
            polynomial_ref pp_u(pm()), pp_v(pm());
            ic(u, c_u, pp_u);
            ic(v, c_v, pp_v);
            
            scoped_numeral d_a(m());
            m_manager.gcd(c_u, c_v, d_a);
            
            unsigned mm_u_pos = pp_u->graded_lex_max_pos(); // position of the maximal monomial in u
            unsigned mm_v_pos = pp_v->graded_lex_max_pos(); // position of the maximal monomial in v
            scoped_numeral lc_u(m());
            scoped_numeral lc_v(m());
            lc_u = pp_u->a(mm_u_pos);
            lc_v = pp_v->a(mm_v_pos);
            scoped_numeral lc_g(m());
            m().gcd(lc_u, lc_v, lc_g);

            polynomial_ref u_Zp(m_wrapper);
            polynomial_ref v_Zp(m_wrapper);
            polynomial_ref C_star(m_wrapper);
            scoped_numeral bound(m());
            polynomial_ref q(m_wrapper);
            polynomial_ref candidate(m_wrapper);
            scoped_numeral p(m());
            
            for (unsigned i = 0; i < NUM_BIG_PRIMES; i++) {
                m().set(p, g_big_primes[i]);
                TRACE("mgcd", tout << "trying prime: " << p << "\n";);
                {
                    scoped_set_zp setZp(m_wrapper, p);
                    u_Zp = normalize(pp_u);
                    if (u_Zp->size() != pp_u->size()) {
                        TRACE("mgcd", tout << "bad prime, coefficient(s) vanished\n";);
                        continue; // bad prime some monomial vanished
                    }
                    v_Zp = normalize(pp_v);
                    if (v_Zp->size() != pp_v->size()) {
                        TRACE("mgcd", tout << "bad prime, coefficient(s) vanished\n";);
                        continue; // bad prime some monomial vanished
                    }
                    TRACE("mgcd", tout << "u_Zp: " << u_Zp << "\nv_Zp: " << v_Zp << "\n";);
                    mod_gcd_rec(u_Zp, v_Zp, g_big_primes[i], 0, vars, q);
                    q = mk_glex_monic(q);
                    scoped_numeral c(m());
                    m().set(c, lc_g);
                    q = mul(c, q);
                }
                TRACE("mgcd", tout << "new q:\n" << q << "\n";);
                if (is_const(q)) {
                    TRACE("mgcd", tout << "done, modular gcd is one\n";);
                    r = mk_const(d_a);
                    return;
                }
                if (C_star.get() == 0) {
                    C_star = q;
                    m().set(bound, p);
                }
                else {
                    monomial * max_C_star = C_star->m(C_star->graded_lex_max_pos());
                    monomial * max_q      = q->m(q->graded_lex_max_pos());
                    if (graded_lex_compare(max_q, max_C_star) < 0) {
                        // Discard accumulated image, it was affected by unlucky primes
                        // maximal monomial of q is smaller than maximal monomial of C_star
                        TRACE("mgcd", tout << "discarding image\n";);
                        C_star = q;
                        m().set(bound, p);
                    }
                    else {
                        CRA_combine_images(q, p, C_star, bound, C_star);
                        TRACE("mgcd", tout << "new combined:\n" << C_star << "\n";);
                    }
                }
                candidate = normalize(C_star);
                TRACE("mgcd", tout << "candidate:\n" << candidate << "\n";);
                scoped_numeral lc_candidate(m());
                lc_candidate = candidate->a(candidate->graded_lex_max_pos());
                if (m().divides(lc_candidate, lc_g) && 
                    divides(candidate, pp_u) && 
                    divides(candidate, pp_v)) {
                    TRACE("mgcd", tout << "found GCD\n";);
                    r = mul(d_a, candidate);
                    flip_sign_if_lm_neg(r);
                    TRACE("mgcd", tout << "r: " << r << "\n";);
                    return;
                }
            }
            // Oops, modular GCD failed, not enough primes
            // fallback to prs
            gcd_prs(u, v, max_var(u), r);
        }
        
        void gcd(polynomial const * u, polynomial const * v, polynomial_ref & r) {
            power_buffer u_var_degrees;
            power_buffer v_var_degrees;
            TRACE("gcd_calls", tout << "gcd\nu: "; u->display(tout, m_manager); tout << "\nv: "; v->display(tout, m_manager); tout << "\n";);
            TRACE("polynomial_gcd", 
                  tout << "gcd\nu: "; u->display(tout, m_manager); tout << "\nv: "; v->display(tout, m_manager);
                  tout << "\nis_zero(u): " << is_zero(u) << ", is_const(u): " << is_const(u) << "\n";
                  tout << "is_zero(v): " << is_zero(v) << ", is_const(v): " << is_const(v) << "\n";
                  tout << "modular: " << m().modular() << "\n";);
            if (is_zero(u)) {
                r = const_cast<polynomial*>(v); 
                flip_sign_if_lm_neg(r);
                return;
            }
            if (is_zero(v)) {
                r = const_cast<polynomial*>(u);
                flip_sign_if_lm_neg(r);
                return;
            }
            if (u == v) {
                r = const_cast<polynomial*>(u);
                flip_sign_if_lm_neg(r);
                return;
            }
            if (is_const(u) || is_const(v)) { 
                scoped_numeral i_u(m_manager), i_v(m_manager);
                ic(v, i_v);
                ic(u, i_u);
                scoped_numeral a(m_manager);
                m_manager.gcd(i_v, i_u, a);
                r = mk_const(a);
                return;
            }
            
            // Search for a variable x that occurs only in u or v.
            var_max_degrees(u, u_var_degrees); std::sort(u_var_degrees.begin(), u_var_degrees.end(), power::lt_var());
            var_max_degrees(v, v_var_degrees); std::sort(v_var_degrees.begin(), v_var_degrees.end(), power::lt_var());

            TRACE("polynomial_gcd", 
                  tout << "u var info\n"; for (unsigned i = 0; i < u_var_degrees.size(); i++) tout << u_var_degrees[i] << " "; tout << "\n";
                  tout << "v var info\n"; for (unsigned i = 0; i < v_var_degrees.size(); i++) tout << v_var_degrees[i] << " "; tout << "\n";);
            var x        = null_var;
            bool u_found = false;
            bool v_found = false;
            unsigned i    = 0;
            unsigned u_sz = u_var_degrees.size();
            unsigned v_sz = v_var_degrees.size();
            unsigned sz   = std::min(u_sz, v_sz);
            for (; i < sz; i++) {
                var xu = u_var_degrees[i].get_var();
                var xv = v_var_degrees[i].get_var();
                if (xu < xv) {
                    x = xu;
                    u_found = true;
                    break;
                }
                if (xu > xv) {
                    x = xv;
                    v_found = true;
                    break;
                }
            }
            if (!u_found && !v_found && i < u_sz) {
                x = u_var_degrees[i].get_var();
                u_found = true;
            }
            if (!u_found && !v_found && i < v_sz) {
                x = v_var_degrees[i].get_var();
                v_found = true;
            }

            if (u_found) {
                // u has a variable x that v doesn't have.
                // Thus, gcd(u, v) = gcd(content(u, x), v)
                gcd_content(u, x, v, r);
                return;
            }

            if (v_found) {
                // v has a variable x that u doesn't have.
                // Thus, gcd(u, v) = gcd(u, content(v, x))
                gcd_content(v, x, u, r);
                return;
            }

            // TODO:
            // Try to find a variable x that occurs linearly in u or v
            // In this case, the GCD is linear or constant in x.
            // Assume x occurs linearly in u. Then,
            // gcd(u, v) = gcd(content(u, x), content(v, x))         if pp(u, x) does not divide pp(v, x)
            // gcd(u, v) = gcd(content(u, x), content(v, x))*pp(u,x) if pp(u, x) divides pp(v, x)
            //

            // select variable with minimal degree
            x = u_var_degrees[sz - 1].get_var(); // give preference to maximal variable
            SASSERT(u_var_degrees[sz - 1].get_var() == v_var_degrees[sz - 1].get_var());
            SASSERT(max_var(u) == max_var(v));
            SASSERT(max_var(u) == x);
#if 0
            unsigned min_k = std::max(m_u_var_degrees[sz - 1].degree(), m_v_var_degrees[sz - 1].degree());
            unsigned max_var_bias = 2; // the basic procedures are optimized for operating on the maximal variable. So, we have a bias to select the maximal one 
            if (min_k > max_var_bias) {
                min_k -= max_var_bias;
                i = sz - 1;
                while (i > 0) {
                    --i;
                    SASSERT(m_u_var_degrees[i].get_var() == m_v_var_degrees[i].get_var());
                    unsigned k = std::max(m_u_var_degrees[i].degree(), m_v_var_degrees[i].degree());
                    if (k < min_k) {
                        x     = m_u_var_degrees[i].get_var();
                        min_k = k;
                    }
                }
            }
#endif
            if (!m().modular() && !m_use_prs_gcd) {
                SASSERT(max_var(u) == max_var(v));
                if (is_univariate(u)) {
                    SASSERT(is_univariate(v));
                    uni_mod_gcd(u, v, r);
                }
                else {
                    try {
                        #ifdef Z3DEBUG
                        polynomial_ref orig_u(m_wrapper);
                        polynomial_ref orig_v(m_wrapper);
                        if (is_debug_enabled("mgcd_check")) {
                            orig_u = const_cast<polynomial*>(u);
                            orig_v = const_cast<polynomial*>(v);
                        }
                        #endif

                        mod_gcd(u, v, u_var_degrees, v_var_degrees, r);
                            
                        #ifdef Z3DEBUG
                        if (is_debug_enabled("mgcd_check")) {
                            polynomial_ref r2(m_wrapper);
                            flet<bool> use_prs(m_use_prs_gcd, false);
                            gcd_prs(orig_u, orig_v, x, r2);
                            CTRACE("mgcd_bug", !eq(r, r2), tout << "u: " << orig_u << "\nv: " << orig_v << "\nr1: " << r << "\nr2: " << r2 << "\n";);
                            SASSERT(eq(r, r2));
                        }
                        #endif
                    }
                    catch (sparse_mgcd_failed) {
                        flet<bool> use_prs(m_use_prs_gcd, false);
                        gcd_prs(u, v, x, r);
                    }
                }
            }
            else {
                gcd_prs(u, v, x, r);
            }
        }

        monomial * derivative(monomial const * m, var x) {
            return mm().derivative(m, x);
        }

        polynomial * derivative(polynomial const * p, var x) {
            SASSERT(is_valid(x));
            SASSERT(m_cheap_som_buffer.empty());
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                monomial * m = p->m(i);
                unsigned   d = m->degree_of(x);
                TRACE("polynomial", m->display(tout); tout << " degree_of x" << x << ": " << d << "\n";);
                if (d > 0) {
                    scoped_numeral n(m_manager);
                    m_manager.set(n, d);
                    scoped_numeral a(m_manager);
                    m_manager.mul(p->a(i), n, a);
                    m_cheap_som_buffer.add_reset(a, derivative(m, x));
                }
            }
            return m_cheap_som_buffer.mk();
        }

        void square_free(polynomial const * p, polynomial_ref & r) {
            if (is_zero(p)) {
                r = mk_zero();
                return;
            }
            if (is_const(p)) {
                r = const_cast<polynomial*>(p);
                return;
            }
            
            var x = max_var(p);
            scoped_numeral i(m_manager);
            polynomial_ref c(pm()), pp(pm());
            iccp(p, x, i, c, pp);
            polynomial_ref sqf_c(pm());
            square_free(c, sqf_c);

            polynomial_ref pp_prime(pm());
            pp_prime = derivative(pp, x);
            polynomial_ref g(pm());
            gcd(pp, pp_prime, g);
            if (is_const(g)) {
                if (eq(sqf_c, c)) {
                    r = const_cast<polynomial*>(p);
                    return;
                }
            }
            else {
                pp = exact_div(pp, g);
            }
            r = mul(i, sqf_c);
            r = mul(r, pp);
        }

        bool is_square_free(polynomial const * p) {
            polynomial_ref r(pm());
            square_free(p, r);
            SASSERT(!eq(p, r) || p == r.get()); // this is a property of the square_free procedure
            return p == r.get();
        }

        void square_free(polynomial const * p, var x, polynomial_ref & r) {
            if (is_zero(p)) {
                r = mk_zero();
                return;
            }
            if (is_const(p)) {
                r = const_cast<polynomial*>(p);
                return;
            }
            
            polynomial_ref p_prime(pm());
            p_prime = derivative(p, x);
            polynomial_ref g(pm());
            gcd(p, p_prime, g);
            if (is_const(g)) {
                r = const_cast<polynomial*>(p);
            }
            else {
                r = exact_div(p, g);
            }
        }

        bool is_square_free(polynomial const * p, var x) {
            polynomial_ref r(pm());
            square_free(p, x, r);
            SASSERT(!eq(p, r) || p == r.get()); // this is a property of the square_free procedure
            return p == r.get();
        }

        void pw(polynomial const * p, unsigned k, polynomial_ref & r) {
            if (k == 0) {
                r = mk_one();
                return;
            }
            if (k == 1) {
                r = const_cast<polynomial*>(p);
                return;
            }
            polynomial_ref result(pm());
            result = const_cast<polynomial*>(p);
            for (unsigned i = 1; i < k; i++)
                result = mul(result, const_cast<polynomial*>(p));
            r = result;
#if 0
            SASSERT(k >= 2);
            unsigned mask  = 1;
            polynomial_ref p2(pm());
            p2 = const_cast<polynomial*>(p);
            r  = mk_one();
            while (true) {
                if (mask & k)
                    r = mul(r, p2);
                mask = mask << 1;
                if (mask > k)
                    return;
                p2 = mul(p2, p2);
            }
#endif
        }

        bool eq(polynomial const * p1, polynomial const * p2) {
            if (p1 == p2)
                return true;
            unsigned sz1 = p1->size();
            unsigned sz2 = p2->size();
            if (sz1 != sz2)
                return false;
            if (sz1 == 0)
                return true;
            if (max_var(p1) != max_var(p2))
                return false;
            m_m2pos.set(p1);
            for (unsigned i = 0; i < sz2; i++) {
                unsigned pos1 = m_m2pos.get(p2->m(i));
                if (pos1 == UINT_MAX || !m_manager.eq(p1->a(pos1), p2->a(i))) {
                    m_m2pos.reset(p1);
                    return false;
                }
            }
            m_m2pos.reset(p1);
            return true;
        }

        polynomial * compose_1_div_x(polynomial const * p) {
            SASSERT(is_univariate(p));
            if (is_const(p))
                return const_cast<polynomial*>(p);
            SASSERT(m_cheap_som_buffer.empty());
            var x       = max_var(p);
            unsigned n  = degree(p, x);
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                monomial * m = p->m(i);
                SASSERT(m->size() <= 1);
                monomial * new_m = mk_monomial(x, n - m->degree_of(x));
                m_cheap_som_buffer.add(p->a(i), new_m);
            }
            return m_cheap_som_buffer.mk();
        }

        void push_power(sbuffer<power> & pws, var x, unsigned d) {
            if (d > 0)
                pws.push_back(power(x, d));
        }

        polynomial * compose_x_div_y(polynomial const * p, var y) {
            SASSERT(is_univariate(p));
            SASSERT(max_var(p) != y);
            if (is_const(p))
                return const_cast<polynomial*>(p);
            SASSERT(m_cheap_som_buffer.empty());
            var x       = max_var(p);
            unsigned n  = degree(p, x);
            unsigned sz = p->size();
            sbuffer<power> pws;
            for (unsigned i = 0; i < sz; i++) {
                unsigned   k = p->m(i)->degree_of(x);
                pws.reset();
                if (x < y) {
                    push_power(pws, x, k);
                    push_power(pws, y, n - k);
                }
                else {
                    push_power(pws, y, n - k);
                    push_power(pws, x, k);
                }
                monomial * new_m = mk_monomial(pws.size(), pws.c_ptr());
                m_cheap_som_buffer.add(p->a(i), new_m);
            }
            return m_cheap_som_buffer.mk();
        }

        polynomial * compose_y(polynomial const * p, var y) {
            SASSERT(is_valid(y));
            SASSERT(is_univariate(p));
            if (y == max_var(p) || is_const(p))
                return const_cast<polynomial*>(p);
            SASSERT(m_cheap_som_buffer.empty());
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                monomial * m = p->m(i);
                SASSERT(m->size() <= 1);
                monomial * new_m;
                if (m->size() == 0) 
                    new_m = m;
                else
                    new_m = mk_monomial(y, m->degree(0));
                m_cheap_som_buffer.add(p->a(i), new_m);
            }
            return m_cheap_som_buffer.mk();
        }

        polynomial * compose_minus_x(polynomial const * p) {
            SASSERT(is_univariate(p));
            if (is_const(p))
                return const_cast<polynomial*>(p);
            SASSERT(m_cheap_som_buffer.empty());
            scoped_numeral a(m_manager);
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                monomial * m = p->m(i);
                if (m->total_degree() % 2 == 0) {
                    m_cheap_som_buffer.add(p->a(i), p->m(i));
                }
                else {
                    m_manager.set(a, p->a(i));
                    m_manager.neg(a);
                    m_cheap_som_buffer.add(a, p->m(i));
                }
            }
            return m_cheap_som_buffer.mk();
        }

        /**
           \brief Store the positions (in m_degree2pos) of the monomials of an univariate polynomial.
        */
        void save_degree2pos(polynomial const * p) {
            SASSERT(is_univariate(p));
            var x = max_var(p);
            unsigned n  = degree(p, x);
            m_degree2pos.reserve(n+1, UINT_MAX);
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                monomial * m = p->m(i);
                SASSERT(m->size() <= 1);
                SASSERT(m_degree2pos[m->total_degree()] == UINT_MAX);
                m_degree2pos[m->total_degree()] = i;
            }
        }

        /**
           \brief Undo the modifications in m_degree2pos performed by save_degree2pos.
        */
        void reset_degree2pos(polynomial const * p) {
            SASSERT(is_univariate(p));
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                monomial * m = p->m(i);
                SASSERT(m->size() <= 1);
                SASSERT(m_degree2pos[m->total_degree()] == i);
                m_degree2pos[m->total_degree()] = UINT_MAX;
            }
        }

        // muladd may throw if the cancel flag is set.
        // So we wrap the degree2pos set and reset
        // in a scoped class to ensure the state is clean
        // on exit.
        struct scoped_degree2pos {
            imp& pm;
            polynomial const* p;            
            scoped_degree2pos(imp& pm, polynomial const* p):
                pm(pm),
                p(p)
            {
                pm.save_degree2pos(p);
            }

            ~scoped_degree2pos() {
                pm.reset_degree2pos(p);
            }
        };

        /**
           \brief Given an univariate polynomial p(x) and a polynomial q(y_1, ..., y_n),
           return a polynomial r(y_1, ..., y_n) = p(q(y_1, ..., y_n)).
        */
        void compose(polynomial const * p, polynomial const * q, polynomial_ref & r) {
            SASSERT(is_univariate(p));
            if (is_const(p)) {
                r = const_cast<polynomial*>(p);
                return;
            }
            var x      = max_var(p);
            unsigned d = degree(p, x); 
            scoped_degree2pos _sd2pos(*this, p);
            scoped_numeral a(m());
            m_manager.set(a, p->a(m_degree2pos[d]));
            r = mk_const(a);
            for (unsigned i = 1; i <= d; i++) {
                unsigned pos = m_degree2pos[d-i];
                if (pos != UINT_MAX)
                    m_manager.set(a, p->a(pos));
                else
                    m_manager.reset(a);
                r = muladd(q, r, a); 
            }
        }

        polynomial * mk_x_minus_y(var x, var y) {
            numeral zero(0);
            numeral one(1);
            numeral minus_one; // It is not safe to initialize with -1 when numeral_manager is GF_2
            m_manager.set(minus_one, -1);
            numeral as[2] = { one, minus_one };
            var     xs[2] = { x, y };
            return mk_linear(2, as, xs, zero);
        }
        
        void compose_x_minus_y(polynomial const * p, var y, polynomial_ref & r) {
            SASSERT(is_valid(y));
            SASSERT(is_univariate(p));
            var x = max_var(p);
            if (y == max_var(p)) {
                r = coeff(p, x, 0); 
                return;
            }
            polynomial_ref x_minus_y(pm());
            x_minus_y = mk_x_minus_y(x, y);
            return compose(p, x_minus_y, r);
        }

        polynomial * mk_x_plus_y(var x, var y) {
            numeral zero(0);
            numeral one(1);
            numeral as[2] = { one, one };
            var     xs[2] = { x, y };
            return mk_linear(2, as, xs, zero);
        }

        void compose_x_plus_y(polynomial const * p, var y, polynomial_ref & r) {
            SASSERT(is_valid(y));
            SASSERT(is_univariate(p));
            var x = max_var(p);
            polynomial_ref x_plus_y(pm());
            x_plus_y = mk_x_plus_y(x, y);
            return compose(p, x_plus_y, r);
        }

        // Return the polynomial x - c
        polynomial * mk_x_minus_c(var x, numeral const & c) {
            numeral as[2];
            m_manager.set(as[0], c);
            m_manager.set(as[1], 1);
            m_manager.neg(as[0]);
            polynomial * p = mk_univariate(x, 1, as);
            TRACE("polynomial", tout << "x - c: "; p->display(tout, m_manager); tout << "\n";);
            m_manager.del(as[0]);
            m_manager.del(as[1]);
            return p;
        }

        void compose_x_minus_c(polynomial const * p, numeral const & c, polynomial_ref & r) {
            SASSERT(is_univariate(p));
            if (m_manager.is_zero(c)) {
                r = const_cast<polynomial*>(p);
                return;
            }
            var x = max_var(p);
            polynomial_ref x_minus_c(pm());
            x_minus_c = mk_x_minus_c(x, c);
            return compose(p, x_minus_c, r);
        }

        /**
           \brief Template for computing several variations of pseudo division algorithm.
           If degree(p) < degree(q) -->  Q = m_zero, d = 0, R = p
           
           The following property is guaranteed by this method

           l(q)^d * p = Q * q + R

           where l(q) is coeff(q, x, degree(q, x))

           Possible configurations:
           Exact_d == true, then d = degree(p) - degree(q) + 1.
           If Exact_d == false, then d <= degree(p) - degree(q) + 1.
           
           If Quotient == false, Q is not computed.

           If ModD == true, then x2d must be different from 0.
           Moreover, p and q are assumed to be normalized modulo x2d. 
           For all x, x2d->degree(x) > 0 implies  degree(p, x) < x2d->degree(x) and degree(q, x) < x2d->degree(x)
           Moreover, the division algorithm will compute Q and R modulo x2d.
        */
        template<bool Exact_d, bool Quotient, bool ModD>
        void pseudo_division_core(polynomial const * p, polynomial const * q, var x, unsigned & d, polynomial_ref & Q, polynomial_ref & R, 
                                  var2degree const * x2d = 0) {
            SASSERT(is_valid(x));
            SASSERT(!ModD || x2d != 0);
            TRACE("polynomial", tout << "pseudo_division\np: "; p->display(tout, m_manager); 
                  tout << "\nq: "; q->display(tout, m_manager); tout << "\nx: " << x << "\n";);
            polynomial * A = const_cast<polynomial*>(p);
            polynomial * B = const_cast<polynomial*>(q);
            unsigned deg_A = degree(A, x);
            unsigned deg_B = degree(B, x);
            if (deg_B == 0) {
                R = m_zero;
                if (Quotient) {
                    if (Exact_d) {
                        d = deg_A /* - deg_B */ + 1;
                        // Since degree(B) = 0, lc(B) == B
                        // lc(B)^d * A = Q * B + R  -->  (using R == 0, lc(B) == B)
                        // B^d * A = Q * B
                        // Thus, Q = A * B^{d-1}
                        if (d == 1) {
                            Q = A;
                            return;
                        }
                        polynomial_ref Bdm1(pm());
                        pw(B, d - 1, Bdm1);
                        Q = mul(A, Bdm1);
                        if (ModD)
                            Q = mod_d(Q, *x2d);
                    }
                    else {
                        d = 1;
                        Q = A;
                    }
                }
                return;
            }
            if (deg_B > deg_A) {
                Q = m_zero;
                R = A;
                d = 0;
            }
            scoped_numeral minus_a(m_manager);
            polynomial_ref l_B(pm()); // leading coefficient of B (that is, coefficient of x^(deg_B))
            polynomial_ref r_B(pm()); // reduct of B (that is, B without leading coefficient)
            l_B = coeff(B, x, deg_B, r_B);
            d = 0;
            R = A;
            Q = m_zero;
            while (true) {
                checkpoint();
                TRACE("polynomial",
                      tout << "A: "; A->display(tout, m_manager); tout << "\n";
                      tout << "B: "; B->display(tout, m_manager); tout << "\n";
                      tout << "l_B: "; l_B->display(tout, m_manager); tout << "\n";
                      tout << "r_B: "; r_B->display(tout, m_manager); tout << "\n";                      
                      tout << "Q: "; Q->display(tout, m_manager); tout << "\n";
                      tout << "R: "; R->display(tout, m_manager); tout << "\n";
                      tout << "d: " << d << "\n";);
                unsigned deg_R = degree(R, x);
                if (deg_B > deg_R) {
                    if (Exact_d) {
                        // Adjust Q and R
                        unsigned exact_d = deg_A - deg_B + 1;
                        SASSERT(d <= exact_d);
                        if (d < exact_d) {
                            unsigned e = exact_d - d;
                            polynomial_ref l_B_e(pm());
                            pw(l_B, e, l_B_e);
                            TRACE("polynomial", tout << "l_B_e: " << l_B_e << "\n";);
                            if (Quotient) {
                                Q = mul(l_B_e, Q);
                                if (ModD) 
                                    Q = mod_d(Q, *x2d);
                            }
                            R = mul(l_B_e, R);
                            if (ModD)
                                R = mod_d(R, *x2d);
                        }
                    }
                    return;
                }
                // S <- l_R * x^(deg_R - deg_B)
                // R <- l_B * R - S * B
                // Note that the goal is to cancel x^deg_R in R.
                // m_som_buffer will contain the new monomials of R.
                m_som_buffer.reset();
                // We can accomplish that by traversing the current R, and 
                //  - For each monomial a * m * x^deg_R --> m_som_buffer.addmul(-a, m * x^(deg_R - deg_B), r_B)
                //               Note that m*x^(deg_R - deg_B) is div_x_k(m*x^deg_R, deg_B)
                //  - For other monomials a*m,  --->   m_som_buffer.addmul(a, m, l_B) 
                // Note that, with this trick and don't need to create the temporary polynomials l_B * R and S * B
                //
                // If the quotient needs to be computed, we have that
                // S <- l_R * x^(deg_R - deg_B)
                // Q <- l_B * Q + S
                // The new monomials of Q are stored in m_som_buffer2
                // When traversing R, for each monomial a*m*x^deg_R  we add m_som_buffer2.add(a, m*x^(deg_R - deg_B)) 
                m_som_buffer2.reset();
                // 
                unsigned sz = R->size();
                for (unsigned i = 0; i < sz; i++) {
                    monomial * m      = R->m(i);
                    numeral const & a = R->a(i);
                    if (m->degree_of(x) == deg_R) {
                        monomial_ref m_prime(pm());
                        m_prime = div_x_k(m, x, deg_B);
                        CTRACE("polynomial", m->degree_of(x) != deg_R - deg_B, 
                               tout << "deg_R: " << deg_R << ", deg_B: " << deg_B << ", x: " << x << "\n";
                               m->display(tout); tout << ", "; m_prime->display(tout); tout << "\n";);
                        SASSERT(m->degree_of(x) == deg_R);
                        SASSERT(m_prime->degree_of(x) == deg_R - deg_B);
                        if (Quotient) {
                            m_som_buffer2.add(a, m_prime);
                        }
                        m_manager.set(minus_a, a);
                        m_manager.neg(minus_a);
                        m_som_buffer.addmul(minus_a, m_prime, r_B);
                    }
                    else {
                        m_som_buffer.addmul(a, m, l_B);
                    }
                }
                if (ModD)
                    m_som_buffer.mod_d(*x2d);
                R = m_som_buffer.mk();
                if (Quotient) {
                    // m_som_buffer2 contains new monomials of Q <- l_B Q + S
                    // We have already copied S to m_som_buffer2.
                    // To add l_B * Q, we just traverse Q executing addmul(Q->a(i), Q->m(i), l_B)
                    unsigned sz = Q->size();
                    for (unsigned i = 0; i < sz; i++) {
                        m_som_buffer2.addmul(Q->a(i), Q->m(i), l_B);
                    }
                    if (ModD)
                        m_som_buffer2.mod_d(*x2d);
                    Q = m_som_buffer2.mk();
                }
                d++;
            }
        }

        void exact_pseudo_remainder(polynomial const * p, polynomial const * q, var x, polynomial_ref & R) {
            unsigned d;
            polynomial_ref Q(pm());
            pseudo_division_core<true, false, false>(p, q, x, d, Q, R);
        }

        void pseudo_remainder(polynomial const * p, polynomial const * q, var x, unsigned & d, polynomial_ref & R) {
#ifdef Z3DEBUG
            polynomial_ref old_p(pm());
            polynomial_ref old_q(pm());
            old_p = const_cast<polynomial*>(p); // R may be aliasing p and q
            old_q = const_cast<polynomial*>(q);
            polynomial_ref Q(pm());
            pseudo_division_core<false, true, false>(p, q, x, d, Q, R);
            // debugging code
            // check if lc(q)^d * p = Q * q + R
            polynomial_ref l(pm());
            l = coeff(old_q, x, degree(q, x));
            polynomial_ref ld(pm());
            pw(l, d, ld);
            polynomial_ref lhs(pm());
            lhs = mul(ld, old_p);
            polynomial_ref rhs(pm());
            rhs = mul(Q, old_q);
            rhs = add(rhs, R);
            bool is_eq = eq(lhs, rhs);
            TRACE("pseudo_remainder", 
                  tout << "pseudo_division bug\n";
                  tout << "p:   "; old_p->display(tout, m_manager); tout << "\n";
                  tout << "q:   "; old_q->display(tout, m_manager); tout << "\n";
                  tout << "Q:   " << Q << "\nR:   " << R << "\n";
                  tout << "l^d: " << ld << "\nlhs: " << lhs << "\nrhs: " << rhs << "\n";);
            SASSERT(is_eq);
#else
            polynomial_ref Q(pm());
            pseudo_division_core<false, false, false>(p, q, x, d, Q, R);
#endif
        }

        void exact_pseudo_division(polynomial const * p, polynomial const * q, var x, polynomial_ref & Q, polynomial_ref & R) {
            unsigned d;
            pseudo_division_core<true, true, false>(p, q, x, d, Q, R);
        }

        void pseudo_division(polynomial const * p, polynomial const * q, var x, unsigned & d, polynomial_ref & Q, polynomial_ref & R) {
            pseudo_division_core<false, true, false>(p, q, x, d, Q, R);
        }

        polynomial * exact_div(polynomial const * p, numeral const & c) {
            SASSERT(!m().is_zero(c));
            
            som_buffer & R = m_som_buffer;
            R.reset();

            numeral tmp;

            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; ++ i) {
                SASSERT(m().divides(c, p->a(i)));
                m().div(p->a(i), c, tmp);
                if (!m().is_zero(tmp)) {
                    R.add(tmp, p->m(i));
                }
            }

            m().del(tmp);

            return R.mk();
        }

        polynomial * exact_div(polynomial const * p, polynomial const * q) {
            TRACE("polynomial", tout << "exact division\np: "; p->display(tout, m_manager); tout << "\nq: "; q->display(tout, m_manager); tout << "\n";);
            if (is_zero(p))
                return const_cast<polynomial*>(p);
            SASSERT(!is_zero(q));
            m_som_buffer.reset();
            m_som_buffer2.reset();
            som_buffer & R = m_som_buffer;
            som_buffer & C = m_som_buffer2;
            R.add(p);
            unsigned max_q = q->graded_lex_max_pos();
            monomial * m_q = q->m(max_q);
            numeral const & a_q = q->a(max_q);
            monomial_ref m_r_q_ref(pm());
            scoped_numeral a_r_q(m_manager);
            while (true) {
                checkpoint();
                unsigned max_R = R.graded_lex_max_pos();
                if (max_R == UINT_MAX) {
                    // R is empty
                    R.reset();
                    return C.mk();
                }
                monomial const * m_r = R.m(max_R);
                numeral const & a_r  = R.a(max_R);
                monomial * m_r_q = 0;
                VERIFY(div(m_r, m_q, m_r_q));
                TRACE("polynomial", tout << "m_r: "; m_r->display(tout); tout << "\nm_q: "; m_q->display(tout); tout << "\n";
                      if (m_r_q) { tout << "m_r_q: "; m_r_q->display(tout); tout << "\n"; });
                m_r_q_ref = m_r_q;
                m_manager.div(a_r, a_q, a_r_q);
                C.add(a_r_q, m_r_q);       // C <- C + (a_r/a_q)*(m_r/m_q)
                m_manager.neg(a_r_q);
                R.addmul(a_r_q, m_r_q, q); // R <- R - (a_r/a_q)*(m_r/m_q)*Q
            }
        }
        
        // Return true if q divides p.
        bool divides(polynomial const * q, polynomial const * p) {
            TRACE("polynomial", tout << "divides\nq: "; q->display(tout, m_manager); tout << "\np: "; p->display(tout, m_manager); tout << "\n";);
            TRACE("divides", tout << "divides\nq: "; q->display(tout, m_manager); tout << "\np: "; p->display(tout, m_manager); tout << "\n";);
            if (is_zero(p))
                return true;
            SASSERT(!is_zero(q));
            m_som_buffer.reset();
            m_som_buffer2.reset();
            som_buffer & R = m_som_buffer;
            R.add(p);
            unsigned max_q = q->graded_lex_max_pos();
            monomial * m_q = q->m(max_q);
            numeral const & a_q = q->a(max_q);
            monomial_ref m_r_q_ref(pm());
            scoped_numeral a_r_q(m_manager);
            while (true) {
                checkpoint();
                unsigned max_R = R.graded_lex_max_pos();
                if (max_R == UINT_MAX) {
                    // R is empty
                    return true;
                }
                monomial const * m_r = R.m(max_R);
                numeral const & a_r  = R.a(max_R);
                monomial * m_r_q = 0;
                bool q_div_r = div(m_r, m_q, m_r_q);
                m_r_q_ref = m_r_q;
                TRACE("polynomial", tout << "m_r: "; m_r->display(tout); tout << "\nm_q: "; m_q->display(tout); tout << "\n";
                      if (m_r_q) { tout << "m_r_q: "; m_r_q->display(tout); tout << "\n"; });
                if (!q_div_r)
                    return false;
                if (!m_manager.divides(a_q, a_r))
                    return false;
                m_manager.div(a_r, a_q, a_r_q);
                m_manager.neg(a_r_q);
                R.addmul(a_r_q, m_r_q, q); // R <- R - (a_r/a_q)*(m_r/m_q)*Q
            }
        }

        void quasi_resultant(polynomial const * p, polynomial const * q, var x, polynomial_ref & r) {
            // For h_0 = p and h_1 = q, we compute the following sequence
            // using the pseudo remainder procedure
            // 
            // l(h_1)^d_1 * h_0     = q_1 * h_1 + h_2
            // l(h_2)^d_2 * h_1     = q_2 * h_2 + h_3
            // l(h_3)^d_3 * h_2     = q_3 * h_3 + h_4
            // ...
            // l(h_n)^d_n * h_{n-1} = q_n * h_n + h_{n+1}
            //
            // where 
            // degree(h_i, x) > 0 for all i in [0, n], and
            // degree(h_{n+1}, x) == 0
            //
            // l(h_i) is the leading coefficient of h_i with respect to variable x.
            // l(h_i) is in general a polynomial.
            // For example, l( y*x^2 + x^2 + y^2 x + 1 ) = y + 1
            // 
            // d^i is an unsigned integer. It is introduce by the pseudo remainder procedure
            // because the coefficients of x^k do not form a field. That is, they are elements of a polynomial ring Q[y_1, ..., y_n].
            // Their values are irrelevant for the correctness of this procedure.
            //
            // Observation 1:
            //   If h_0 and h_1 are polynomials in Q[y_1, ..., y_n, x],
            //   then h_{n+1} is a polynomial in Q[y_1, ..., y_n].
            //
            // Observation 2:
            //   For any (complex values) a_1, ..., a_n, b,
            //   if h_0(a_1, ..., a_n, b) = h_1(a_1, ..., a_n, b) = 0
            //   then for any h_i in the sequence, h_i(a_1, ..., a_n, b) = 0.
            //   In particular, h_{n+1}(a_1, ..., a_n) = 0
            // 
            // Observation 3:
            //   The procedure terminates because degree(h_i, x) > degree(h_{i+1}, x) 
            //   for all i >= 1
            //
            // Observation 4:
            //   If h_{n+1} is the zero polynomial, then 
            //   For any complex numbers a_1, ..., a_n
            //   the univariate polynomials p(a_1, ..., a_n, x) and q(a_1, ..., a_n, x) in C[x]
            //   have a common root.
            //   Reason:  
            //      If h_n(a_1, ..., a_n, x) is not the zero polynomial, then it is the GCD of p(a_1, ..., a_n, x) and q(a_1, ..., a_n, x),
            //      and it contains the common roots.
            //      If h_n(a_1, ..., a_n, x) is the zero polynomial, then 
            //      we consider h_{n-1}(a_1, ..., a_n, x). If it is not the zero polynomial then it is the GCD and we are done,
            //      otherwise we consider h_{n-2}(a_1, ..., a_n, x), and we continue the same process.
            //      Thus, eventually we find a h_i(a_1, ..., a_n, x) for i > 1 that is the GCD, or q(a_1, ..., a_n, x) is the zero polynomial,
            //      and any polynomial p(a_1, ..., a_n, x) has a common root with the zero polynomial.
            //
            SASSERT(degree(p, x) > 0);
            SASSERT(degree(q, x) > 0);
            polynomial_ref h_0(pm());
            polynomial_ref h_1(pm());
            polynomial_ref h_2(pm());
            if (degree(p, x) < degree(q, x))
                std::swap(p, q);
            h_0 = const_cast<polynomial*>(p);
            h_1 = const_cast<polynomial*>(q);
            unsigned d;
            while (true) {
                SASSERT(degree(h_1, x) <= degree(h_0, x));
                pseudo_remainder(h_0, h_1, x, d, h_2);
                TRACE("polynomial", tout << "h_0: " << h_0 << "\nh_1: " << h_1 << "\nh_2: " << h_2 << "\n";);
                SASSERT(degree(h_2, x) < degree(h_1, x));
                // We have that
                // l(h_1)^d h_0 = Q h_1 + h_2.
                // Q is the quotient of the division.
                // l(h_1) is the leading coefficient of h_1.
                // From this equation, we have that any zero of h_0 and h_1 is also a zero of h_2
                if (degree(h_2, x) == 0) {
                    r = h_2;
                    return;
                }
                h_0 = h_1;
                h_1 = h_2;
                // this computation will terminate since the pseudo_remainder guarantees that
                // degree(h_2, x) < degree(h_1, x)
            }
        }
        
        // sign = sign * (-1)^(deg_A * deg_B)
        static void update_sign(unsigned deg_A, unsigned deg_B, bool & sign) {
            if (deg_A % 2 == 0 || deg_B % 2 == 0)
                return;
            sign = !sign;
        }

        /**
           \brief Compute the resultant of p and q with respect to r.

           The Resultant is usually defined as the determinant of the
           Sylvester matrix for p and q. This matrix is built using
           the coefficients of p and q with respect to x.

           Given p and q polynomials in Q[y_1, ..., y_n, x], r is a polynomial in Q[y_1, ..., y_n].
           
           Property 1)
            If p and q can be written as
                 p = a_m * (x - alpha_1) * ... * (x - alpha_m)
                 q = b_n * (x - beta_1)  * ... * (x - beta_n)
            Then, 
              Res(p, q, x) = a_m^n * b_n^m * Product_{i in [1,m], j in [1, n]} (alpha_i - beta_j)
              
            Remark: if p and q are univariate polynomials, then alpha_i's and beta_j's are the roots
            of p and q, then Res(p, q, x) is the product of the differences of their roots modulo
            a constant.

           Property 2)
           For any (complex values) a_1, ..., a_n, b,
           if p(a_1, ..., a_n, b) = q(a_1, ..., a_n, b) = 0, then r(a_1, ..., b_n) = 0

           Property 3)
           There are polynomials U and V in Q[y_1, ..., y_n, x] s.t. 
           p*U + q*V = r
           s.t.
           deg(U, x) < deg(q, x) 
           and
           deg(V, x) < deg(p, x)

           We use Res(p, q, x) to denote the resultant of p and q.

           Property 4) (follows from 1)
           If Res(p, q, x) = 0, then p and q have a common divisor.
        
           Resultant Calculus:
             Let A and B be two polynomials of degree m and n on variable x.
             Let c and d be numerals.

             Res(A, B, x)  = (-1)^(m*n) * Res(B, A, x)
             Res(cA, B, x) = c^n * Res(A, B, x)
             Res(c, B, x)  = c^n
             Res(0, B, x)  = 0 if n > 0
             Res(c, d, x)  = 1
             Res(A, B1*B2, x) = Res(A, B1, x)*Res(A, B2, x)
             Res(A, A*Q + B, x)  = coeff(A, x)^(l-n) * Res(A, B, x)   where l = deg(A*Q + R)
                          
             The last equation suggests an approach for computing the Resultant using
             pseudo-division instead of determinants.

             Given A and B s.t. degree(A, x) = m >= n = degree(B, x)
             Then  lc^d * A = Q * B + R
             where lc = coeff(B, x), and
                   pseudo_division(A, B, x, d, Q, R);
                   r = degree(R)
             Then we have:
             (lc^d)^n * Res(A, B) = Res(A * l^d, B) = Res(Q * B + R, B) = (-1)^(m*n) * Res(B, Q * B + R) = (-1)^(m*n) * lc^(m-r) * Res(B, R)      

             So,
             lc^(d*n) * Res(A, B) = (-1)^(m*n) * lc^(m-r) * Res(B, R)

             From the pseudo-division algorithm, we have that:
                 1) 1 <= d <= m - n + 1
                 2) 0 <= r <  n <= m

                 d*n >= m >= m-r

             So, if d*n == m-r 
                    Res(A, B) = (-1)^(m*n) * Res(R, B)
                 if d*n >  m-r
                    Res(A, B) = (-1)^(m*n) * exact_div(Res(R, B), lc^(d*n - m + r))
                 if d*n <  m-r
                    Res(A, B) = (-1)^(m*n) * mul(Res(R, B), lc^(m - r - d * n))
        */
        void resultant(polynomial const * p, polynomial const * q, var x, polynomial_ref & result) {
            polynomial_ref A(pm());
            polynomial_ref B(pm());
            A = const_cast<polynomial*>(p);
            B = const_cast<polynomial*>(q);
            TRACE("resultant", tout << "resultant(A, B, x)\nA: " << A << "\nB: " << B << "\nx: " << x << "\n";);
            // Res(0, B) = Res(A, 0) = 0
            if (is_zero(A) || is_zero(B)) {
                result = mk_zero();
                return;
            }
            // Res(c, d, x)  = 1             c and d are constants
            // Res(c, B, x)  = c^{deg(B)}
            if (is_const(A)) {
                if (is_const(B))
                    result = mk_one();
                else
                    pw(A, degree(B, x), result);
                return;
            }
            // Res(A, d, x)  = d^{deg(A)}
            if (is_const(B)) {
                pw(B, degree(A, x), result);
                return;
            }
            
            // decompose A and B into
            //   A = iA*cA*ppA
            //   B = iB*cB*ppB
            scoped_numeral iA(m_manager), iB(m_manager);
            polynomial_ref cA(pm()), cB(pm());
            polynomial_ref ppA(pm()), ppB(pm());
            iccp(A, x, iA, cA, ppA);
            iccp(B, x, iB, cB, ppB);
            cA = mul(iA, cA);
            cB = mul(iB, cB);
            // At this point, A = cA*ppA and B = cB*ppB,  where cA and cB are the content of A and B, and ppA and ppB the primitive polynomials
            polynomial_ref t(pm());
            // t <- cA^{deg(B)}*cB^{deg(A)}
            pw(cA, degree(B, x), cA);
            pw(cB, degree(A, x), cB);
            t = mul(cA, cB);
            A = ppA;
            B = ppB;
            // 
            TRACE("resultant", tout << "resultant(A, B, x) after normalization\nA: " << A << "\nB: " << B << "\nx: " << x << "\n";
                  tout << "t: " << t << "\n";);

            int s = 1;
            unsigned degA = degree(A, x);
            unsigned degB = degree(B, x);
            if (degA < degB) {
                A.swap(B);
                if (degA % 2 == 1 && degB % 2 == 1)
                    s = -1;
            }

            polynomial_ref R(pm());
            polynomial_ref g(pm());
            polynomial_ref h(pm());
            polynomial_ref new_h(pm());
            // g <- 1
            g = mk_one();
            // h <- 1
            h = mk_one();

            while (true) {
                TRACE("resultant", tout << "A: " << A << "\nB: " << B << "\n";);
                degA = degree(A, x);
                degB = degree(B, x);
                SASSERT(degA >= degB);
                unsigned delta = degA - degB;
                if (degA % 2 == 1 && degB % 2 == 1)
                    s = -s;
                // lc(B)^delta+1 A = BQ + R
                exact_pseudo_remainder(A, B, x, R);
                A = B;
                // B <- R/g*h^{delta}
                B = exact_div(R, g);
                for (unsigned i = 0; i < delta; i++)
                    B = exact_div(B, h);
                // g <- lc(A)
                g = lc(A, x);
                // h <- g^delta * h^{1-delta}
                new_h = mk_one();
                pw(g, delta, new_h);
                if (delta > 1) {
                    for (unsigned i = 0; i < delta - 1; i++)
                        new_h = exact_div(new_h, h);
                }
                h = new_h;
                if (degree(B, x) == 0) {
                    unsigned degA = degree(A, x);
                    // h <- lc(B)^{deg(A)} * h^{1-deg(A)}
                    new_h = lc(B, x);
                    pw(new_h, degA, new_h);
                    if (degA > 1) {
                        for (unsigned i = 0; i < degA - 1; i++)
                            new_h = exact_div(new_h, h);
                    }
                    h = new_h;
                    // result <- s*t*h
                    result = mul(t, h);
                    if (s < 0)
                        result = neg(result);
                    return;
                }
            }
        }

        /**
           \brief Return the discriminant of p with respect to x.

           Disc(p, x) = (-1)^(m * (m-1)/2) * Resultant(p, dp/dx, x) / coeff(p, x)
           dp/dx is the derivative of p with respect to x.
        */
        void discriminant(polynomial const * p, var x, polynomial_ref & r) {
            polynomial_ref p_prime(pm());
            unsigned m = degree(p, x);
            if (m == 0) {
                r = m_zero;
                return;
            }
            p_prime = derivative(p, x);
            resultant(p, p_prime, x, r);
            bool sign = (static_cast<uint64>(m) * static_cast<uint64>(m-1))%4 != 0;
            TRACE("resultant", tout << "discriminant sign: " << sign << "\n";);
            scoped_numeral lc(m_manager);
            if (const_coeff(p, x, m, lc)) {
                if (sign)
                    m_manager.neg(lc);
                r = div(r, lc);
            }
            else {
                if (sign)
                    r = neg(r);
                polynomial_ref c(pm());
                c = coeff(p, x, m);
                r = exact_div(r, c);
            }
        }

        void subresultant_chain(polynomial const * p, polynomial const * q, var x, polynomial_ref_vector & sRes) {
            // REMARK: the code does not work if deg_p == deg_q
            unsigned deg_p = degree(p, x);
            unsigned deg_q = degree(q, x);
            if (deg_p < deg_q) {
                std::swap(p, q);
                std::swap(deg_p, deg_q);
            }
            SASSERT(deg_p > 0);
            unsigned n = deg_p; 
            sRes.reset();
            sRes.resize(n + 1); // the sequence is from 0 ... n
            sRes.set(n, const_cast<polynomial*>(p));
            sRes.set(n - 1, const_cast<polynomial*>(q));

            polynomial_ref R_j_plus_1(pm());
            polynomial_ref prem(pm());
            polynomial_ref newS(pm());

            unsigned j = n - 1;
            while (j > 0) {
                SASSERT(degree(sRes.get(j+1), x) == j+1); // sRes_{j+1} is regular
                if (j == n-1) 
                    R_j_plus_1 = mk_one(); // by definition of PSC chain
                else
                    R_j_plus_1 = coeff(sRes.get(j+1), x, j+1);
                unsigned r = degree(sRes.get(j), x);
                if (r == j) {
                    // sRes_j is regular
                    
                    exact_pseudo_remainder(sRes.get(j+1), sRes.get(j), x, prem);
                    TRACE("psc", tout << "j: " << j << "\nsRes_j+1: "; sRes.get(j+1)->display(tout, m_manager);
                          tout << "\nsRes_j: "; sRes.get(j)->display(tout, m_manager); 
                          tout << "\nprem: " << prem << "\n";);
                    // sRes_{j-1} = prem/R_j_plus_1^2
                    newS = exact_div(prem, R_j_plus_1);
                    newS = exact_div(newS, R_j_plus_1);
                    sRes.set(j-1, newS);
                    j--;
                }
                else {
                    SASSERT(r < j);
                    // sRes_j is defective
                    
                    // sRes_{j-1} = sRes_{j-2} = ... = sRes_{r+1} = 0
                    for (int i = j-1; i >= static_cast<int>(r+1); i--)
                        sRes.set(i, mk_zero());

                    // sRes_r = lc(sRes_j)^{j-r} * sRes_j / R_j_plus_1^{j-r}
                    newS = lc(sRes.get(j), x);
                    pw(newS, j-r, newS);
                    newS = mul(newS, sRes.get(j));
                    for (unsigned i = 0; i < j-r; i++)
                        newS = exact_div(newS, R_j_plus_1);
                    sRes.set(r, newS);
                    
                    // If r > 0, we also compute sRes_{r-1}
                    if (r > 0) {
                        exact_pseudo_remainder(sRes.get(j+1), sRes.get(j), x, prem);
                        // sRes_{r-1} = prem/(-R_j_plus_1)^{j-r+2}
                        newS = prem;
                        for (unsigned i = 0; i < j-r+2; i++)
                            newS = exact_div(newS, R_j_plus_1);
                        if ((j-r+2)%2 == 1)
                            newS = neg(newS);
                        sRes.set(r-1, newS);
                        j = r - 1;
                    }
                    else {
                        j = 0;
                    }
                }
            }
        }

        void psc_chain1(polynomial const * p, polynomial const * q, var x, polynomial_ref_vector & S) {
            subresultant_chain(p, q, x, S);
            unsigned sz = S.size();
            TRACE("psc", tout << "subresultant_chain\n"; 
                  for (unsigned i = 0; i < sz; i++) { tout << "i: " << i << " "; S.get(i)->display(tout, m_manager); tout << "\n"; });
            for (unsigned i = 0; i < sz - 1; i++) {
                S.set(i, coeff(S.get(i), x, i));
            }
            S.set(sz-1, mk_one());
        }

        // Store in S a list of the non-zero principal subresultant coefficients of A and B
        // If i < j then psc_{i}(A,B) precedes psc_{j}(A,B) in S.
        // The leading coefficients of A and B are not included in S.
        void psc_chain2(polynomial const * A, polynomial const * B, var x, polynomial_ref_vector & S) {
            polynomial_ref G1(pm());
            polynomial_ref G2(pm());
            polynomial_ref G3(pm());
            polynomial_ref Gh3(pm());
            polynomial_ref g1(pm()), h0(pm()), hs0(pm()), h1(pm()), hs1(pm());
            unsigned n1 = degree(A, x);
            unsigned n2 = degree(B, x);
            if (n1 > n2) {
                G1 = const_cast<polynomial*>(A);
                G2 = const_cast<polynomial*>(B); 
            }
            else {
                G1 = const_cast<polynomial*>(B);
                G2 = const_cast<polynomial*>(A); 
                std::swap(n1, n2);
            }
            unsigned d0 = 0;
            unsigned d1 = n1 - n2;
            unsigned i  = 1;
            unsigned n3; 
            S.reset();
            while (true) {
                // Compute Gh_{i+2}
                if (!is_zero(G2)) {
                    exact_pseudo_remainder(G1, G2, x, Gh3);
                    n3 = degree(Gh3, x);
                    if (!is_zero(Gh3) && d1%2 == 0) 
                        Gh3 = neg(Gh3);
                }
                
                // Compute hi
                if (i > 1) {
                    g1 = lc(G1, x);
                    pw(g1, d0, h1);
                    if (i > 2) {
                        pw(h0, d0 - 1, hs0);
                        h1 = exact_div(h1, hs0);
                        S.push_back(h1);
                        if (is_zero(G2)) {
                            std::reverse(S.c_ptr(), S.c_ptr() + S.size());
                            return;
                        }
                    } 
                }
                
                // Compute G_{i+2}
                if (i == 1 || is_zero(Gh3)) {
                    G3 = Gh3;
                }
                else {
                    pw(h1, d1, hs1);
                    hs1 = mul(g1, hs1);
                    G3  = exact_div(Gh3, hs1);
                    hs1 = 0; 
                }
                
                // prepare for next iteration
                n1 = n2;
                n2 = n3;
                d0 = d1;
                d1 = n1 - n2;
                G1 = G2;
                G2 = G3;
                if (i > 1)
                    h0 = h1;
                i = i + 1;
            }
        }

        // Optimized calculation of S_e using "Dichotomous Lazard" 
        void Se_Lazard(unsigned d, polynomial const * lc_S_d, polynomial const * S_d_1, var x, polynomial_ref & S_e) {
            unsigned n = d - degree(S_d_1, x) - 1;
            TRACE("Lazard", tout << "lc_S_d: "; lc_S_d->display(tout, m_manager); tout << "\nS_d_1: "; S_d_1->display(tout, m_manager);
                  tout << "\nn: " << n << "\n";);
            if (n == 0) {
                S_e = const_cast<polynomial*>(S_d_1);
                return;
            }
            polynomial_ref X(pm());
            X = lc(S_d_1, x);
            polynomial const * Y = lc_S_d;
            unsigned a = 1 << log2(n);
            TRACE("Lazard", tout << "a: " << a << "\n";);
            SASSERT(a <= n); 
            SASSERT(n < 2*a);
            polynomial_ref C(pm());
            C = X;
            n = n - a;
            while (a != 1) {
                a = a / 2;
                // C <- C^2/Y
                C = mul(C, C);
                C = exact_div(C, Y);
                TRACE("Lazard", tout << "loop a: " << a << "\nC : " << C << "\n";);
                if (n >= a) {
                    // C <- C*X/Y
                    C = mul(C, X);
                    C = exact_div(C, Y);
                    n = n - a;
                    TRACE("Lazard", tout << "if, C: " << C << "\n";);
                }
            }
            TRACE("Lazard", tout << "C: " << C << "\nY: " << Y << "\n";);
            S_e = mul(C, S_d_1);
            S_e = exact_div(S_e, Y);
        }

        // Optimized calculation of S_{e-1} for optimized psc_chain
        void optimized_S_e_1(unsigned d, unsigned e, polynomial const * A, polynomial const * S_d_1, polynomial const * S_e, polynomial const * s, 
                             var x, polynomial_ref & S_e_1) {
            SASSERT(d == degree(A, x));
            SASSERT(e == degree(S_d_1, x));
            polynomial_ref c_d_1(pm()), s_e(pm()), x_j(pm()), tmp(pm());
            c_d_1 = lc(S_d_1, x);
            s_e = lc(S_e, x);
            polynomial_ref_buffer H(pm());
            x_j = mk_one();
            for (unsigned j = 0; j <= e - 1; j++) {
                // H_j <- s_e * x^j
                x_j = mk_polynomial(x, j);
                H.push_back(mul(s_e, x_j));
            }
            SASSERT(H.size() == e);
            // H_e <- s_e * x^e - S_e
            x_j = mk_polynomial(x, e);
            x_j = mul(s_e, x_j);
            H.push_back(sub(x_j, S_e));
            SASSERT(H.size() == e+1);
            polynomial_ref x_pol(pm()), xH(pm()), xHe(pm());
            x_pol = mk_polynomial(x, 1);
            for (unsigned j = e + 1; j <= d - 1; j++) {
                // H_j <- x H_{j-1} - (coeff(x H_{j-1}, e) * S_{d-1})/c_{d-1}
                xH = mul(x_pol, H[j-1]);
                xHe = coeff(xH, x, e);
                tmp = mul(xHe, S_d_1);
                tmp = exact_div(tmp, c_d_1);
                H.push_back(sub(xH, tmp));
            }
            SASSERT(H.size() == d);
            // D <- (Sum coeff(A,j) * H[j])/lc(A)
            polynomial_ref D(pm());
            D = mk_zero();
            for (unsigned j = 0; j < d; j++) {
                tmp = coeff(A, x, j);
                tmp = mul(tmp, H[j]);
                D = add(D, tmp);
            }
            polynomial_ref lc_A(pm());
            lc_A = lc(A, x);
            D = exact_div(D, lc_A);
            // S_e_1 = (-1)^(d-e+1) [c_{d-1} (x H[j-1] + D) - coeff(x H[j-1], e)*S_d-1]/s
            xH    = mul(x_pol, H[d-1]);
            xHe   = coeff(xH, x, e);
            xHe   = mul(xHe, S_d_1);
            S_e_1 = add(xH, D);
            S_e_1 = mul(c_d_1, S_e_1);
            S_e_1 = sub(S_e_1, xHe);
            S_e_1 = exact_div(S_e_1, s);
            if ((d-e+1) % 2 == 1)
                S_e_1 = neg(S_e_1);
        } 

        void psc_chain_optimized_core(polynomial const * P, polynomial const * Q, var x, polynomial_ref_vector & S) {
            TRACE("psc_chain_classic", tout << "P: "; P->display(tout, m_manager); tout << "\nQ: "; Q->display(tout, m_manager); tout << "\n";);
            unsigned degP = degree(P, x);
            unsigned degQ = degree(Q, x);
            SASSERT(degP >= degQ);
            polynomial_ref A(pm()), B(pm()), C(pm()), minus_Q(pm()), lc_Q(pm()), ps(pm());
                    
            lc_Q = lc(Q, x);
            polynomial_ref s(pm());
            // s <- lc(Q)^(deg(P)-deg(Q))
            pw(lc_Q, degP - degQ, s);
            minus_Q = neg(Q);
            // A <- Q
            A = const_cast<polynomial*>(Q);
            // B <- prem(P, -Q)
            exact_pseudo_remainder(P, minus_Q, x, B);
            while (true) {
                unsigned d = degree(A, x);
                unsigned e = degree(B, x);
                if (is_zero(B))
                    return;
                TRACE("psc_chain_classic", tout << "A: " << A << "\nB: " << B << "\ns: " << s << "\nd: " << d << ", e: " << e << "\n";);
                // B is S_{d-1}
                ps = coeff(B, x, d-1);
                if (!is_zero(ps))
                    S.push_back(ps);
                unsigned delta = d - e;
                if (delta > 1) {
                    // C <- S_e
                    // Optimized S_e calculation
                    // s = lc(S_d) at this point
                    Se_Lazard(d, s, B, x, C);

                    // C is S_e
                    ps = coeff(C, x, e);
                    if (!is_zero(ps))
                        S.push_back(ps);
                }
                else {
                    SASSERT(delta == 0 || delta == 1);
                    C = B;
                }
                if (e == 0)
                    return;
                // B <- optimized S_e_1
                optimized_S_e_1(d, e, A, B, C, s, x, B);
                // A <- C
                A = C;
                // s <- lc(A)
                s = lc(A, x);
            }
        }

        void psc_chain_optimized(polynomial const * P, polynomial const * Q, var x, polynomial_ref_vector & S) {
            SASSERT(degree(P, x) > 0);
            SASSERT(degree(Q, x) > 0);
            S.reset();
            if (degree(P, x) >= degree(Q, x))
                psc_chain_optimized_core(P, Q, x, S);
            else
                psc_chain_optimized_core(Q, P, x, S); 
            if (S.empty())
                S.push_back(mk_zero());
            std::reverse(S.c_ptr(), S.c_ptr() + S.size());
        }

        void psc_chain_classic_core(polynomial const * P, polynomial const * Q, var x, polynomial_ref_vector & S) {
            TRACE("psc_chain_classic", tout << "P: "; P->display(tout, m_manager); tout << "\nQ: "; Q->display(tout, m_manager); tout << "\n";);
            unsigned degP = degree(P, x);
            unsigned degQ = degree(Q, x);
            SASSERT(degP >= degQ);
            polynomial_ref A(pm()), B(pm()), C(pm()), minus_Q(pm()), lc_Q(pm()), lc_B(pm()), lc_A(pm());
            polynomial_ref tmp1(pm()), tmp2(pm()), s_delta(pm()), minus_B(pm()), ps(pm());
                    
            lc_Q = lc(Q, x);
            polynomial_ref s(pm());
            // s <- lc(Q)^(deg(P)-deg(Q))
            pw(lc_Q, degP - degQ, s);
            minus_Q = neg(Q);
            // A <- Q
            A = const_cast<polynomial*>(Q);
            // B <- prem(P, -Q)
            exact_pseudo_remainder(P, minus_Q, x, B);
            while (true) {
                unsigned d = degree(A, x);
                unsigned e = degree(B, x);
                if (is_zero(B))
                    return;
                TRACE("psc_chain_classic", tout << "A: " << A << "\nB: " << B << "\ns: " << s << "\nd: " << d << ", e: " << e << "\n";);
                // B is S_{d-1}
                ps = coeff(B, x, d-1);
                if (!is_zero(ps))
                    S.push_back(ps);
                unsigned delta = d - e;
                if (delta > 1) {
                    // C <- S_e
                    // Standard S_e calculation
                    // C <- (lc(B)^(delta-1) B) / s^(delta-1)
                    lc_B = lc(B, x);
                    pw(lc_B, delta-1, lc_B);
                    lc_B = mul(lc_B, B);
                    pw(s, delta - 1, s_delta); // s_delta <- s^(delta-1)
                    C = exact_div(lc_B, s_delta);

                    // s_delta <- s^delta
                    s_delta = mul(s_delta, s);
                    // C is S_e
                    ps = coeff(C, x, e);
                    if (!is_zero(ps))
                        S.push_back(ps);
                   
                }
                else {
                    SASSERT(delta == 0 || delta == 1);
                    C = B;
                    // s_delta <- s^delta
                    pw(s, delta, s_delta);
                }
                if (e == 0)
                    return;
                // B <- prem(A, -B)/(s^delta * lc(A)
                lc_A = lc(A, x);
                minus_B = neg(B);
                exact_pseudo_remainder(A, minus_B, x, tmp1);
                tmp2 = mul(lc_A, s_delta);
                B = exact_div(tmp1, tmp2);
                // A <- C
                A = C;
                // s <- lc(A)
                s = lc(A, x);
            }
        }

        void psc_chain_classic(polynomial const * P, polynomial const * Q, var x, polynomial_ref_vector & S) {
            SASSERT(degree(P, x) > 0);
            SASSERT(degree(Q, x) > 0);
            S.reset();
            if (degree(P, x) >= degree(Q, x))
                psc_chain_classic_core(P, Q, x, S);
            else
                psc_chain_classic_core(Q, P, x, S); 
            if (S.empty())
                S.push_back(mk_zero());
            std::reverse(S.c_ptr(), S.c_ptr() + S.size());
        }

        void psc_chain(polynomial const * A, polynomial const * B, var x, polynomial_ref_vector & S) {
            // psc_chain1(A, B, x, S);
            // psc_chain2(A, B, x, S);
            // psc_chain_classic(A, B, x, S);
            psc_chain_optimized(A, B, x, S);
        }

        polynomial * normalize(polynomial const * p) {
            if (is_zero(p))
                return const_cast<polynomial*>(p);
            unsigned sz = p->size();
            if (m().modular()) {
                unsigned i = 0;
                for (; i < sz; i++) {
                    if (!m().is_p_normalized(p->a(i)))
                        break;
                }
                if (i < sz) {
                    m_cheap_som_buffer.reset();
                    scoped_numeral a(m_manager);
                    for (unsigned i = 0; i < sz; i++) {
                        monomial * m = p->m(i);
                        m_manager.set(a, p->a(i));
                        m_cheap_som_buffer.add_reset(a, m);
                    }
                    m_cheap_som_buffer.normalize();
                    return m_cheap_som_buffer.mk();
                }
            }
            scoped_numeral g(m_manager);
            m_manager.gcd(sz, p->as(), g);
            if (m_manager.is_one(g))
                return const_cast<polynomial*>(p);
            m_cheap_som_buffer.reset();
            scoped_numeral a(m_manager);
            for (unsigned i = 0; i < sz; i++) {
                monomial * m = p->m(i);
                m_manager.div(p->a(i), g, a);
                m_cheap_som_buffer.add_reset(a, m);
            }
            return m_cheap_som_buffer.mk();
        }

        polynomial * neg(polynomial const * p) {
            SASSERT(m_cheap_som_buffer.empty());
            scoped_numeral minus_a(m_manager);
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                m_manager.set(minus_a, p->a(i));
                m_manager.neg(minus_a);
                m_cheap_som_buffer.add(minus_a, p->m(i));
            }
            return m_cheap_som_buffer.mk();
        }

        // Return true if is a(i)*m(i) is a perfect square.
        // Store sqrt of a(i) in sqrt_a
        bool is_perfect_square(polynomial const * p, unsigned i, numeral & sqrt_a) {
            monomial * m = p->m(i);
            if (!m->is_square())
                return false; 
            numeral const & a = p->a(i);
            if (!m_manager.is_perfect_square(a, sqrt_a))
                return false;
            return true;
        }

        bool sqrt(polynomial const * p, polynomial_ref & r) {
            SASSERT(p != 0);
            if (is_zero(p)) {
                r = const_cast<polynomial*>(p);
                return true;
            }
            scoped_numeral a(m_manager);
            TRACE("sqrt_bug", 
                  tout << "sqrt:    "; p->display(tout, m_manager); tout << "\n";
                  tout << "min pos: " <<  p->graded_lex_min_pos() << "\n";
                  tout << "max pos: " <<  p->graded_lex_max_pos() << "\n";);
            // Quick Check: the minimal monomial must be a perfect square
            unsigned min_pos = p->graded_lex_min_pos();
            if (!is_perfect_square(p, min_pos, a))
                return false;
            // Quick Check: the maximal monomial must be a perfect square
            unsigned max_pos = p->graded_lex_max_pos();
            if (!is_perfect_square(p, max_pos, a))
                return false;
            // Compute square root using
            //    (m_1 + ... + m_k)^2 ==
            //         (m_1)m_1
            //         (2m_1 + m_2)m_2
            //         (2m_1 + 2m_2 + m_3)m_3
            //         ...
            //
            // R <- m1
            // C <- p - m1*m1
            // while (true) {
            //    if (is_zero(C))
            //       return true;
            //    m <- biggest monomial in C
            //    if (m is not divisible by 2*m1)
            //       return false;
            //    m' <- m/2m1
            //    C  <- C - 2*R*m' - m'*m'
            //    R  <- R + m'
            // }
            //
            // The loop above terminates because total degree of the
            // maximal monomial in C decreases in each iteration.
            monomial * m1 = sqrt(p->m(max_pos));
            SASSERT(m1 != 0);
            som_buffer & R = m_som_buffer;
            som_buffer & C = m_som_buffer2;
            R.reset(); 
            C.reset();
            numeral two;
            m_manager.set(two, 2);
            scoped_numeral two_a(m_manager);
            m_manager.mul(a, two, two_a);
            // R <- a * m1
            R.add(a, m1);
            // C <- p - m1*m1
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                if (i == max_pos)
                    continue;
                C.add(p->a(i), p->m(i));
            } 
            scoped_numeral a_i(m_manager);
            scoped_numeral aux(m_manager);
            monomial_ref m_aux(pm());
            while (true) {
                checkpoint();
                TRACE("sqrt_bug", tout << "R: "; R.display(tout); tout << "C: "; C.display(tout););
                unsigned curr_max = C.graded_lex_max_pos();
                if (curr_max == UINT_MAX) {
                    // C is empty
                    C.reset();
                    r = R.mk();
                    return true;
                }
                monomial * m = C.m(curr_max);
                monomial * m_i;
                if (!div(m, m1, m_i)) {
                    // m1 does not divide maximal monomial of C.
                    R.reset();
                    C.reset();
                    return false;
                }
                // 2*a does not divide maximal coefficient of C
                if (!m_manager.divides(two_a, C.a(curr_max)))
                    return false;
                m_manager.div(C.a(curr_max), two_a, a_i);
            
                // C  <- C - 2*R*a_i*m_i - a_i*a_i*m_i*m_i
                unsigned R_sz = R.size();
                for (unsigned j = 0; j < R_sz; j++) {
                    if (m_manager.is_zero(R.a(j)))
                        continue;
                    m_manager.mul(R.a(j), a_i, aux);
                    m_manager.mul(aux, two, aux);
                    m_manager.neg(aux);
                    m_aux = mul(R.m(j), m_i);
                    C.add(aux, m_aux);
                }
                m_manager.mul(a_i, a_i, aux);
                m_manager.neg(aux);
                m_aux = mul(m_i, m_i);
                C.add(aux, m_aux);
                // R <- R + a_i*m_i
                R.add(a_i, m_i);
            }
        }

        void rename(unsigned sz, var const * xs) {
            TRACE("rename", for (unsigned i = 0; i < sz; i++) tout << xs[i] << " "; tout << "\n";
                  tout << "polynomials before rename\n";
                  for (unsigned i = 0; i < m_polynomials.size(); i++) {
                      if (m_polynomials[i] == 0)
                          continue; 
                      m_polynomials[i]->display(tout, m_manager);
                      tout << "\n";
                  });
            mm().rename(sz, xs);
            // we must traverse the polynomial vector, and update the first monomial,
            // since it may not contain anymore the maximal variable with maximal degree.
            polynomial_vector::iterator it2  = m_polynomials.begin();
            polynomial_vector::iterator end2 = m_polynomials.end();
            for (; it2 != end2; ++it2) {
                polynomial * p = *it2;
                if (p == 0)
                    continue;
                p->make_first_maximal();
                SASSERT(p->size() <= 1 || !p->lex_sorted());
            }
            TRACE("rename", 
                  tout << "polynomials after rename\n";
                  for (unsigned i = 0; i < m_polynomials.size(); i++) {
                      if (m_polynomials[i] == 0)
                          continue;
                      m_polynomials[i]->display(tout, m_manager);
                      tout << "\n";
                  });
        }

        bool is_pos(polynomial const * p) {
            bool found_unit = false;
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                if (!p->m(i)->is_power_of_two())
                    return false;
                if (p->m(i) == mk_unit())
                    found_unit = true;
                if (!m_manager.is_pos(p->a(i)))
                    return false;
            }
            return found_unit;
        }

        bool is_neg(polynomial const * p) {
            bool found_unit = false;
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                if (!p->m(i)->is_power_of_two())
                    return false;
                if (p->m(i) == mk_unit())
                    found_unit = true;
                if (!m_manager.is_neg(p->a(i)))
                    return false;
            }
            return found_unit;
        }
        
        bool is_nonpos(polynomial const * p) {
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                if (!p->m(i)->is_power_of_two())
                    return false;
                if (!m_manager.is_neg(p->a(i)))
                    return false;
            }
            return true;
        }

        bool is_nonneg(polynomial const * p) {
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                if (!p->m(i)->is_power_of_two())
                    return false;
                if (!m_manager.is_pos(p->a(i)))
                    return false;
            }
            return true;
        }
      
        // Functor used to compute the maximal degree of each variable in a polynomial p.
        class var_max_degree {
            unsigned_vector    m_max_degree;  
            var_vector         m_xs;
        public:
            void init(polynomial const * p) {
                unsigned sz = p->size();
                for (unsigned i = 0; i < sz; i++) {
                    monomial * m = p->m(i);
                    unsigned msz = m->size();
                    for (unsigned j = 0; j < msz; j++) {
                        var x = m->get_var(j);
                        unsigned k = m->degree(j);
                        unsigned max_k = m_max_degree.get(x, 0);
                        if (k > max_k) {
                            if (max_k == 0)
                                m_xs.push_back(x);
                            m_max_degree.setx(x, m->degree(j), 0);
                        }
                    }
                }
            }
            
            void reset() {
                unsigned sz = m_xs.size();
                for (unsigned i = 0; i < sz; i++) {
                    m_max_degree[m_xs[i]] = 0;
                }
                m_xs.reset();
            }

            unsigned operator()(var x) const {
                return m_max_degree.get(x, 0);
            }

            unsigned num_vars() const { return m_xs.size(); }
            
            var const * vars() const { return m_xs.c_ptr(); }
        };

        struct scoped_var_max_degree {
            var_max_degree & m;
            scoped_var_max_degree(var_max_degree & _m, polynomial const * p):
                m(_m) {
                m.init(p);
            }
            ~scoped_var_max_degree() {
                m.reset();
            }
            unsigned operator()(var x) const {
                return m(x);
            }
            unsigned num_vars() const { return m.num_vars(); }
            var const * vars() const { return m.vars(); }
        };

        var_max_degree  m_var_max_degree;

        // This method uses the tmp fields: m_found_vars, m_var_max_degree.
        polynomial * substitute(polynomial const * p, var2mpq const & x2v) {
            scoped_var_max_degree var2max_degree(m_var_max_degree, p);
            unsigned xs_sz = var2max_degree.num_vars();
            var const * xs = var2max_degree.vars();
            bool found = false;
            for (unsigned i = 0; i < xs_sz; i++) {
                var x = xs[i];
                if (x2v.contains(x) && var2max_degree(x) > 0) {
                    found = true;
                    break;
                }
            }
            if (!found)
                return const_cast<polynomial*>(p);
            scoped_numeral new_a(m_manager);
            scoped_numeral tmp(m_manager);
            m_found_vars.reserve(num_vars(), false);
            m_som_buffer.reset();
            som_buffer & R       = m_som_buffer;
            tmp_monomial & new_m = m_tmp1; 
            unsigned sz    = p->size();
            for (unsigned i = 0; i < sz; i++) {
                monomial * m = p->m(i);
                unsigned msz = m->size();
                unsigned new_msz = 0;
                m_manager.set(new_a, p->a(i));
                new_m.reserve(msz);
                for (unsigned j = 0; j < msz; j++) {
                    var x = m->get_var(j);
                    unsigned k = m->degree(j);
                    if (x2v.contains(x)) {
                        unsigned max_k = var2max_degree(x);
                        m_found_vars[x] = true;
                        mpq const & x_value = x2v(x);
                        m_manager.power(x_value.numerator(), k, tmp);
                        m_manager.mul(tmp, new_a, new_a);
                        if (k < max_k) {
                            m_manager.power(x_value.denominator(), max_k - k, tmp);
                            m_manager.mul(tmp, new_a, new_a);
                        }
                    }
                    else {
                        new_m.set_power(new_msz, m->get_power(j));
                        new_msz++;
                    }
                }
                // For each variable x in xs that does not occur in m, I
                // should include (x2v(x).denominator())^{var2max_degree(x)} to new_a
                for (unsigned j = 0; j < xs_sz; j++) {
                    var x = xs[j];
                    if (m_found_vars[x])
                        continue;
                    if (x2v.contains(x)) {
                        m_manager.power(x2v(x).denominator(), var2max_degree(x), tmp);
                        m_manager.mul(tmp, new_a, new_a);
                    }
                }
                // Reset m_found_vars
                for (unsigned j = 0; j < msz; j++) {
                    var x = m->get_var(j);
                    m_found_vars[x] = false;
                }
                // Add new_a*new_m to R
                if (!m_manager.is_zero(new_a)) {
                    new_m.set_size(new_msz);
                    R.add(new_a, mk_monomial(new_m));
                }
            }
            return R.mk(true);
        }

        struct var_pos {
            unsigned_vector m_pos;
            
            void init(unsigned sz, var const * xs) {
                for (unsigned i = 0; i < sz; i++) {
                    SASSERT(m_pos.get(xs[i], UINT_MAX) == UINT_MAX);
                    m_pos.setx(xs[i], i, UINT_MAX);
                }
            }
            
            void reset(unsigned sz, var const * xs) {
                for (unsigned i = 0; i < sz; i++) {
                    SASSERT(m_pos.get(xs[i], UINT_MAX) != UINT_MAX);
                    m_pos[xs[i]] = UINT_MAX;
                }
            }

            unsigned operator()(var x) const { return m_pos.get(x, UINT_MAX); }
        };

        struct scoped_var_pos {
            var_pos &          m;
            unsigned           m_xs_sz;
            var const *        m_xs;
            scoped_var_pos(var_pos & p, unsigned xs_sz, var const * xs):
                m(p),
                m_xs_sz(xs_sz),
                m_xs(xs) {
                m.init(m_xs_sz, m_xs);
            }
            ~scoped_var_pos() {
                m.reset(m_xs_sz, m_xs);
            }
            unsigned operator()(var x) const { return m(x); }
        };

        var_pos         m_var_pos;

        struct var2mpq_wrapper : public var2mpq {
            scoped_var_pos  m_var_pos;
            mpq const * m_vs;
            var2mpq_wrapper(unsigned xs_sz, var const * xs, mpq const * vs, var_pos & buffer):
                m_var_pos(buffer, xs_sz, xs),
                m_vs(vs) {
            }
            virtual unsynch_mpq_manager & m() const { UNREACHABLE(); static unsynch_mpq_manager m; return m; }
            virtual bool contains(var x) const { return m_var_pos(x) != UINT_MAX; }
            virtual mpq const & operator()(var x) const { return m_vs[m_var_pos(x)]; }
        }; 
        
        polynomial * substitute(polynomial const * p, unsigned xs_sz, var const * xs, mpq const * vs) {
            var2mpq_wrapper x2v(xs_sz, xs, vs, m_var_pos);
            return substitute(p, x2v);
        }

        polynomial * substitute(polynomial const * p, unsigned xs_sz, var const * xs, numeral const * vs) {
            TRACE("polynomial", tout << "substitute num_vars: " << xs_sz << "\n";
                  for (unsigned i = 0; i < xs_sz; i++) { tout << "x" << xs[i] << " -> " << m_manager.to_string(vs[i]) << "\n"; });
            scoped_var_pos var2pos(m_var_pos, xs_sz, xs);
            scoped_numeral new_a(m_manager);
            scoped_numeral tmp(m_manager);
            m_som_buffer.reset();
            som_buffer & R       = m_som_buffer;
            tmp_monomial & new_m = m_tmp1; 
            unsigned sz    = p->size();
            for (unsigned i = 0; i < sz; i++) {
                monomial * m = p->m(i);
                unsigned msz = m->size();
                unsigned new_msz = 0;
                m_manager.set(new_a, p->a(i));
                new_m.reserve(msz);
                for (unsigned j = 0; j < msz; j++) {
                    var x = m->get_var(j);
                    unsigned k = m->degree(j);
                    unsigned pos = var2pos(x);
                    if (pos != UINT_MAX) {
                        m_manager.power(vs[pos], k, tmp);
                        m_manager.mul(tmp, new_a, new_a);
                    }
                    else {
                        SASSERT(var2pos(x) == UINT_MAX); // x is not in xs
                        new_m.set_power(new_msz, m->get_power(j));
                        new_msz++;
                    }
                }
                new_m.set_size(new_msz);
                TRACE("polynomial", tout << "processing " << m_manager.to_string(p->a(i)) << " "; m->display(tout); tout << "\n";
                      tout << "new_a: " << m_manager.to_string(new_a) << " "; mk_monomial(new_m)->display(tout); tout << "\n";);
                R.add(new_a, mk_monomial(new_m));
            }
            return R.mk();
        }

        
        /**
           Auxiliary method used to implement t_eval.
           If evaluates the sub-polynomial p composed of the monomials at positions [start, end)
           where all variables > x are ignored.

           var2pos is a mapping from variables to the positions.
           vs[var2pos(x)] contains the value of x.
        */
        template<typename ValManager>
        void t_eval_core(polynomial * p, ValManager & vm, var2value<ValManager> const & x2v,
                         unsigned start, unsigned end, var x, typename ValManager::numeral & r) {
            TRACE("eval_bug", tout << "p: "; p->display(tout, m()); tout << "\n";
                  tout << "start: " << start << ", end: " << end << ", x: " << x << "\n";);
            SASSERT(start < end);
            SASSERT(end <= p->size());
            SASSERT(is_valid(x));
            _scoped_numeral<ValManager> aux(vm);
            if (end == start + 1) {
                vm.set(r, p->a(start));
                monomial * m = p->m(start);
                SASSERT(m->degree_of(x) > 0);
                unsigned sz = m->size();
                for (unsigned i = 0; i < sz; i++) {
                    var y = m->get_var(i);
                    if (y > x)
                        break;
                    SASSERT(x2v.contains(y));
                    unsigned d    = m->degree(i);
                    vm.power(x2v(y), d, aux);
                    vm.mul(r, aux, r);
                }
            }
            else {
                SASSERT(x2v.contains(x));
                typename ValManager::numeral const & x_value = x2v(x);
                vm.reset(r);
                unsigned i = start;
                while (i < end) {
                    checkpoint();
                    unsigned d = p->m(i)->degree_of(x);
                    if (d == 0) {
                        var y = p->max_smaller_than(i, end, x);
                        if (y == null_var) {
                            SASSERT(end == i+1);
                            vm.add(r, p->a(i), r); 
                        }
                        else {
                            t_eval_core<ValManager>(p, vm, x2v, i, end, y, aux.get());
                            vm.add(r, aux, r);
                        }
                        break;
                    }
                    unsigned j = i+1;
                    unsigned next_d = 0;
                    for (; j < end; j++) {
                        unsigned d_j = p->m(j)->degree_of(x);
                        SASSERT(d_j <= d);
                        if (d_j < d) {
                            next_d = d_j;
                            break;
                        }
                    }
                    SASSERT(j == end || p->m(j)->degree_of(x) < d);
                    var y = p->max_smaller_than(i, j, x);
                    if (y == null_var) {
                        SASSERT(j == i+1);
                        vm.set(aux, p->a(i));
                    }
                    else {
                        t_eval_core<ValManager>(p, vm, x2v, i, j, y, aux.get());
                    }
                    vm.add(r, aux, r);
                    vm.power(x_value, d - next_d, aux);
                    vm.mul(r, aux, r);
                    i = j;
                }
            }
            TRACE("eval_bug", tout << "result for start: " << start << ", end: " << end << ", x: " << x << "\n";
                  tout << "r: "; vm.display(tout, r); tout << "\n";);
        }

        template<typename ValManager>
        void t_eval(polynomial * p, var2value<ValManager> const & x2v, typename ValManager::numeral & r) {
            ValManager & vm = x2v.m();
            if (is_zero(p)) {
                vm.reset(r);
                return;
            }
            if (is_const(p)) {
                SASSERT(size(p)==1);
                vm.set(r, p->a(0));
                return;
            }
            lex_sort(p); // lex_sort just reorders the monomials of p. That is, p still represents the same polynomial
            t_eval_core(p, vm, x2v, 0, p->size(), max_var(p), r);
        }
        
        class single_var2value : public var2value<numeral_manager> {
            numeral_manager & m_manager;
            var             m_x;
            numeral const & m_val;
        public:
            single_var2value(numeral_manager & m, var x, numeral const & val):m_manager(m), m_x(x), m_val(val) {}
            virtual numeral_manager & m() const { return m_manager; }
            virtual bool contains(var x) const { return m_x == x; }
            virtual numeral const & operator()(var x) const { SASSERT(m_x == x); return m_val; }
        };

        void univ_eval(polynomial const * p, var x, numeral const & val, numeral & r) {
            SASSERT(is_univariate(p));
            if (is_zero(p)) 
                m().set(r, 0);
            else if (is_const(p)) 
                m().set(r, p->a(0));
            else
                t_eval<numeral_manager>(const_cast<polynomial*>(p), single_var2value(m(),x, val), r);
        }
        
        void eval(polynomial const * p, var2mpbqi const & x2v, mpbqi & r) {
            t_eval<mpbqi_manager>(const_cast<polynomial*>(p), x2v, r);
        }

        void eval(polynomial const * p, var2mpq const & x2v, mpq & r) {
            t_eval<unsynch_mpq_manager>(const_cast<polynomial*>(p), x2v, r);
        }

        void eval(polynomial const * p, var2anum const & x2v, anum & r) {
            t_eval<anum_manager>(const_cast<polynomial*>(p), x2v, r);
        }

        // Return the variable with minimal degree in p
        // That is min_x s.t. forall x in p degree(p, min_x) <= degree(p, x)
        var get_min_degree_var(polynomial const * p) {
            SASSERT(!is_const(p));
            scoped_var_max_degree var2max_degree(m_var_max_degree, p);
            unsigned num_vars = var2max_degree.num_vars();
            var const * xs = var2max_degree.vars();
            var min_x = null_var;
            unsigned deg_min = UINT_MAX;
            for (unsigned i = 0; i < num_vars; i++) {
                var x_i = xs[i];
                unsigned deg_x_i = var2max_degree(x_i);
                if (deg_x_i < deg_min) {
                    min_x   = x_i;
                    deg_min = deg_x_i;
                }
            }
            return min_x;
        }

        void acc_constant(factors & r, numeral const & c) {
            TRACE("factor_bug", tout << "acc_constant, c: "; m_manager.display(tout, c); tout << "\n";);
            scoped_numeral new_c(m_manager);
            m_manager.mul(r.get_constant(), c, new_c);
            r.set_constant(new_c);
        }

        void flip_sign(factors & r) {
            scoped_numeral new_c(m_manager);
            m_manager.set(new_c, r.get_constant());
            m_manager.neg(new_c);
            r.set_constant(new_c);
        }

        void factor_1_sqf_pp(polynomial const * p, factors & r, var x, unsigned k) {
            SASSERT(degree(p, x) == 1);
            SASSERT(is_primitive(p, x));
            SASSERT(is_square_free(p, x));
            TRACE("factor", tout << "factor square free (degree == 1):\n"; p->display(tout, m_manager); tout << "\n";);
            // easy case
            r.push_back(const_cast<polynomial*>(p), k);
        }

        void factor_2_sqf_pp(polynomial const * p, factors & r, var x, unsigned k) {
            SASSERT(degree(p, x) == 2);
            SASSERT(is_primitive(p, x));
            SASSERT(is_square_free(p, x));
            TRACE("factor", tout << "factor square free (degree == 2):\n"; p->display(tout, m_manager); tout << "\n";);

            polynomial_ref a(pm());
            polynomial_ref b(pm());
            polynomial_ref c(pm());
            a = coeff(p, x, 2);
            b = coeff(p, x, 1);
            c = coeff(p, x, 0);
            TRACE("factor", tout << "a: " << a << "\nb: " << b << "\nc: " << c << "\n";);
            // make sure the leading monomoal of a is positive
            bool flipped_coeffs = false;
            SASSERT(!is_zero(a));
            unsigned a_glex_max_pos = a->graded_lex_max_pos();
            SASSERT(a_glex_max_pos != UINT_MAX);
            if (m_manager.is_neg(a->a(a_glex_max_pos))) {
                a = neg(a);
                b = neg(b);
                c = neg(c);
                flipped_coeffs = true;
            }
            // Create the discriminant: b^2 - 4*a*c
            polynomial_ref b2(pm());
            b2  = mul(b, b);
            polynomial_ref ac(pm());
            ac = mul(a, c);
            polynomial_ref disc(pm());
            numeral m_four;
            m_manager.set(m_four, -4);
            disc = addmul(b2, m_four, mk_unit(), ac);
            // discriminant must be different from 0, since p is square free
            SASSERT(!is_zero(disc)); 
            polynomial_ref disc_sqrt(pm());
            TRACE("factor", tout << "disc: " << disc << "\n";);
            if (!sqrt(disc, disc_sqrt)) {
                // p is irreducible
                r.push_back(const_cast<polynomial*>(p), k);
                return;
            }
            if (flipped_coeffs && k % 2 == 1) {
                // if k is ODD, and we flipped the coefficients,
                // we must also flip the sign of r.
                flip_sign(r);
            }
            DEBUG_CODE({
                polynomial_ref tmp(pm());
                tmp = mul(disc_sqrt, disc_sqrt);
                SASSERT(eq(disc, tmp));
            });
            TRACE("factor", tout << "disc_sqrt: " << disc_sqrt << "\n";);
            // p = cont*(2*a*x + b - disc_sqrt)*(2*a*x + b + disc_sqrt)
            numeral two;
            m_manager.set(two, 2);
            polynomial_ref f1(pm());
            polynomial_ref f2(pm());
            monomial_ref mx(pm());
            mx = mk_monomial(x);
            polynomial_ref two_ax(pm());
            two_ax = mul(two, mx, a);
            f1 = add(two_ax, b);
            f2 = f1;
            f1 = sub(f1, disc_sqrt);
            f2 = add(f2, disc_sqrt);
            TRACE("factor", tout << "before pp\nf1: " << f1 << "\nf2: " << f2 << "\n";
                  polynomial_ref cf1(pm()); m_wrapper.content(f1, x, cf1);
                  polynomial_ref cf2(pm()); m_wrapper.content(f2, x, cf2);
                  tout << "content(f1): " << cf1 << "\ncontent(f2): " << cf2 << "\n";);
            pp(f1, x, f1);
            pp(f2, x, f2);
            TRACE("factor", tout << "f1: " << f1 << "\nf2: " << f2 << "\n";);
            DEBUG_CODE({
                polynomial_ref f1f2(pm());
                f1f2 = mul(f1, f2);
                if (flipped_coeffs)
                    f1f2 = neg(f1f2);
                SASSERT(eq(f1f2, p));
            });
            r.push_back(f1, k);
            r.push_back(f2, k);
        }
        
        void factor_sqf_pp_univ(polynomial const * p, factors & r, unsigned k, factor_params const & params) {
            SASSERT(is_univariate(p));
            SASSERT(is_square_free(p, max_var(p)));
            SASSERT(is_primitive(p, max_var(p)));
            SASSERT(!is_zero(p));
            TRACE("factor", tout << "factor square free univariate:\n"; p->display(tout, m_manager); tout << "\n";);
            
            // Convert polynomial into a upolynomial, and execute univariate factorization.
            var x = max_var(p);
            up_manager::scoped_numeral_vector p1(upm().m());
            polynomial_ref p_ref(pm());
            p_ref = const_cast<polynomial*>(p);
            upm().to_numeral_vector(p_ref, p1);
            up_manager::factors fs(upm());
            upolynomial::factor_square_free(upm(), p1, fs, params);
            SASSERT(m().is_one(fs.get_constant()) || m().is_minus_one(fs.get_constant()));

            if (fs.distinct_factors() == 1 && fs.get_degree(0) == 1) {
                // p is irreducible
                r.push_back(const_cast<polynomial*>(p), k);
            }
            else {
                // Convert factors back into polynomial objects
                TRACE("factor_bug", tout << "factoring fs constant: " << m().to_string(fs.get_constant()) << "\np:\n";
                      p->display(tout, m()); tout << "\n";);
                polynomial_ref f(pm());
                unsigned num_factors = fs.distinct_factors();
                for (unsigned i = 0; i < num_factors; i++) {
                    numeral_vector const & f1 = fs[i];
                    unsigned k1 = fs.get_degree(i);
                    f = to_polynomial(f1.size(), f1.c_ptr(), x);
                    TRACE("factor_bug", 
                          tout << "uni-factor:\n"; upm().display(tout, f1); tout << "\n";
                          tout << "factor:\n" << f << "\n";);
                    r.push_back(f, k*k1);
                }
                TRACE("factor_bug", tout << "end-factors...\n";);
                SASSERT(m().is_one(fs.get_constant()) || m().is_minus_one(fs.get_constant()));
                if (m().is_minus_one(fs.get_constant()) && k % 2 == 1)
                    flip_sign(r);
            }
        }

        void factor_n_sqf_pp(polynomial const * p, factors & r, var x, unsigned k) {
            SASSERT(degree(p, x) > 2);
            SASSERT(is_primitive(p, x));
            SASSERT(is_square_free(p, x));
            TRACE("factor", tout << "factor square free (degree > 2):\n"; p->display(tout, m_manager); tout << "\n";);
            
            // TODO: invoke Dejan's procedure
            r.push_back(const_cast<polynomial*>(p), k);
        }

        void factor_sqf_pp(polynomial const * p, factors & r, var x, unsigned k, factor_params const & params) {
            SASSERT(degree(p, x) > 0);
            SASSERT(is_primitive(p, x));
            SASSERT(is_square_free(p, x));
            SASSERT(!is_zero(p));

            unsigned deg_x = degree(p, x);
            if (deg_x == 1)
                factor_1_sqf_pp(p, r, x, k);
            else if (is_univariate(p))
                factor_sqf_pp_univ(p, r, k, params);
            else if (deg_x == 2)
                factor_2_sqf_pp(p, r, x, k);
            else
                factor_n_sqf_pp(p, r, x, k);
        }

        void factor_core(polynomial const * p, factors & r, factor_params const & params) {
            TRACE("factor", tout << "factor_core\np: "; p->display(tout, m_manager); tout << "\n";);
            TRACE("factor_bug", tout << "factors r.get_constant(): " << m_manager.to_string(r.get_constant()) << "\n";);
            SASSERT(!is_zero(p));
            if (is_const(p)) {
                SASSERT(!is_zero(p));
                SASSERT(p->size() == 1);
                acc_constant(r, p->a(0));
                return;
            }
            var x = get_min_degree_var(p);
            SASSERT(degree(p, x) > 0);
            scoped_numeral i(m_manager);
            polynomial_ref c(pm()), pp(pm());
            iccp(p, x, i, c, pp);
            TRACE("factor", tout << "i: " << i << "\n";);
            acc_constant(r, i);
            factor_core(c, r, params);
            
            polynomial_ref C(pm());
            C = pp;
            // Let C be a primitive polynomial of the form: P_1^1 * P_2^2 * ... * P_k^k, where each P_i is square free
            polynomial_ref C_prime(pm()); 
            C_prime = derivative(C, x);
            polynomial_ref B(pm()), A(pm()), D(pm());
            gcd(C, C_prime, B); 
            if (is_const(B)) {
                // C must be of the form P_1 (square free)
                SASSERT(degree(C, x) > 0);
                factor_sqf_pp(C, r, x, 1, params);
            }
            else {
                // B is of the form P_2 * P_3^2 * ... * P_k^{k-1}
                A = exact_div(C, B); 
                // A is of the form P_1 * P_2 * ... * P_k
                unsigned j = 1;
                while (!is_const(A)) {
                    SASSERT(is_primitive(A, x));
                    SASSERT(is_square_free(A, x));
                    SASSERT(degree(A, x) > 0);
                    checkpoint();
                    TRACE("factor", tout << "factor_core main loop j: " << j << "\nA: " << A << "\nB: " << B << "\n";);
                    // A is of the form       P_j * P_{j+1} * P_{j+2}   * ... * P_k
                    // B is of the form             P_{j+1} * P_{j+2}^2 * ... * P_k^{k - j - 2}
                    gcd(A, B, D);
                    // D is of the form             P_{j+1} * P_{j+2}   * ... * P_k
                    C = exact_div(A, D);
                    // C is of the form P_j
                    if (!is_const(C)) {
                        SASSERT(degree(C, x) > 0);
                        factor_sqf_pp(C, r, x, j, params);
                    }
                    else {
                        TRACE("factor", tout << "const C: " << C << "\n";);
                        SASSERT(C->size() == 1);
                        SASSERT(m_manager.is_one(C->a(0)) || m_manager.is_minus_one(C->a(0)));
                        if (m_manager.is_minus_one(C->a(0)) && j % 2 == 1)
                            flip_sign(r);
                    }
                    B = exact_div(B, D);
                    // B is of the form                       P_{j+2}   * ... * P_k^{k - j - 3}
                    A = D;
                    // D is of the form             P_{j+1} * P_{j+2}   * ... * P_k
                    j++;
                }
                SASSERT(eq(mk_one(), A));
            }
        }

        void factor(polynomial const * p, factors & r, factor_params const & params) {
            if (is_zero(p)) {
                r.set_constant(mpz(0));
                return;
            }
            factor_core(p, r, params);
            TRACE("factor_bug", tout << "[factor] end, r.get_constant(): " << m_manager.to_string(r.get_constant()) << "\n";);
        }

        polynomial * to_polynomial(unsigned sz, numeral const * p, var x) {
            if (sz == 0)
                return mk_zero();
            _scoped_numeral_buffer<numeral_manager, 128> coeffs(m_manager);
            for (unsigned i = 0; i < sz; i++) {
                coeffs.push_back(numeral());
                m_manager.set(coeffs.back(), p[i]);
            }
            return mk_univariate(x, sz-1, coeffs.c_ptr());
        }

        polynomial * mk_glex_monic(polynomial const * p) {
            SASSERT(m_manager.field());
            if (is_zero(p))
                return const_cast<polynomial*>(p);
            unsigned pos = p->graded_lex_max_pos();
            if (m_manager.is_one(p->a(pos)))
                return const_cast<polynomial*>(p);
            scoped_numeral inv_c(m());
            scoped_numeral new_a(m());
            m().set(inv_c, p->a(pos));
            m().inv(inv_c);
            m_cheap_som_buffer.reset();
            cheap_som_buffer & R = m_cheap_som_buffer;
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                m().set(new_a, p->a(i));
                m().mul(new_a, inv_c, new_a);
                R.add(new_a, p->m(i));
            }
            return R.mk();
        }

        som_buffer_vector m_translate_buffers;
        polynomial * translate(polynomial const * p, var x, numeral const & v) {
            unsigned deg_x = degree(p, x);
            if (deg_x == 0 || m().is_zero(v))
                return const_cast<polynomial*>(p);
            som_buffer_vector & as = m_translate_buffers;
            m_translate_buffers.reset(deg_x+1);
            coeffs(p, x, as);
            for (unsigned i = 1; i <= deg_x; i++) {
                checkpoint();
                for (unsigned k = deg_x-i; k <= deg_x-1; k++) {
                    as[k]->addmul(v, as[k+1]);
                }
            }
            monomial_ref xk(pm());
            som_buffer & R = m_som_buffer;
            R.reset();
            for (unsigned k = 0; k <= deg_x; k++) {
                xk = mk_monomial(x, k);
                R.addmul(xk, as[k]);
            }
            m_translate_buffers.reset(deg_x+1);
            return R.mk();
        }

        void translate(polynomial const * p, unsigned xs_sz, var const * xs, numeral const * vs, polynomial_ref & r) {
            r = const_cast<polynomial*>(p);
            if (xs_sz == 0 || is_const(p))
                return;
            for (unsigned i = 0; i < xs_sz; i++)
                r = translate(r, xs[i], vs[i]);
        }

        polynomial * mod_d(polynomial const * p, var2degree const & x2d) {
            if (is_const(p))
                return const_cast<polynomial*>(p);

            cheap_som_buffer & R = m_cheap_som_buffer;
            R.reset();
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                monomial * m = p->m(i);
                unsigned msz = m->size();
                unsigned j;
                for (j = 0; j < msz; j++) {
                    var x = m->get_var(j);
                    unsigned dx = x2d.degree(x);
                    if (dx == 0)
                        continue;
                    if (m->degree(j) >= dx)
                        break;
                }
                if (j == msz) {
                    R.add(p->a(i), p->m(i));
                }
            }
            return R.mk();
        }

        void exact_pseudo_division_mod_d(polynomial const * p, polynomial const * q, var x, var2degree const & x2d, polynomial_ref & Q, polynomial_ref & R) {
            unsigned d;
            pseudo_division_core<true, true, true>(p, q, x, d, Q, R, &x2d);
        }
    };

    manager::manager(numeral_manager & m, monomial_manager * mm) {
        m_imp = alloc(imp, *this, m, mm);
    }

    manager::manager(numeral_manager & m, small_object_allocator * a) {
        m_imp = alloc(imp, *this, m, a);
    }

    manager::~manager() {
        dealloc(m_imp);
    }

    numeral_manager & manager::m() const {
        return m_imp->m_manager.m();
    }

    monomial_manager & manager::mm() const {
        return m_imp->mm();
    }

    bool manager::modular() const {
        return m_imp->m().modular();
    }

    numeral const & manager::p() const {
        return m_imp->m().p();
    }

    void manager::set_z() {
        return m_imp->m().set_z();
    }

    void manager::set_zp(numeral const & p) {
        return m_imp->m().set_zp(p);
    }

    void manager::set_zp(uint64 p) {
        return m_imp->m().set_zp(p);
    }

    small_object_allocator & manager::allocator() const {
        return m_imp->mm().allocator();
    }
    
    void manager::set_cancel(bool f) {
        m_imp->set_cancel(f);
    }

    void manager::add_del_eh(del_eh * eh) {
        m_imp->add_del_eh(eh);
    }

    void manager::remove_del_eh(del_eh * eh) {
        m_imp->remove_del_eh(eh);
    }
    
    var manager::mk_var() {
        return m_imp->mk_var();
    }

    unsigned manager::num_vars() const {
        return m_imp->num_vars();
    }

    void manager::inc_ref(monomial * m) {
        if (m)
            m->inc_ref();
    }

    void manager::dec_ref(monomial * m) {
        if (m)
            m_imp->dec_ref(m);
    }

    void manager::inc_ref(polynomial * p) {
        if (p)
            p->inc_ref();
    }

    void manager::dec_ref(polynomial * p) {
        if (p)
            m_imp->dec_ref(p);
    }

    void manager::lex_sort(polynomial * p) {
        m_imp->lex_sort(p);
    }

    unsigned manager::hash(monomial const * m) {
        return m->hash();
    }

    unsigned manager::hash(polynomial const * p) {
        return m_imp->hash(p);
    }
    
    polynomial * manager::coeff(polynomial const * p, var x, unsigned k) {
        return m_imp->coeff(p, x, k);
    }

    polynomial * manager::coeff(polynomial const * p, var x, unsigned k, polynomial_ref & reduct) {
        return m_imp->coeff(p, x, k, reduct);
    }

    bool manager::nonzero_const_coeff(polynomial const * p, var x, unsigned k) {
        return m_imp->nonzero_const_coeff(p, x, k);
    }

    bool manager::const_coeff(polynomial const * p, var x, unsigned k, numeral & c) {
        return m_imp->const_coeff(p, x, k, c);
    }

    monomial * manager::mk_unit() {
        return m_imp->mk_unit();
    }

    monomial * manager::mk_monomial(var x) {
        return m_imp->mk_monomial(x);
    }

    monomial * manager::mk_monomial(var x, unsigned k) {
        return m_imp->mk_monomial(x, k);
    }

    monomial * manager::mk_monomial(unsigned sz, var * xs) {
        return m_imp->mk_monomial(sz, xs);
    }

    monomial * manager::convert(monomial const * src) {
        return m_imp->convert(src);
    }

    monomial * manager::mul(monomial const * m1, monomial const * m2) {
        return m_imp->mul(m1, m2);
    }

    bool manager::div(monomial const * m1, monomial const * m2) {
        return m_imp->div(m1, m2);
    }

    bool manager::div(monomial const * m1, monomial const * m2, monomial * & r) {
        return m_imp->div(m1, m2, r);
    }

    void manager::newton_interpolation(var x, unsigned d, numeral const * inputs, polynomial * const * outputs, polynomial_ref & r) {
        return m_imp->newton_interpolation(x, d, inputs, outputs, r);
    }

    monomial * manager::gcd(monomial const * m1, monomial const * m2, monomial * & q1, monomial * & q2) {
        return m_imp->gcd(m1, m2, q1, q2);
    }

    bool manager::unify(monomial const * m1, monomial const * m2, monomial * & q1, monomial * & q2) {
        return m_imp->unify(m1, m2, q1, q2);
    }

    monomial * manager::pw(monomial const * m, unsigned k) {
        return m_imp->pw(m, k);
    }

    polynomial * manager::mk_zero() {
        return m_imp->mk_zero();
    }
    
    polynomial * manager::mk_const(numeral & a) {
        return m_imp->mk_const(a);
    }

    polynomial * manager::mk_const(rational const & a) {
        return m_imp->mk_const(a);
    }

    polynomial * manager::mk_polynomial(var x, unsigned k) {
        return m_imp->mk_polynomial(x, k);
    }

    polynomial * manager::mk_polynomial(unsigned sz, numeral * as, monomial * const * ms) {
        return m_imp->mk_polynomial(sz, as, ms);
    }

    polynomial * manager::mk_polynomial(unsigned sz, rational const * as, monomial * const * ms) {
        return m_imp->mk_polynomial(sz, as, ms);
    }

    polynomial * manager::mk_linear(unsigned sz, rational const * as, var const * xs, rational const & c) {
        return m_imp->mk_linear(sz, as, xs, c);
    }

    polynomial * manager::mk_linear(unsigned sz, numeral * as, var const * xs, numeral & c) {
        return m_imp->mk_linear(sz, as, xs, c);
    }

    polynomial * manager::mk_univariate(var x, unsigned n, numeral * as) {
        return m_imp->mk_univariate(x, n, as);
    }

    polynomial * manager::neg(polynomial const * p) {
        return m_imp->neg(p);
    }

    polynomial * manager::add(polynomial const * p1, polynomial const * p2) {
        return m_imp->add(p1, p2);
    }

    polynomial * manager::sub(polynomial const * p1, polynomial const * p2) {
        return m_imp->sub(p1, p2);
    }

    polynomial * manager::addmul(numeral const & a1, monomial const * m1, polynomial const * p1, 
                                 numeral const & a2, monomial const * m2, polynomial const * p2) {
        return m_imp->addmul(a1, m1, p1, a2, m2, p2);
    }

    polynomial * manager::addmul(polynomial const * p1, numeral const & a2, monomial const * m2, polynomial const * p2) {
        return m_imp->addmul(p1, a2, m2, p2);
    }

    polynomial * manager::addmul(polynomial const * p1, numeral const & a2, polynomial const * p2) {
        return m_imp->addmul(p1, a2, p2);
    }

    polynomial * manager::mul(numeral const & a, polynomial const * p) {
        return m_imp->mul(a, p);
    }
    
    polynomial * manager::mul(rational const & a, polynomial const * p) {
        return m_imp->mul(a, p);
    }
        
    polynomial * manager::mul(polynomial const * p1, polynomial const * p2) {
        return m_imp->mul(p1, p2);
    }

    polynomial * manager::mul(numeral const & a, monomial const * m, polynomial const * p) {
        return m_imp->mul(a, m, p);
    }

    polynomial * manager::mul(monomial const * m, polynomial const * p) {
        return m_imp->mul(m, p);
    }
    
    void manager::pw(polynomial const * p, unsigned k, polynomial_ref & r) {
        m_imp->pw(p, k, r);
    }

    void manager::int_content(polynomial const * p, numeral & c) {
        m_imp->ic(p, c);
    }

    void manager::abs_norm(polynomial const * p, numeral & norm) {
        m_imp->abs_norm(p, norm);
    }

    polynomial::numeral const & manager::numeral_lc(polynomial const * p, var x) {
        return m_imp->numeral_lc(p, x);
    }

    polynomial::numeral const & manager::numeral_tc(polynomial const * p) {
        return m_imp->numeral_tc(p);
    }

    void manager::content(polynomial const * p, var x, numeral & i, polynomial_ref & c) {
        polynomial_ref pp(*this);
        m_imp->iccp(p, x, i, c, pp);
    }

    void manager::content(polynomial const * p, var x, polynomial_ref & c) {
        scoped_numeral i(m_imp->m_manager.m());
        content(p, x, i, c);
        if (!m_imp->m_manager.is_one(i)) {
            c = mul(i, c);
        }
    }

    void manager::primitive(polynomial const * p, var x, polynomial_ref & pp) {
        m_imp->pp(p, x, pp);
    }

    void manager::icpp(polynomial const * p, var x, numeral & i, polynomial_ref & c, polynomial_ref & pp) {
        m_imp->iccp(p, x, i, c, pp);
    }

    polynomial * manager::flip_sign_if_lm_neg(polynomial const * p) {
        return m_imp->flip_sign_if_lm_neg_core(p);
    }
    
    void manager::gcd(polynomial const * p, polynomial const * q, polynomial_ref & g) {
        m_imp->gcd(p, q, g);
    }

    polynomial * manager::derivative(polynomial const * p, var x) {
        return m_imp->derivative(p, x);
    }
    
    void manager::square_free(polynomial const * p, var x, polynomial_ref & r) {
        m_imp->square_free(p, x, r);
    }

    bool manager::is_square_free(polynomial const * p, var x) {
        return m_imp->is_square_free(p, x);
    }

    void manager::square_free(polynomial const * p, polynomial_ref & r) {
        m_imp->square_free(p, r);
    }

    bool manager::is_square_free(polynomial const * p) {
        return m_imp->is_square_free(p);
    }

    bool manager::eq(polynomial const * p1, polynomial const * p2) {
        return m_imp->eq(p1, p2);
    }

    polynomial * manager::compose_y(polynomial const * p, var y) {
        return m_imp->compose_y(p, y);
    }

    polynomial * manager::compose_minus_x(polynomial const * p) {
        return m_imp->compose_minus_x(p);
    }

    polynomial * manager::compose_1_div_x(polynomial const * p) {
        return m_imp->compose_1_div_x(p);
    }

    polynomial * manager::compose_x_div_y(polynomial const * p, var y) {
        return m_imp->compose_x_div_y(p, y);
    }

    void manager::compose(polynomial const * p, polynomial const * q, polynomial_ref & r) {
        m_imp->compose(p, q, r);
    }

    void manager::compose_x_minus_y(polynomial const * p, var y, polynomial_ref & r) {
        m_imp->compose_x_minus_y(p, y, r);
    }

    void manager::compose_x_plus_y(polynomial const * p, var y, polynomial_ref & r) {
        m_imp->compose_x_plus_y(p, y, r);
    }

    void manager::compose_x_minus_c(polynomial const * p, numeral const & c, polynomial_ref & r) {
        m_imp->compose_x_minus_c(p, c, r);
    }

    bool manager::sqrt(polynomial const * p, polynomial_ref & r) {
        return m_imp->sqrt(p, r);
    }

    polynomial * manager::normalize(polynomial const * p) {
        return m_imp->normalize(p);
    }

    void manager::exact_pseudo_remainder(polynomial const * p, polynomial const * q, var x, polynomial_ref & R) {
        m_imp->exact_pseudo_remainder(p, q, x, R);
    }

    void manager::pseudo_remainder(polynomial const * p, polynomial const * q, var x, unsigned & d, polynomial_ref & R) {
        m_imp->pseudo_remainder(p, q, x, d, R);
    }

    void manager::exact_pseudo_division(polynomial const * p, polynomial const * q, var x, polynomial_ref & Q, polynomial_ref & R) {
        m_imp->exact_pseudo_division(p, q, x, Q, R);
    }

    void manager::pseudo_division(polynomial const * p, polynomial const * q, var x, unsigned & d, polynomial_ref & Q, polynomial_ref & R) {
        m_imp->pseudo_division(p, q, x, d, Q, R);
    }

    polynomial * manager::exact_div(polynomial const * p, polynomial const * q) {
        return m_imp->exact_div(p, q);
    }

    polynomial * manager::exact_div(polynomial const * p, numeral const & c) {
        return m_imp->exact_div(p, c);
    }
    
    bool manager::divides(polynomial const * q, polynomial const * p) {
        return m_imp->divides(q, p);
    }

    void manager::quasi_resultant(polynomial const * p, polynomial const * q, var x, polynomial_ref & r) {
        m_imp->quasi_resultant(p, q, x, r);
    }

    void manager::resultant(polynomial const * p, polynomial const * q, var x, polynomial_ref & r) {
        m_imp->resultant(p, q, x, r);
    }

    void manager::discriminant(polynomial const * p, var x, polynomial_ref & r) {
        m_imp->discriminant(p, x, r);
    }

    void manager::psc_chain(polynomial const * p, polynomial const * q, var x, polynomial_ref_vector & S) {
        m_imp->psc_chain(p, q, x, S);
    }

    bool manager::is_pos(polynomial const * p) {
        return m_imp->is_pos(p);
    }

    bool manager::is_neg(polynomial const * p) {
        return m_imp->is_neg(p);
    }

    bool manager::is_nonpos(polynomial const * p) {
        return m_imp->is_nonpos(p);
    }

    bool manager::is_nonneg(polynomial const * p) {
        return m_imp->is_nonneg(p);
    }

    void manager::rename(unsigned sz, var const * xs) {
        return m_imp->rename(sz, xs);
    }

    void manager::vars(polynomial const * p, var_vector & xs) {
        m_imp->vars(p, xs);
    }

    polynomial * manager::substitute(polynomial const * p, var2mpq const & x2v) {
        return m_imp->substitute(p, x2v);
    }

    polynomial * manager::substitute(polynomial const * p, unsigned xs_sz, var const * xs, mpq const * vs) {
        return m_imp->substitute(p, xs_sz, xs, vs);
    }

    polynomial * manager::substitute(polynomial const * p, unsigned xs_sz, var const * xs, numeral const * vs) {
        return m_imp->substitute(p, xs_sz, xs, vs);
    }

    void manager::factor(polynomial const * p, factors & r, factor_params const & params) {
        m_imp->factor(p, r, params);
    }

    polynomial * manager::to_polynomial(unsigned sz, numeral const * p, var x) {
        return m_imp->to_polynomial(sz, p, x);
    }

    polynomial * manager::mk_glex_monic(polynomial const * p) {
        return m_imp->mk_glex_monic(p);
    }

    polynomial * manager::translate(polynomial const * p, var x, numeral const & v) {
        return m_imp->translate(p, x, v);
    }

    void manager::translate(polynomial const * p, unsigned xs_sz, var const * xs, numeral const * vs, polynomial_ref & r) {
        return m_imp->translate(p, xs_sz, xs, vs, r);
    }

    polynomial * manager::mod_d(polynomial const * p, var2degree const & x2d) {
        return m_imp->mod_d(p, x2d);
    }

    void manager::exact_pseudo_division_mod_d(polynomial const * p, polynomial const * q, var x, var2degree const & x2d, 
                                                                    polynomial_ref & Q, polynomial_ref & R) {
        m_imp->exact_pseudo_division_mod_d(p, q, x, x2d, Q, R);
    }

    void manager::eval(polynomial const * p, var2mpbqi const & x2v, mpbqi & r) {
        return m_imp->eval(p, x2v, r);
    }

    void manager::eval(polynomial const * p, var2mpq const & x2v, mpq & r) {
        return m_imp->eval(p, x2v, r);
    }
    
    void manager::eval(polynomial const * p, var2anum const & x2v, algebraic_numbers::anum & r) {
        return m_imp->eval(p, x2v, r);
    }

    void manager::display(std::ostream & out, monomial const * m, display_var_proc const & proc, bool user_star) const {
        m->display(out, proc, user_star);
    }

    void manager::display(std::ostream & out, polynomial const * p, display_var_proc const & proc, bool use_star) const {
        SASSERT(m_imp->consistent_coeffs(p));
        p->display(out, m_imp->m_manager, proc, use_star);
    }

    void manager::display_smt2(std::ostream & out, polynomial const * p, display_var_proc const & proc) const {
        p->display_smt2(out, m_imp->m_manager, proc);
    }
};

polynomial::polynomial * convert(polynomial::manager & sm, polynomial::polynomial * p, polynomial::manager & tm, 
                                 polynomial::var x, unsigned max_d) {
    ptr_buffer<polynomial::monomial, 128> ms;
    polynomial::numeral_manager & nm = tm.m();
    _scoped_numeral_buffer<polynomial::numeral_manager, 128> as(nm);
    unsigned sz = sm.size(p);
    if (&sm == &tm) {
        // same source and target manager.
        // So, we just return p
        return p;
    }
    else if (&(sm.mm()) == &(tm.mm())) {
        // polynomial managers share the same monomial manager.
        // So, we don't need to convert monomials.
        for (unsigned i = 0; i < sz; i++) {
            polynomial::monomial * m = sm.get_monomial(p, i);
            if (x == polynomial::null_var || sm.degree_of(m, x) <= max_d) {
                ms.push_back(m);
                as.push_back(polynomial::numeral());
                nm.set(as.back(), sm.coeff(p, i));
            }
        }
    }
    else {
        for (unsigned i = 0; i < sz; i++) {
            polynomial::monomial * m = sm.get_monomial(p, i);
            if (x == polynomial::null_var || sm.degree_of(m, x) <= max_d) {
                ms.push_back(tm.convert(m));
                as.push_back(polynomial::numeral());
                nm.set(as.back(), sm.coeff(p, i));
            }
        }
    }
    return tm.mk_polynomial(as.size(), as.c_ptr(), ms.c_ptr());
}

std::ostream & operator<<(std::ostream & out, polynomial_ref_vector const & seq) {
    unsigned sz = seq.size();
    for (unsigned i = 0; i < sz; i++) {
        seq.m().display(out, seq.get(i));
        out << "\n";
    }
    return out;
}
