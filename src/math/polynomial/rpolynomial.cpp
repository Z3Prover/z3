/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    rpolynomial.cpp

Abstract:

    Goodies for creating and handling polynomials in dense recursive representation.

Author:

    Leonardo (leonardo) 2012-06-11

Notes:

--*/
#include "math/polynomial/rpolynomial.h"
#include "util/tptr.h"
#include "util/buffer.h"

namespace rpolynomial {

    typedef void poly_or_num;
    
    inline bool is_poly(poly_or_num * p) { return GET_TAG(p) == 0; }
    inline bool is_num(poly_or_num * p) { return GET_TAG(p) == 1; }
    polynomial * to_poly(poly_or_num * p) { SASSERT(is_poly(p)); return UNTAG(polynomial*, p); }
    manager::numeral * to_num_ptr(poly_or_num * p) { SASSERT(is_num(p)); return (UNTAG(manager::numeral *, p)); }
    manager::numeral & to_num(poly_or_num * p) { return *to_num_ptr(p); }
    poly_or_num * to_poly_or_num(polynomial * p) { return TAG(poly_or_num*, p, 0); }
    poly_or_num * to_poly_or_num(manager::numeral * n) { return TAG(poly_or_num*, n, 1); }

    class polynomial {
        friend class  manager;
        friend struct manager::imp;

        unsigned      m_ref_count;
        var           m_var;
        unsigned      m_size;
        poly_or_num * m_args[0]; 

    public:
        unsigned ref_count() const { return m_ref_count; }
        void inc_ref() { m_ref_count++; }
        void dec_ref() { SASSERT(m_ref_count > 0); m_ref_count--; }

        static unsigned get_obj_size(unsigned n) { return sizeof(polynomial) + n*sizeof(void*); }

        var max_var() const { return m_var; }
        unsigned size() const { return m_size; }
        poly_or_num * arg(unsigned i) const { SASSERT(i < size()); return m_args[i]; }
    };
    
    struct manager::imp {
        manager &                        m_wrapper;
        numeral_manager &                m_manager;
        small_object_allocator *         m_allocator;
        bool                             m_own_allocator;
        
        imp(manager & w, numeral_manager & m, small_object_allocator * a):
            m_wrapper(w),
            m_manager(m),
            m_allocator(a),
            m_own_allocator(a == nullptr) {
            if (a == nullptr)
                m_allocator = alloc(small_object_allocator, "rpolynomial");
        }

        ~imp() {
            if (m_own_allocator)
                dealloc(m_allocator);
        }

        // Remark: recursive calls should be fine since I do not expect to have polynomials with more than 100 variables.

        manager & pm() const { return m_wrapper; } 

        numeral * mk_numeral() {
            void * mem = m_allocator->allocate(sizeof(numeral));
            return new (mem) numeral();
        }

        void del_numeral(numeral * n) {
            m_manager.del(*n);
            m_allocator->deallocate(sizeof(numeral), n);
        }

        static void inc_ref(polynomial * p) {
            if (p)
                p->inc_ref();
        }

        static void inc_ref(poly_or_num * p) {
            if (p && is_poly(p))
                inc_ref(to_poly(p));
        }

        void del_poly(polynomial * p) {
            SASSERT(p != 0);
            ptr_buffer<polynomial> todo;
            todo.push_back(p);
            while (!todo.empty()) {
                p = todo.back();
                todo.pop_back();
                unsigned sz = p->size();
                for (unsigned i = 0; i < sz; i++) {
                    poly_or_num * pn = p->arg(i);
                    if (pn == nullptr)
                        continue;
                    if (is_num(pn)) {
                        del_numeral(to_num_ptr(pn));
                    }
                    else {
                        SASSERT(is_poly(p));
                        polynomial * p_arg = to_poly(p);
                        p_arg->dec_ref();
                        if (p_arg->ref_count() == 0) {
                            todo.push_back(p_arg);
                        }
                    }
                }
                unsigned obj_sz = polynomial::get_obj_size(sz);
                m_allocator->deallocate(obj_sz, p);
            }
        }
        
        void dec_ref(polynomial * p) {
            if (p) {
                p->dec_ref();
                if (p->ref_count() == 0)
                    del_poly(p);
            }
        }

        void dec_ref(poly_or_num * p) {
            if (p && is_poly(p))
                dec_ref(to_poly(p));
        }

        static bool is_const(polynomial const * p) {
            SASSERT(p == 0 || (p->max_var() == null_var) == (p->size() == 1 && p->arg(0) != 0 && is_num(p->arg(0))));
            return p == nullptr || p->max_var() == null_var;
        }

        bool is_zero(polynomial const * p) {
            return p == nullptr;
        }

        static bool is_univariate(polynomial const * p) {
            if (is_const(p))
                return false;
            unsigned sz = p->size();
            for (unsigned i = 0; i < sz; i++) {
                poly_or_num * pn = p->arg(i);
                if (pn == nullptr)
                    continue;
                if (is_poly(pn))
                    return false;
            }
            return true;
        }

        bool is_monomial(polynomial const * p) {
            if (is_const(p))
                return true;
            unsigned sz = p->size();
            SASSERT(sz > 0);
            SASSERT(p->arg(sz - 1) != 0);
            for (unsigned i = 0; i < sz - 1; i++) {
                if (p->arg(i) != nullptr)
                    return false;
            }
            SASSERT(is_poly(p->arg(sz - 1)));
            return is_monomial(to_poly(p->arg(sz-1)));
        }

        unsigned degree(polynomial const * p) {
            SASSERT(p != 0);
            SASSERT(p->size() > 0);
            return p == nullptr ? 0 : p->size() - 1;
        }
     
        bool eq(polynomial const * p1, polynomial const * p2) {
            if (p1 == p2)
                return true;
            if (p1 == nullptr || p2 == nullptr)
                return false;
            if (p1->size() != p2->size())
                return false;
            if (p1->max_var() != p2->max_var())
                return false;
            unsigned sz = p1->size();
            for (unsigned i = 0; i < sz; i++) {
                poly_or_num * pn1 = p1->arg(i);
                poly_or_num * pn2 = p2->arg(i);
                if (pn1 == nullptr && pn2 == nullptr)
                    continue;
                if (pn1 == nullptr || pn2 == nullptr)
                    return false;
                if (is_num(pn1) && is_num(pn2)) {
                    if (!m_manager.eq(to_num(pn1), to_num(pn2)))
                        return false;
                }
                else if (is_poly(pn1) && is_poly(pn2)) {
                    if (!eq(to_poly(pn1), to_poly(pn2)))
                        return false;
                }
                else {
                    return false;
                }
            }
            return true;
        }

        void inc_ref_args(unsigned sz, poly_or_num * const * args) {
            for (unsigned i = 0; i < sz; i++) {
                poly_or_num * pn = args[i];
                if (pn == nullptr || is_num(pn))
                    continue;
                inc_ref(to_poly(pn));
            }
        }

        void dec_ref_args(unsigned sz, poly_or_num * const * args) {
            for (unsigned i = 0; i < sz; i++) {
                poly_or_num * pn = args[i];
                if (pn == nullptr || is_num(pn))
                    continue;
                dec_ref(to_poly(pn));
            }
        }

        unsigned trim(unsigned sz, poly_or_num * const * args) {
            while (sz > 0) {
                if (args[sz - 1] != nullptr)
                    return sz;
                sz--;
            }
            UNREACHABLE();
            return UINT_MAX;
        }

        polynomial * allocate_poly(unsigned sz, poly_or_num * const * args, var max_var) {
            SASSERT(sz > 0);
            SASSERT((max_var == null_var) == (sz == 1 && is_num(args[0])));
            unsigned obj_sz = polynomial::get_obj_size(sz);
            void * mem      = m_allocator->allocate(obj_sz);
            polynomial * new_pol = new (mem) polynomial();
            new_pol->m_ref_count = 0;
            new_pol->m_var       = max_var;
            new_pol->m_size      = sz;
            for (unsigned i = 0; i < sz; i++) {
                poly_or_num * pn = args[i];
                if (is_poly(pn)) {
                    inc_ref(to_poly(pn));
                    new_pol->m_args[i] = pn;
                    SASSERT(max_var == null_var || to_poly(pn)->max_var() < max_var);
                }
                else {
                    SASSERT(!m_manager.is_zero(to_num(pn)));
                    new_pol->m_args[i] = pn;
                }
            }
            return new_pol;
        }

        poly_or_num * mk_poly_core(unsigned sz, poly_or_num * const * args, var max_var) {
            sz = trim(sz, args);
            SASSERT(sz > 0);
            if (sz == 1) {
                poly_or_num * pn0 = args[0];
                SASSERT(!is_num(pn0) || !m_manager.is_zero(to_num(pn0)));
                return pn0;
            }
            SASSERT((max_var == null_var) == (sz == 1 && is_num(args[0])));
            SASSERT(sz > 1);
            return to_poly_or_num(allocate_poly(sz, args, max_var));
        }

        polynomial * mk_poly(unsigned sz, poly_or_num * const * args, var max_var) {
            poly_or_num * _p = mk_poly_core(sz, args, max_var);
            if (_p == nullptr)
                return nullptr;
            else if (is_num(_p))
                return allocate_poly(1, &_p, null_var);
            else
                return to_poly(_p);
        }

        polynomial * mk_const(numeral const & n) {
            if (m_manager.is_zero(n))
                return nullptr;
            numeral * a = mk_numeral();
            m_manager.set(*a, n);
            poly_or_num * _a = to_poly_or_num(a);
            return allocate_poly(1, &_a, null_var);
        }

        polynomial * mk_const(rational const & a) {
            SASSERT(a.is_int());
            scoped_numeral tmp(m_manager);
            m_manager.set(tmp, a.to_mpq().numerator());
            return mk_const(tmp);
        }

        polynomial * mk_polynomial(var x, unsigned k) {
            SASSERT(x != null_var);
            if (k == 0) {
                numeral one;
                m_manager.set(one, 1);
                return mk_const(one);
            }
            ptr_buffer<poly_or_num> new_args;
            for (unsigned i = 0; i < k; i++)
                new_args.push_back(0);
            numeral * new_arg = mk_numeral();
            m_manager.set(*new_arg, 1);
            new_args.push_back(to_poly_or_num(new_arg));
            return mk_poly(new_args.size(), new_args.data(), x);
        }

        poly_or_num * unpack(polynomial const * p) {
            if (p == nullptr) {
                return nullptr;
            }
            else if (is_const(p)) {
                SASSERT(p->size() == 1);
                SASSERT(p->max_var() == null_var);
                return p->arg(0);
            }
            else {
                return to_poly_or_num(const_cast<polynomial*>(p));
            }
        }

        polynomial * pack(poly_or_num * p) {
            if (p == nullptr)
                return nullptr;
            else if (is_num(p))
                return mk_poly(1, &p, null_var);
            else
                return to_poly(p);
        }

        poly_or_num * mul_core(numeral const & c, poly_or_num * p) {
            if (m_manager.is_zero(c) || p == nullptr) {
                return nullptr;
            }
            else if (is_num(p)) {
                numeral * r = mk_numeral();
                m_manager.mul(c, to_num(p), *r);
                return to_poly_or_num(r);
            }
            else {
                polynomial * _p = to_poly(p);
                unsigned sz = _p->size();
                SASSERT(sz > 1);
                ptr_buffer<poly_or_num> new_args;
                for (unsigned i = 0; i < sz; i++) {
                    new_args.push_back(mul_core(c, _p->arg(i)));
                }
                return mk_poly_core(new_args.size(), new_args.data(), _p->max_var());
            }
        }

        polynomial * mul(numeral const & c, polynomial const * p) {
            return pack(mul_core(c, unpack(p)));
        }

        polynomial * neg(polynomial const * p) {
            numeral minus_one;
            m_manager.set(minus_one, -1);
            return pack(mul_core(minus_one, unpack(p)));
        }

        poly_or_num * add_core(numeral const & c, poly_or_num * p) {
            if (m_manager.is_zero(c)) {
                return p;
            }
            else if (p == nullptr) {
                numeral * r = mk_numeral();
                m_manager.set(*r, c);
                return to_poly_or_num(r);
            }
            else if (is_num(p)) {
                numeral a;
                m_manager.add(c, to_num(p), a);
                if (m_manager.is_zero(a))
                    return nullptr;
                numeral * new_arg = mk_numeral();
                m_manager.swap(*new_arg, a);
                return to_poly_or_num(new_arg);
            }
            else {
                polynomial * _p = to_poly(p);
                unsigned sz = _p->size();
                SASSERT(sz > 1);
                ptr_buffer<poly_or_num> new_args;
                new_args.push_back(add_core(c, _p->arg(0)));
                for (unsigned i = 1; i < sz; i++)
                    new_args.push_back(_p->arg(1));
                return mk_poly_core(new_args.size(), new_args.data(), _p->max_var());
            }
        }

        polynomial * add(numeral const & c, polynomial const * p) {
            return pack(add_core(c, unpack(p)));
        }

#if 0
        polynomial * add_lt(polynomial const * p1, polynomial const * p2) {
            // Add non-constant polynomials p1 and p2 when max_var(p1) < max_var(p2)
            SASSERT(p1->max_var() != null_var);
            SASSERT(p2->max_var() != null_var);
            SASSERT(p1->max_var() < p2->max_var());

            unsigned sz = p2->size();
            ptr_buffer<poly_or_num> new_args;
            poly_or_num * pn0 = p2->arg(0);
            if (pn0 == 0) {
                new_args.push_back(to_poly_or_num(const_cast<polynomial*>(p1)));
            }
            else if (is_num(pn0)) {
                SASSERT(!is_const(p1));
                polynomial * new_arg = add(to_num(pn0), p1);
                SASSERT(!is_zero(new_arg));
                SASSERT(!is_const(new_arg));
                new_args.push_back(to_poly_or_num(new_arg));
            }
            else {
                SASSERT(is_poly(pn0));
                polynomial * new_arg = add(p1, to_poly(pn0));
                new_args.push_back(to_poly_or_num(new_arg));
            }
            for (unsigned i = 1; i < sz; i++)
                new_args.push_back(p2->arg(i));
            return mk_poly(sz, new_args.c_ptr(), p2->max_var());
        }
        
        polynomial * add(polynomial const * p1, polynomial const * p2) {
            if (is_zero(p1))
                return const_cast<polynomial*>(p2);
            if (is_zero(p2))
                return const_cast<polynomial*>(p1);
            var x1 = p1->max_var();
            var x2 = p2->max_var();
            if (x1 == null_var) {
                SASSERT(is_const(p1));
                return add(to_num(p1->arg(0)), p2);
            }
            if (x2 == null_var) {
                SASSERT(is_const(p2));
                return add(to_num(p2->arg(0)), p1);
            }
            if (x1 < x2)
                return add_lt(p1, p2);
            if (x2 < x1)
                return add_lt(p2, p1);
            SASSERT(x1 == x2);
            unsigned sz1 = p1->size();
            unsigned sz2 = p2->size();
            unsigned msz = std::min(sz1, sz2);
            ptr_buffer<poly_or_num> new_args;
            for (unsigned i = 0; i < msz; i++) {
                poly_or_num * pn1 = p1->arg(i);
                poly_or_num * pn2 = p2->arg(i);
                if (pn1 == 0) {
                    new_args.push_back(pn2);
                    continue;
                }
                if (pn2 == 0) {
                    new_args.push_back(pn1);
                    continue;
                }
                SASSERT(pn1 != 0 && pn2 != 0);
                if (is_num(pn1)) {
                    if (is_num(pn2)) {
                        SASSERT(is_num(pn1) && is_num(pn2));
                        numeral a;
                        m_manager.add(to_num(pn1), to_num(pn2), a);
                        if (m_manager.is_zero(a)) {
                            new_args.push_back(0);
                        }
                        else {
                            numeral * new_arg = mk_numeral();
                            m_manager.swap(*new_arg, a);
                            new_args.push_back(to_poly_or_num(new_arg));
                        }
                    }
                    else {
                        SASSERT(is_num(pn1) && is_poly(pn2));
                        new_args.push_back(to_poly_or_num(add(to_num(pn1), to_poly(pn2))));                        
                    }
                }
                else {
                    if (is_num(pn2)) {
                        SASSERT(is_poly(pn1) && is_num(pn2));
                        new_args.push_back(to_poly_or_num(add(to_num(pn2), to_poly(pn1))));
                    }
                    else {
                        SASSERT(is_poly(pn1) && is_poly(pn2));
                        new_args.push_back(to_poly_or_num(add(to_poly(pn1), to_poly(pn2))));                        
                    }
                }
            }
            SASSERT(new_args.size() == sz1 || new_args.size() == sz2);
            for (unsigned i = msz; i < sz1; i++) {
                new_args.push_back(p1->arg(i));
            }
            for (unsigned i = msz; i < sz2; i++) {
                new_args.push_back(p2->arg(i));
            }
            SASSERT(new_args.size() == std::max(sz1, sz2));
            return mk_poly(new_args.size(), new_args.c_ptr(), x1);
        }

        class resetter_mul_buffer;
        friend class resetter_mul_buffer;
        class resetter_mul_buffer {
            imp &                   m_owner;
            ptr_buffer<poly_or_num> m_buffer;
        public:
            resetter_mul_buffer(imp & o, ptr_buffer<poly_or_num> & b):m_owner(o), m_buffer(b) {}
            ~resetter_mul_buffer() {
                m_owner.dec_ref_args(m_buffer.size(), m_buffer.c_ptr());
                m_buffer.reset();
            }
        };
        
        void acc_mul_xk(ptr_buffer<poly_or_num> & mul_buffer, unsigned k, polynomial * p) {
            if (mul_buffer[k] == 0) {
                mul_buffer[k] = to_poly_or_num(p);
                inc_ref(p);
            }
            else {
                polynomial * new_p;
                if (is_num(mul_buffer[k]))
                    new_p = add(to_num(mul_buffer.get(k)), p);
                else
                    new_p = add(p, to_poly(mul_buffer.get(k)));
                if (is_zero(new_p)) {
                    dec_ref(mul_buffer[k]);
                    mul_buffer[k] = 0;
                }
                else {
                    inc_ref(new_p);
                    dec_ref(mul_buffer[k]);
                    mul_buffer[k] = to_poly_or_num(new_p);
                }
            }
        }

        void acc_mul_xk(ptr_buffer<poly_or_num> & mul_buffer, unsigned k, numeral & a) {
            if (mul_buffer.get(k) == 0) { 
                numeral * new_arg = mk_numeral();
                m_manager.swap(*new_arg, a);
                mul_buffer[k] = to_poly_or_num(new_arg);
            }
            else {
                if (is_num(mul_buffer[k])) {
                    m_manager.add(to_num(mul_buffer[k]), a, to_num(mul_buffer[k]));
                    if (m_manager.is_zero(to_num(mul_buffer[k]))) {
                        del_numeral(to_num_ptr(mul_buffer[k]));
                        mul_buffer[k] = 0;
                    }
                }
                else {
                    polynomial * new_p = add(a, to_poly(mul_buffer.get(k)));
                    if (is_zero(new_p)) {
                        dec_ref(mul_buffer[k]);
                        mul_buffer[k] = 0;
                    }
                    else {
                        inc_ref(new_p);
                        dec_ref(mul_buffer[k]);
                        mul_buffer[k] = to_poly_or_num(new_p);
                    }
                }
            }
        }

        polynomial * mul_lt(polynomial const * p1, polynomial const * p2) {
            unsigned sz2 = p2->size();
            
            // TODO
            return 0;
        }

        polynomial * mul(polynomial const * p1, polynomial const * p2) {
            var x1 = p1->max_var();
            var x2 = p2->max_var();
            if (x1 == null_var) {
                SASSERT(is_const(p1));
                return mul(to_num(p1->arg(0)), p2);
            }
            if (x2 == null_var) {
                SASSERT(is_const(p2));
                return mul(to_num(p2->arg(0)), p1);
            }
            if (x1 < x2)
                return mul_lt(p1, p2);
            if (x2 < x1)
                return mul_lt(p2, p1);
            SASSERT(x1 == x2);
            if (degree(p1) < degree(p2))
                std::swap(p1, p2);
            unsigned sz = degree(p1) * degree(p2) + 1;
            ptr_buffer<poly_or_num> mul_buffer;
            resetter_mul_buffer resetter(*this, mul_buffer);
            mul_buffer.resize(sz);
            unsigned sz1 = p1->size();
            unsigned sz2 = p2->size();
            for (unsigned i1 = 0; i1 < sz1; i1++) {
                poly_or_num * pn1 = p1->arg(i1);
                if (pn1 == 0)
                    continue;
                for (unsigned i2 = 0; i2 < sz2; i2++) {
                    poly_or_num * pn2 = p2->arg(i2);
                    if (pn2 == 0)
                        continue;
                    unsigned i = i1+i2;
                    if (is_num(pn1)) {
                        if (is_num(pn2)) {
                            SASSERT(is_num(pn1) && is_num(pn2));
                            scoped_numeral a(m_manager); 
                            m_manager.mul(to_num(pn1), to_num(pn2), a);
                            acc_mul_xk(mul_buffer, i, a);
                        }
                        else {
                            SASSERT(is_num(pn1) && is_poly(pn2));
                            polynomial_ref p(pm());
                            p = mul(to_num(pn1), to_poly(pn2));
                            acc_mul_xk(mul_buffer, i, p);                        
                        }
                    }
                    else {
                        if (is_num(pn2)) {
                            SASSERT(is_poly(pn1) && is_num(pn2));
                            polynomial_ref p(pm());
                            p = mul(to_num(pn2), to_poly(pn1));
                            acc_mul_xk(mul_buffer, i, p);                        
                        }
                        else {
                            SASSERT(is_poly(pn1) && is_poly(pn2));
                            polynomial_ref p(pm());
                            p = mul(to_poly(pn2), to_poly(pn1));
                            acc_mul_xk(mul_buffer, i, p);                        
                        }
                    }
                }
            }
            return mk_poly(mul_buffer.size(), mul_buffer.c_ptr(), x1);
        }
#endif

        void display(std::ostream & out, polynomial const * p, display_var_proc const & proc, bool use_star) {
            var x      = p->max_var();
            bool first = true;
            unsigned i = p->size();
            while (i > 0) {
                --i;
                poly_or_num * pn = p->arg(i);
                if (pn == nullptr)
                    continue;
                if (first)
                    first = false;
                else
                    out << " + ";
                if (is_num(pn)) {
                    numeral & a = to_num(pn);
                    if (i == 0) {
                        m_manager.display(out, a);
                    }
                    else {
                        if (m_manager.is_one(a)) {
                            proc(out, x);
                            if (i > 1)
                                out << "^" << i;
                        }
                        else {
                            m_manager.display(out, a);
                            if (use_star)
                                out << "*";
                            else
                                out << " ";
                            proc(out, x);
                            if (i > 1)
                                out << "^" << i;
                        }
                    }
                }
                else {
                    SASSERT(is_poly(pn));
                    if (i == 0) {
                        display(out, to_poly(pn), proc, use_star);
                    }
                    else {
                        bool add_paren = false;
                        if (i > 0)
                            add_paren = !is_monomial(to_poly(pn));
                        if (add_paren)
                            out << "(";
                        display(out, to_poly(pn), proc, use_star);
                        if (add_paren)
                            out << ")";
                        if (i > 0) {
                            if (use_star)
                                out << "*";
                            else
                                out << " ";
                            proc(out, x);
                            if (i > 1)
                                out << "^" << i;
                        }
                    }
                }
            }
        }
   
    };

    manager:: manager(numeral_manager & m, small_object_allocator * a) {
        m_imp = alloc(imp, *this, m, a);
    }

    manager::~manager() {
        dealloc(m_imp);
    }

    bool manager::is_zero(polynomial const * p) {
        return p == nullptr;
    }

#if 0     
    bool manager::is_const(polynomial const * p) {
        return imp::is_const(p);
    }

    bool manager::is_univariate(polynomial const * p) {
        return imp::is_univariate(p);
    }

    bool manager::is_monomial(polynomial const * p) const {
        return m_imp->is_monomial(p);
    }

    bool manager::eq(polynomial const * p1, polynomial const * p2) {
        return m_imp->eq(p1, p2);
    }

    polynomial * manager::mk_zero() {
        return m_imp->mk_zero();
    }

    polynomial * manager::mk_const(numeral const & r) {
        return m_imp->mk_const(r);
    }

    polynomial * manager::mk_const(rational const & a) {
        return m_imp->mk_const(a);
    }

    polynomial * manager::mk_polynomial(var x, unsigned k) {
        return m_imp->mk_polynomial(x, k);
    }

    polynomial * manager::mul(numeral const & r, polynomial const * p) {
        return m_imp->mul(r, p);
    }

    polynomial * manager::neg(polynomial const * p) {
        return m_imp->neg(p);
    }

    polynomial * manager::add(numeral const & r, polynomial const * p) {
        return m_imp->add(r, p);
    }
    
    polynomial * manager::add(polynomial const * p1, polynomial const * p2) {
        return m_imp->add(p1, p2);
    }

    var manager::max_var(polynomial const * p) {
        return p->max_var();
    }

    unsigned manager::size(polynomial const * p) {
        return p->size();
    }

    void manager::display(std::ostream & out, polynomial const * p, display_var_proc const & proc, bool use_star) const {
        return m_imp->display(out, p, proc, use_star);
    }
#endif

};
