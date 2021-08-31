/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    basic_interval.h

Abstract:

    Basic interval arithmetic template for precise numerals: mpz, mpq, mpbq.
    Only basic support is provided. 
    There is no support for:
      - minus and plus infinity bounds.
      - mixed open/closed intervals such as (2, 3]
    The main customer of this package is the algebraic_number module.  

Author:

    Leonardo de Moura (leonardo) 2012-12-04.

Revision History:

--*/
#pragma once

template<typename numeral_manager, bool closed>
class basic_interval_manager {
public:
    typedef typename numeral_manager::numeral bound;

    class interval {
        friend class basic_interval_manager;
        bound m_lower;
        bound m_upper;
    public:
        bound const & lower() const { return m_lower; }
        bound const & upper() const { return m_upper; }
        bound & lower() { return m_lower; }
        bound & upper() { return m_upper; }
    };

    class scoped_interval {
        basic_interval_manager & m_manager;
        interval                 m_interval;
    public:
        scoped_interval(basic_interval_manager & m):m_manager(m) {}
        ~scoped_interval() { m_manager.del(m_interval); }

        basic_interval_manager & m() const { return m_manager; }
        operator interval const &() const { return m_interval; }
        operator interval&() { return m_interval; }
        interval const & get() const { return m_interval; }
        interval & get() { return m_interval; }
        void reset() { m().reset(m_interval); }
        void swap(scoped_interval & a) { m().swap(m_interval, a.m_interval); }
        void swap(interval & a) { m().swap(m_interval, a); }
        bound const & lower() const { return m_interval.lower(); }
        bound const & upper() const { return m_interval.upper(); }
        bound & lower() { return m_interval.lower(); }
        bound & upper() { return m_interval.upper(); }

        friend std::ostream & operator<<(std::ostream & out, scoped_interval const & a) {
            a.m().display(out, a.get());
            return out;
        }
    };

protected:
    numeral_manager & m_manager;
    bound             m_mul_curr;
    bound             m_mul_max;
    bound             m_mul_min;

public:
    typedef interval numeral; // allow intervals to be used by algorithms parameterized by numeral_manager

    basic_interval_manager(numeral_manager & m):
        m_manager(m) {
    }

    ~basic_interval_manager() {
        m().del(m_mul_curr);
        m().del(m_mul_max);
        m().del(m_mul_min);
    }

    numeral_manager & m() const { return m_manager; }

    /**
       \brief Delete interval
    */
    void del(interval & a) { 
        m().del(a.m_lower); 
        m().del(a.m_upper); 
    }

    /**
       \brief Delete and reset lower and upper bounds to 0
    */
    void reset(interval & a) {
        m().reset(a.m_lower);
        m().reset(a.m_upper);
    }

    bound const & lower(interval const & a) {
        return a.lower();
    }

    bound const & upper(interval const & a) {
        return a.upper();
    }
    
    /**
       \brief a <- (lower, upper)
    */
    void set(interval & a, bound const & lower, bound const & upper) {
        SASSERT(m().le(lower, upper));
        m().set(a.m_lower, lower);
        m().set(a.m_upper, upper);
    }

    /**
       \brief a <- b
    */
    void set(interval & a, interval const & b) {
        set(a, b.m_lower, b.m_upper);
    }

    /**
       \brief a <- (n, n)   
      
       Manager must be configured for closed intervals.
    */
    void set(interval & a, bound const & n) {
        m().set(a.m_lower, n);
        m().set(a.m_upper, n);
    }

    void set_lower(interval & a, bound const & n) {
        SASSERT(m().le(n, a.m_upper));
        m().set(a.m_lower, n);
    }

    void set_upper(interval & a, bound const & n) {
        SASSERT(m().le(a.m_lower, n));
        m().set(a.m_upper, n);
    }

    void swap(interval & a, interval & b) {
        m().swap(a.m_lower, b.m_lower);
        m().swap(a.m_upper, b.m_upper);
    }

    /**
       \brief a <- -a
    */
    void neg(interval & a) {
        m().neg(a.m_lower);
        m().neg(a.m_upper);
        m().swap(a.m_lower, a.m_upper);
    }
    
    /**
       \brief Return true if a does not contain any value.  We can
       only have empty intervals if the manager is configured to used
       open intervals.
    */
    bool is_empty(interval const & a) {
        return !closed && m().eq(a.m_lower, a.m_upper);
    }
    
    /**
       \brief Return true if all values in the given interval are positive.
    */
    bool is_pos(interval const & a) { return (closed && m().is_pos(a.m_lower)) || (!closed && m().is_nonneg(a.m_lower)); }

    /**
       \brief Return true if all values in the given interval are negative.
    */
    bool is_neg(interval const & a) { return (closed && m().is_neg(a.m_upper)) || (!closed && m().is_nonpos(a.m_upper)); }

    /**
       \brief Return true if 0 is in the interval.
    */
    bool contains_zero(interval const & a) { 
        return 
            (closed  && m().is_nonpos(a.m_lower) && m().is_nonneg(a.m_upper)) ||
            (!closed && m().is_neg(a.m_lower) && m().is_pos(a.m_upper));
    } 

    /**
       \brief Return true if all values in interval a are in interval b.
    */
    bool is_subset(interval const & a, interval const & b) {
        return m().le(b.m_lower, a.m_lower) && m().le(a.m_upper, b.m_upper);
    } 

    /**
       \brief Return true if there is no value v s.t. v \in a and v \in b.
    */
    bool disjoint(interval const & a, interval const & b) {
        return 
            (closed  && (m().lt(a.m_upper, b.m_lower) || m().lt(b.m_upper, a.m_lower))) ||
            (!closed && (m().le(a.m_upper, b.m_upper) || m().le(b.m_upper, a.m_lower)));
    }
    
    /**
       \brief Return true if all elements in a are smaller than all elements in b.
    */
    bool precedes(interval const & a, interval const & b) {
        return
            (closed  && (m().lt(a.m_upper, b.m_lower))) ||
            (!closed && (m().le(a.m_upper, b.m_lower)));
    }

    /**
       \brief Return true if all elements in a are smaller than b.
    */
    bool precedes(interval const & a, bound const & b) {
        return
            (closed  && (m().lt(a.m_upper, b))) ||
            (!closed && (m().le(a.m_upper, b)));
    }

    /**
       \brief Return true if a is smaller than all elements in b.
    */
    bool precedes(bound const & a, interval const & b) {
        return
            (closed  && (m().lt(a, b.m_lower))) ||
            (!closed && (m().le(a, b.m_lower)));
    }

    /**
       \brief a <- 1/a
       
       \pre a.m_lower and m_upper must not be 0.
       \pre bound must be a field.
    */
    void inv(interval & a) {
        SASSERT(numeral_manager::field());
        SASSERT(!contains_zero(a));
        SASSERT(!m().is_zero(a.m_lower) && !m().is_zero(a.m_upper));
        m().inv(a.m_lower);
        m().inv(a.m_upper);
        m().swap(a.m_lower, a.m_upper);
    }

    /**
       \brief c <- a + b
    */
    void add(interval const & a, interval const & b, interval & c) {
        m().add(a.m_lower, b.m_lower, c.m_lower);
        m().add(a.m_upper, b.m_upper, c.m_upper);
    }
    
    /**
       \brief c <- a - b
    */
    void sub(interval const & a, interval const & b, interval & c) {
        m().sub(a.m_lower, b.m_upper, c.m_lower);
        m().sub(a.m_upper, b.m_lower, c.m_upper);
    }

private:
    /**
       \brief Init the value of m_mul_max and m_mul_min using m_mul_curr
    */
    void init_mul_max_min() {
        m().set(m_mul_min, m_mul_curr);
        m().swap(m_mul_max, m_mul_curr);
    }

    /**
       \brief Update the value of m_mul_max and m_mul_min using m_mul_curr
    */
    void update_mul_max_min() {
        if (m().lt(m_mul_curr, m_mul_min))
            m().set(m_mul_min, m_mul_curr);
        if (m().gt(m_mul_curr, m_mul_max))
            m().swap(m_mul_max, m_mul_curr);
    }

public:
    /**
       \brief c <- a * b
    */
    void mul(interval const & a, interval const & b, interval & c) {
        m().mul(a.m_lower, b.m_lower, m_mul_curr);
        init_mul_max_min();
        m().mul(a.m_lower, b.m_upper, m_mul_curr);
        update_mul_max_min();
        m().mul(a.m_upper, b.m_lower, m_mul_curr);
        update_mul_max_min();
        m().mul(a.m_upper, b.m_upper, m_mul_curr);
        update_mul_max_min();
        m().swap(c.m_lower, m_mul_min);
        m().swap(c.m_upper, m_mul_max);
    }

    /**
       \brief c <- a/b
       
       \pre b m_lower and m_upper must not be 0
       \pre bound must be a field.
    */
    void div(interval const & a, interval const & b, interval & c) {
        SASSERT(numeral_manager::field());
        SASSERT(!contains_zero(b));
        SASSERT(!m().is_zero(b.m_lower) && !m().is_zero(b.m_upper));
        m().div(a.m_lower, b.m_lower, m_mul_curr);
        init_mul_max_min();
        m().div(a.m_lower, b.m_upper, m_mul_curr);
        update_mul_max_min();
        m().div(a.m_upper, b.m_lower, m_mul_curr);
        update_mul_max_min();
        m().div(a.m_upper, b.m_upper, m_mul_curr);
        update_mul_max_min();
        m().swap(c.m_lower, m_mul_min);
        m().swap(c.m_upper, m_mul_max);
    }

    /**
       \brief c <- a^n
    */
    void power(interval const & a, unsigned n, interval & c) {
        // Let a be of the form (l, u)
        if (n % 2 == 1) {
            // n is odd
            // c <- (l^n, u^n)
            m().power(a.m_lower, n, c.m_lower);
            m().power(a.m_upper, n, c.m_upper);
        }
        else {
            SASSERT(n % 2 == 0);
            m().power(a.m_lower, n, c.m_lower);
            m().power(a.m_upper, n, c.m_upper);
            if (m().is_nonneg(a.m_lower)) {
                // n is even and l >= 0
                // c <- (l^n, u^n)
                return;
            }
            if (m().is_neg(a.m_upper)) {
                // n is even and u < 0
                // c <- (u^n, l^n)
                m().swap(c.m_lower, c.m_upper);
                return;
            }
            // c <- (0, max(l^n, u^n))
            if (m().gt(c.m_lower, c.m_upper))
                m().swap(c.m_lower, c.m_upper);
            m().reset(c.m_lower);
        }
    }

    void display(std::ostream & out, interval const & a) {
        out << (closed ? "[" : "(") << m().to_string(a.m_lower) << ", " << m().to_string(a.m_upper) << (closed ? "]" : ")");
    }
};

