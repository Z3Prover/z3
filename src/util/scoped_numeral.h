/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    scoped_numeral.h

Abstract:

    Wrapper for easying the pain when using primitive numeral objects such as:
       mpz, mpq, mpbq, mpf, mpzp

Author:

    Leonardo de Moura (leonardo) 2011-12-03

Revision History:

--*/
#ifndef _SCOPED_NUMERAL_H_
#define _SCOPED_NUMERAL_H_

template<typename Manager>
class _scoped_numeral {
public:
    typedef typename Manager::numeral numeral;
private:
    Manager & m_manager;
    numeral   m_num;
public:
    _scoped_numeral(Manager & m):m_manager(m) {}
    _scoped_numeral(_scoped_numeral const & n):m_manager(n.m_manager) { m().set(m_num, n.m_num); }
    ~_scoped_numeral() { m_manager.del(m_num); }

    Manager & m() const { return m_manager; }

    operator numeral const &() const { return m_num; }
    operator numeral&() { return m_num; }
    numeral const & get() const { return m_num; }
    numeral & get() { return m_num; }
    
    _scoped_numeral & operator=(_scoped_numeral const & n) {
        if (this == &n)
            return *this;
        m().set(m_num, n.m_num);
        return *this;
    }

    _scoped_numeral & operator=(int n) {
        m().set(m_num, n);
        return *this;
    }

    _scoped_numeral & operator=(numeral const & n) {
        m().set(m_num, n);
        return *this;
    }

    void reset() {
        m().reset(m_num);
    }

    void swap(_scoped_numeral & n) {
        m_num.swap(n.m_num);
    }

    void swap(numeral & n) {
        m_num.swap(n);
    }

    _scoped_numeral & operator+=(numeral const & a) {
        m().add(m_num, a, m_num);
        return *this;
    }

    _scoped_numeral & operator-=(numeral const & a) {
        m().sub(m_num, a, m_num);
        return *this;
    }

    _scoped_numeral & operator*=(numeral const & a) {
        m().mul(m_num, a, m_num);
        return *this;
    }

    _scoped_numeral & operator/=(numeral const & a) {
        m().div(m_num, a, m_num);
        return *this;
    }

    _scoped_numeral & operator%=(numeral const & a) {
        m().rem(m_num, a, m_num);
        return *this;
    }

    friend bool operator==(_scoped_numeral const & a, numeral const & b) {
        return a.m().eq(a, b);
    }

    friend bool operator!=(_scoped_numeral const & a, numeral const & b) {
        return !a.m().eq(a, b);
    }

    friend bool operator<(_scoped_numeral const & a, numeral const & b) {
        return a.m().lt(a, b);
    }

    friend bool operator>(_scoped_numeral const & a, numeral const & b) {
        return a.m().gt(a, b);
    }

    friend bool operator<=(_scoped_numeral const & a, numeral const & b) {
        return a.m().le(a, b);
    }

    friend bool operator>=(_scoped_numeral const & a, numeral const & b) {
        return a.m().ge(a, b);
    }

    bool is_zero() const {
        return m().is_zero(*this);
    }

    bool is_pos() const {
        return m().is_pos(*this);
    }

    bool is_neg() const {
        return m().is_neg(*this);
    }

    bool is_nonpos() const {
        return m().is_nonpos(*this);
    }

    bool is_nonneg() const {
        return m().is_nonneg(*this);
    }

    friend bool is_zero(_scoped_numeral const & a) {
        return a.m().is_zero(a);
    }

    friend bool is_pos(_scoped_numeral const & a) {
        return a.m().is_pos(a);
    }

    friend bool is_neg(_scoped_numeral const & a) {
        return a.m().is_neg(a);
    }

    friend bool is_nonneg(_scoped_numeral const & a) {
        return a.m().is_nonneg(a);
    }

    friend bool is_nonpos(_scoped_numeral const & a) {
        return a.m().is_nonpos(a);
    }

    friend _scoped_numeral abs(_scoped_numeral const& a) {
        _scoped_numeral res(a);
        a.m().abs(res);
        return res;
    }

    void neg() {
        m().neg(m_num);
    }

    friend _scoped_numeral operator+(_scoped_numeral const & r1, numeral const & r2) { 
        return _scoped_numeral(r1) += r2; 
    }
    
    friend _scoped_numeral operator-(_scoped_numeral const & r1, numeral const & r2) { 
        return _scoped_numeral(r1) -= r2; 
    }

    friend _scoped_numeral operator*(_scoped_numeral const & r1, numeral const & r2) { 
        return _scoped_numeral(r1) *= r2; 
    }
    
    friend _scoped_numeral operator/(_scoped_numeral const & r1, numeral const & r2) { 
        return _scoped_numeral(r1) /= r2; 
    }

    friend std::ostream & operator<<(std::ostream & out, _scoped_numeral const & s) {
        s.m().display(out, s);
        return out;
    }
                                 
};

#endif
