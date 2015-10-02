/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    upolynomial_factorization_int.h

Abstract:
    
    (Internal) header file for univariate polynomial factorization.
    This classes are exposed for debugging purposes only.

Author:

    Dejan (t-dejanj) 2011-11-29

Notes:

   [1] Elwyn Ralph Berlekamp. Factoring Polynomials over Finite Fields. Bell System Technical Journal, 
       46(8-10):1853-1859, 1967.
   [2] Donald Ervin Knuth. The Art of Computer Programming, volume 2: Seminumerical Algorithms. Addison Wesley, third 
       edition, 1997.
   [3] Henri Cohen. A Course in Computational Algebraic Number Theory. Springer Verlag, 1993.

--*/
#ifndef UPOLYNOMIAL_FACTORIZATION_INT_H_
#define UPOLYNOMIAL_FACTORIZATION_INT_H_

#include"upolynomial_factorization.h"

namespace upolynomial {
    // copy p from some manager to zp_p in Z_p[x]
    inline void to_zp_manager(zp_manager & zp_upm, numeral_vector & p) {
        zp_numeral_manager & zp_nm(zp_upm.m());
        for (unsigned i = 0; i < p.size(); ++ i) {
            zp_nm.p_normalize(p[i]);
        }
        zp_upm.trim(p);
    }

    // copy p from some manager to zp_p in Z_p[x]
    inline void to_zp_manager(zp_manager & zp_upm, numeral_vector const & p, numeral_vector & zp_p) {
        zp_numeral_manager & zp_nm(zp_upm.m());
        zp_upm.reset(zp_p);
        for (unsigned i = 0; i < p.size(); ++ i) {
            numeral p_i; // no need to delete, we keep it pushed in zp_p
            zp_nm.set(p_i, p[i]);
            zp_p.push_back(p_i);
        }
        zp_upm.trim(zp_p);
    }

    /**
       \brief Contains all possible degrees of a factorization of a polynomial.
       If 
         p = p1^{k_1} * ... * pn^{k_n} with p_i of degree d_i
       then it is represents numbers of the for \sum a_i*d_i, where a_i <= k_i. Two numbers always in the set are
       deg(p) and 0. 

    */
    class factorization_degree_set {
    
        // the set itself, a (m_max_degree)-binary number
        bit_vector m_set;
        
    public:

        factorization_degree_set() { }

        factorization_degree_set(zp_factors const & factors)
        {
            zp_manager & upm = factors.upm();
            // the set contains only {0}
            m_set.push_back(true);
            for (unsigned i = 0; i < factors.distinct_factors(); ++ i) {
                unsigned degree = upm.degree(factors[i]);
                unsigned multiplicity = factors.get_degree(i);                
                for (unsigned k = 0; k < multiplicity; ++ k) {
                    bit_vector tmp(m_set);
                    m_set.shift_right(degree);
                    m_set |= tmp;
                }
            }
            SASSERT(in_set(0) && in_set(factors.get_degree()));
        }

        unsigned max_degree() const { return m_set.size() - 1; }

        void swap(factorization_degree_set & other) {
            m_set.swap(other.m_set);
        }

        bool is_trivial() const { 
            // check if set = {0, n}
            for (int i = 1; i < (int) m_set.size() - 1; ++ i) {
                if (m_set.get(i)) return false;
            }
            return true;
        }

        void remove(unsigned k) {
            m_set.set(k, false);
        }

        bool in_set(unsigned k) const { 
            return m_set.get(k);
        }

        void intersect(const factorization_degree_set& other) {
            m_set &= other.m_set;
        }

        void display(std::ostream & out) const {
            out << "[0";
            for (unsigned i = 1; i <= max_degree(); ++ i) {
                if (in_set(i)) {
                    out << ", " << i;
                }
            }
            out << "] represented by " << m_set;
        }
    };

    /**
       \brief A to iterate through all combinations of factors. This is only needed for the factorization, and we 
       always iterate through the 
    */
    template <typename factors_type>
    class factorization_combination_iterator_base {

    protected:


        // total size of available factors
        int                    m_total_size;
        // maximal size of the selection
        int                    m_max_size;
        // the factors to select from
        factors_type const   & m_factors;
        // which factors are enabled
        svector<bool>          m_enabled;
        // the size of the current selection
        int                    m_current_size;
        // the current selection: indices at positions < m_current_size, other values are maxed out
        svector<int>           m_current;
        
        /**
           Assuming a valid selection m_current[0], ..., m_current[position], try to find the next option for
           m_current[position], i.e. the first bigger one that's enabled.
        */
        int find(int position, int upper_bound) {
            int current = m_current[position] + 1;
            while (current < upper_bound && !m_enabled[current]) {
                current ++;
            }
            if (current == upper_bound) {
                return -1;
            } else {
                return current;
            }
        }

    public:

        factorization_combination_iterator_base(factors_type const & factors)
        : m_total_size(factors.distinct_factors()), 
          m_max_size(factors.distinct_factors()/2), 
          m_factors(factors)
        {    
            SASSERT(factors.total_factors() > 1);
            SASSERT(factors.total_factors() == factors.distinct_factors());
            // enable all to start with
            m_enabled.resize(m_factors.distinct_factors(), true);
            // max out the m_current so that it always fits
            m_current.resize(m_factors.distinct_factors()+1, m_factors.distinct_factors());
            m_current_size = 0;
        }

        /**
           \brief Returns the factors we are enumerating through.
        */
        factors_type const & get_factors() const { 
            return m_factors; 
        }

        /**
           \brief Computes the next combination of factors and returns true if it exists. If remove current is true
           it will eliminate the current selected elements from any future selection.
        */
        bool next(bool remove_current) {
            
            int max_upper_bound = m_factors.distinct_factors();
            
            do {

                // the index we are currently trying to fix
                int current_i = m_current_size - 1;
                // the value we found as plausable (-1 we didn't find anything)
                int current_value = -1;

                if (remove_current) {
                    SASSERT(m_current_size > 0);
                    // disable the elements of the current selection from ever appearing again
                    for (current_i = m_current_size - 1; current_i > 0; -- current_i) {
                        SASSERT(m_enabled[m_current[current_i]]);
                        m_enabled[m_current[current_i]] = false;
                        m_current[current_i] = max_upper_bound;
                    }
                    // the last one
                    SASSERT(m_enabled[m_current[0]]);
                    m_enabled[m_current[0]] = false;
                    // not removing current anymore
                    remove_current = false;
                    // out max size is also going down
                    m_total_size -= m_current_size;
                    m_max_size = m_total_size/2;
                } 
            
                // we go back to the first one that can be increased (if removing current go all the way)
                while (current_i >= 0) {
                    current_value = find(current_i, m_current[current_i + 1]);
                    if (current_value >= 0) {
                        // found one
                        m_current[current_i] = current_value;
                        break;
                    } else {
                        // go back some more
                        current_i --;
                    }
                }
            
                do {
                        
                    if (current_value == -1) {
                        // we couldn't find any options, we have to increse size and start from the first one of that size
                        if (m_current_size >= m_max_size) {
                            return false;
                        } else {     
                            m_current_size ++;
                            m_current[0] = -1;
                            current_i = 0;
                            current_value = find(current_i, max_upper_bound);
                            // if we didn't find any, we are done
                            if (current_value == -1) {
                                return false;
                            } else {
                                m_current[current_i] = current_value;
                            }
                        }
                    } 

                    // ok we have a new selection for the current one
                    for (current_i ++; current_i < m_current_size; ++ current_i) {
                        // start from the previous one
                        m_current[current_i] = m_current[current_i-1];
                        current_value = find(current_i, max_upper_bound);
                        if (current_value == -1) {
                            // screwed, didn't find the next one, this means we need to increase the size
                            m_current[0] = -1;
                            break;
                        } else {
                            m_current[current_i] = current_value;
                        }
                    }
                        
                } while (current_value == -1);
                    
            } while (filter_current());
            
            // found the next one, hurray
            return true;
        }

        /**
           \brief A function that returns true if the current combination should be ignored.
        */
        virtual bool filter_current() const = 0;

        /**
           \brief Returns the size of the current selection (cardinality)
        */
        unsigned left_size() const {
            return m_current_size;
        }

        /**
           \brief Returns the size of the rest of the current selection (cardinality)
        */
        unsigned right_size() const {
            return m_total_size - m_current_size;
        }

        void display(std::ostream& out) const {            
            out << "[ ";
            for (unsigned i = 0; i < m_current.size(); ++ i) {
                out << m_current[i] << " ";
            }          
            out << "] from [ ";
            for (unsigned i = 0; i < m_factors.distinct_factors(); ++ i) {
                if (m_enabled[i]) {
                    out << i << " ";
                }
            }                      
            out << "]" << std::endl;
        }


    };

    class ufactorization_combination_iterator : public factorization_combination_iterator_base<zp_factors> {
    
        // the degree sets to choose from
        factorization_degree_set const & m_degree_set;

    public:
        
        ufactorization_combination_iterator(zp_factors const & factors, factorization_degree_set const & degree_set)
        : factorization_combination_iterator_base<zp_factors>(factors),
          m_degree_set(degree_set) 
        {}

        /**
           \brief Filter the ones not in the degree set.
        */
        bool filter_current() const {
            
            // select only the ones that have degrees in the degree set
            if (!m_degree_set.in_set(current_degree())) {
                return true;
            }            
            return false;
        }

        /** 
           \brief Returns the degree of the current selection.
        */
        unsigned current_degree() const {
            unsigned degree = 0;
            zp_manager & upm = m_factors.pm();
            for (unsigned i = 0; i < left_size(); ++ i) {
                degree += upm.degree(m_factors[m_current[i]]);
            }
            return degree;
        }        

        void left(numeral_vector & out) const {
            SASSERT(m_current_size > 0);
            zp_manager & upm = m_factors.upm();
            upm.set(m_factors[m_current[0]].size(), m_factors[m_current[0]].c_ptr(), out);
            for (int i = 1; i < m_current_size; ++ i) {
                upm.mul(out.size(), out.c_ptr(), m_factors[m_current[i]].size(), m_factors[m_current[i]].c_ptr(), out);
            }
        }

        void get_left_tail_coeff(numeral const & m, numeral & out) {
            zp_numeral_manager &  nm = m_factors.upm().m();
            nm.set(out, m);
            for (int i = 0; i < m_current_size; ++ i) {
                nm.mul(out, m_factors[m_current[i]][0], out);
            }
        }

        void get_right_tail_coeff(numeral const & m, numeral & out) {
            zp_numeral_manager &  nm = m_factors.upm().m();
            nm.set(out, m);

            unsigned current = 0;
            unsigned selection_i = 0;

            // selection is ordered, so we just take the ones in between that are not disable
            while (current <  m_factors.distinct_factors()) {
                if (!m_enabled[current]) {
                    // by skipping the disabled we never skip a selected one
                    current ++;
                } else {   
                    if (selection_i >= m_current.size() || (int) current < m_current[selection_i]) {
                        SASSERT(m_factors.get_degree(current) == 1);
                        nm.mul(out, m_factors[current][0], out);
                        current ++;
                    } else {
                        current ++;
                        selection_i ++;
                    }
                }
            }
        }

        void right(numeral_vector & out) const {
            SASSERT(m_current_size > 0);
            zp_manager & upm = m_factors.upm();
            upm.reset(out);

            unsigned current = 0;
            unsigned selection_i = 0;

            // selection is ordered, so we just take the ones in between that are not disable
            while (current <  m_factors.distinct_factors()) {
                if (!m_enabled[current]) {
                    // by skipping the disabled we never skip a selected one
                    current ++;
                } else {   
                    if (selection_i >= m_current.size() || (int) current < m_current[selection_i]) {
                        SASSERT(m_factors.get_degree(current) == 1);
                        if (out.size() == 0) {
                            upm.set(m_factors[current].size(), m_factors[current].c_ptr(), out);
                        } else {
                            upm.mul(out.size(), out.c_ptr(), m_factors[current].size(), m_factors[current].c_ptr(), out);
                        }
                        current ++;
                    } else {
                        current ++;
                        selection_i ++;
                    }
                }
            }
        }
    };
};

#endif
