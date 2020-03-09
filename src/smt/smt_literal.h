/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_literal.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-18.

Revision History:

--*/
#ifndef SMT_LITERAL_H_
#define SMT_LITERAL_H_

#include "ast/ast.h"
#include "smt/smt_types.h"
#include "util/approx_set.h"

namespace smt {
    /**
       \brief The literal b is represented by the value 2*b, and
       the literal (not b) by the value 2*b + 1
       
    */
    class literal {
        int  m_val;
        
    public:
        literal():m_val(-2) {
            SASSERT(var() == null_bool_var && !sign());
        }
        
        explicit literal(bool_var v, bool sign = false):
            m_val((v << 1) + static_cast<int>(sign)) {
        }
        
        bool_var var() const { 
            return m_val >> 1; 
        }
        
        bool sign() const {
            return m_val & 1; 
        }
        
        int index() const {
            return m_val;
        }
        
        void neg() {
            m_val = m_val ^ 1;
        }
        
        friend literal operator~(literal l);
        
        friend literal to_literal(int x);

        void display(std::ostream & out, ast_manager & m, expr * const * bool_var2expr_map) const;

        void display_smt2(std::ostream & out, ast_manager & m, expr * const * bool_var2expr_map) const;

        void display_compact(std::ostream & out, expr * const * bool_var2expr_map) const;

        unsigned hash() const { return m_val; }
    };

    inline bool operator==(literal l1, literal l2) {
        return l1.index() == l2.index();
    }
    
    inline bool operator!=(literal l1, literal l2) {
        return l1.index() != l2.index();
    }
    
    inline bool operator<(literal l1, literal l2) {
        return l1.index() < l2.index();
    }
    
    inline literal operator~(literal l) {
        literal r;
        r.m_val = l.m_val ^ 1;
        return r;
    }
    
    inline literal to_literal(int x) {
        literal l;
        l.m_val = x;
        return l;
    }
    
    const literal null_literal;
    const literal true_literal(true_bool_var, false); 
    const literal false_literal(true_bool_var, true);

    typedef svector<literal> literal_vector;
    typedef sbuffer<literal> literal_buffer;
    std::ostream & operator<<(std::ostream & out, literal l);
    std::ostream & operator<<(std::ostream & out, const literal_vector & v);

    void display_compact(std::ostream & out, unsigned num_lits, literal const * lits, expr * const * bool_var2expr_map);

    void display_verbose(std::ostream & out, ast_manager& m, unsigned num_lits, literal const * lits, expr * const * bool_var2expr_map, char const* sep = "\n");

    template<typename T>
    void neg_literals(unsigned num_lits, literal const * lits, T & result) {
        for (unsigned i = 0; i < num_lits; ++i) 
            result.push_back(~lits[i]);
    }

    struct literal2unsigned { unsigned operator()(literal l) const { return l.index(); } };

    typedef approx_set_tpl<literal, literal2unsigned> literal_approx_set;

    bool backward_subsumption(unsigned num_lits1, literal const * lits1, unsigned num_lits2, literal const * lits2);
};

#endif /* SMT_LITERAL_H_ */

