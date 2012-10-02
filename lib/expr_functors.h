/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    expr_functors.h

Abstract:

    Functors on expressions.

Author:

    Nikolaj Bjorner (nbjorner) 2010-02-19

Revision History:

    Hoisted from quant_elim.

--*/

#ifndef __EXPR_FUNCTORS_H__
#define __EXPR_FUNCTORS_H__

#include "ast.h"
#include "expr_map.h"

class i_expr_pred {
public:
    virtual bool operator()(expr* e) = 0;
    virtual ~i_expr_pred() {}
};

/**
   \brief Memoizing predicate functor on sub-expressions.
   
   The class is initialized with a predicate 'p' on expressions.
   
   The class is memoizing. 

*/

class check_pred {
    i_expr_pred&    m_pred;        
    ast_mark        m_pred_holds;
    ast_mark        m_visited;
    expr_ref_vector m_refs;
public:        
    check_pred(i_expr_pred& p, ast_manager& m) : m_pred(p), m_refs(m) {}
        
    bool operator()(expr* e);

    void reset() { m_pred_holds.reset(); m_visited.reset(); m_refs.reset(); }

private:        
    void visit(expr* e);        
};

/**
   \brief Determine if expression 'e' or vector of expressions 'v' contains the app x
*/

class contains_app {
    class pred : public i_expr_pred {
        app* m_x;
    public:
        pred(app* x) : m_x(x) {}
        virtual bool operator()(expr* e) {
            return m_x == e;
        }
    };
    app_ref    m_x;
    pred       m_pred;
    check_pred m_check;
    
public:
    contains_app(ast_manager& m, app* x) : 
        m_x(x, m), m_pred(x), m_check(m_pred, m) {}
    
    bool operator()(expr* e) {
        return m_check(e);
    }
    
    bool operator()(expr_ref_vector const& v) {
        return (*this)(v.size(), v.c_ptr());
    }
    
    bool operator()(unsigned size, expr* const* es);

    app* x() const { return m_x; }
        
};

/**
   \brief Base class of functor that applies map to expressions.
*/
class map_proc {
protected:
    ast_manager&      m;
    expr_map          m_map;
    ptr_vector<expr>  m_args;        
public:        
    map_proc(ast_manager& m):
        m(m),
        m_map(m)
    {}
    
    void reset() { m_map.reset(); }
    
    void visit(var* e) { m_map.insert(e, e, 0); }
    
    void visit(quantifier* e);
    
    void reconstruct(app* a);
    
    expr* get_expr(expr* e);

};


#endif
