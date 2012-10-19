/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    pdr_util.h

Abstract:

    Utility functions for PDR.

Author:

    Krystof Hoder (t-khoder) 2011-8-19.

Revision History:

--*/

#ifndef _PDR_UTIL_H_
#define _PDR_UTIL_H_

#include "ast.h"
#include "ast_pp.h"
#include "obj_hashtable.h"
#include "ref_vector.h"
#include "simplifier.h"
#include "th_rewriter.h"
#include "trace.h"
#include "vector.h"
#include "arith_decl_plugin.h"
#include "bv_decl_plugin.h"


struct front_end_params;
class model;
class model_core;

namespace pdr {
    class manager;
    class prop_solver;

/**
 * Return the ceiling of base 2 logarithm of a number, 
 * or zero if the nmber is zero.
 */
unsigned ceil_log2(unsigned u);

typedef ptr_vector<app> app_vector;
typedef ptr_vector<func_decl> decl_vector;
typedef obj_hashtable<func_decl> func_decl_set;


std::string pp_cube(const ptr_vector<expr>& model, ast_manager& manager);
std::string pp_cube(const expr_ref_vector& model, ast_manager& manager);
std::string pp_cube(const ptr_vector<app>& model, ast_manager& manager);
std::string pp_cube(const app_ref_vector& model, ast_manager& manager);
std::string pp_cube(unsigned sz, app * const * lits, ast_manager& manager);
std::string pp_cube(unsigned sz, expr * const * lits, ast_manager& manager);


template<class TgtVect, class SrcVect>
void assign_vector_with_casting(TgtVect& tgt, const SrcVect& src)
{
    SASSERT(static_cast<const void*>(&tgt)!=static_cast<const void*>(&src));
    tgt.reset();
    typename SrcVect::data const * begin = src.c_ptr();
    typename SrcVect::data const * end = begin + src.size();
    for(typename SrcVect::data const * it = begin; it!=end; it++)
    {
        tgt.push_back(static_cast<typename TgtVect::data>(*it));
    }
/*    tgt.reset();
    typename SrcVect::const_iterator end = src.end();
    for(typename SrcVect::const_iterator it = src.begin(); it!=end; it++)
    {
        tgt.push_back(static_cast<typename TgtVect::data>(*it));
    }*/
}

template<class TgtType, class SrcType, class Mgr>
void append_ref_vector_with_casting(ref_vector<TgtType,Mgr> & tgt, const ref_vector<SrcType,Mgr> & src)
{
    SASSERT(static_cast<const void*>(&tgt)!=static_cast<const void*>(&src));
    SrcType * const * begin = src.c_ptr();
    SrcType * const * end = begin + src.size();
    for(SrcType * const * it = begin; it!=end; it++)
    {
        tgt.push_back(static_cast<TgtType *>(*it));
    }
}

template<class TgtType, class SrcType, class Mgr>
void assign_ref_vector_with_casting(ref_vector<TgtType,Mgr> & tgt, const ref_vector<SrcType,Mgr> & src)
{
    SASSERT(static_cast<const void*>(&tgt)!=static_cast<const void*>(&src));
    tgt.reset();
    append_ref_vector_with_casting(tgt, src);
}

template<class T,class M>
ref_vector<T,M>& assign_ref_vector(ref_vector<T,M> & tgt, const ref_vector<T,M> & src)
{
    SASSERT(static_cast<const void*>(&tgt)!=static_cast<const void*>(&src));
    //we support assignment only on vectors with the same manager
    SASSERT(&tgt.get_manager()==&src.get_manager());
    tgt.reset();
    tgt.append(src);
    return tgt;
}

template<class Type, class Mgr, class Comp>
void sort_ref_vect(ref_vector<Type,Mgr> & vect, Comp cmp)
{
    Type * * begin = vect.c_ptr();
    Type * * end = begin + vect.size();
    std::sort(begin, end, cmp);
}

/**
Into res put all elements that are in left but not in right.

This function can change the order of elements in left.
*/
template<class Type, class Mgr, class Comp>
void vect_set_diff(ref_vector<Type,Mgr> & left, ref_vector<Type,Mgr> & right, 
    ref_vector<Type,Mgr> & res, Comp cmp)
{
    sort_ref_vect(left, cmp);
    sort_ref_vect(right, cmp);

    res.reset();

    Type * const * lbegin = left.c_ptr();
    Type * const * lend = lbegin + left.size();
    Type * const * lit = lbegin;
    Type * const * rbegin = right.c_ptr();
    Type * const * rend = rbegin + right.size();
    Type * const * rit = rbegin;

    while(lit!=lend) {
        while(rit!=rend && lit!=lend && *rit==*lit) {
            ++rit;
            ++lit;
        }
        if(lit==lend) {
            return;
        }
        while(rit!=rend && cmp(*rit, *lit)) {
            ++rit;
        }
        while(lit!=lend && (rit==rend || cmp(*lit, *rit))) {
            res.push_back(*lit);
            ++lit;
        }
    }
}

/**
Ensure all elements from src are in tgt

This function can change the order of elements in tgt and src.
*/
template<class Type, class Mgr, class Comp>
void vect_set_union(ref_vector<Type,Mgr> & tgt, ref_vector<Type,Mgr> & src, Comp cmp)
{
    ref_vector<Type,Mgr> diff(tgt.get_manager());
    vect_set_diff(src, tgt, diff, cmp);
    tgt.append(diff);
}



class model_evaluator {
    ast_manager& m;
    arith_util   m_arith;
    bv_util      m_bv;
    obj_map<expr,rational> m_numbers;
    expr_ref_vector        m_refs;
    obj_map<expr, expr*>   m_values;
    model_ref m_model;

    //00 -- non-visited
    //01 -- X
    //10 -- false
    //11 -- true
    ast_fast_mark1 m1;
    ast_fast_mark2 m2;
    unsigned m_level1;
    unsigned m_level2;
    expr_mark m_visited;


    void reset();
    void setup_model(model_ref& model);
    void assign_value(expr* e, expr* v);
    bool get_assignment(expr* e, expr*& var, expr*& val);
    void collect(ptr_vector<expr> const& formulas, ptr_vector<expr>& tocollect);
    void process_formula(app* e, ptr_vector<expr>& todo, ptr_vector<expr>& tocollect);
    void prune_by_cone_of_influence(ptr_vector<expr> const & formulas, expr_ref_vector& model);
    void eval_arith(app* e);
    void eval_basic(app* e);
    void eval_iff(app* e, expr* arg1, expr* arg2);
    void inherit_value(expr* e, expr* v);

    //00 -- non-visited
    //01 -- X
    //10 -- false
    //11 -- true
    inline bool is_unknown(expr* x)  { return !m1.is_marked(x) && !m2.is_marked(x); }
    inline void set_unknown(expr* x)  { m1.reset_mark(x); m2.reset_mark(x); }
    inline bool is_x(expr* x)  { return !m1.is_marked(x) && m2.is_marked(x); }
    inline bool is_false(expr* x)  { return m1.is_marked(x) && !m2.is_marked(x); }
    inline bool is_true(expr* x)  { return m1.is_marked(x) && m2.is_marked(x); }
    inline void set_x(expr* x) { SASSERT(is_unknown(x)); m2.mark(x); }
    inline void set_v(expr* x) { SASSERT(is_unknown(x)); m1.mark(x); }
    inline void set_false(expr* x) { SASSERT(is_unknown(x)); m1.mark(x); }
    inline void set_true(expr* x) { SASSERT(is_unknown(x)); m1.mark(x); m2.mark(x); }
    inline void set_bool(expr* x, bool v) { if (v) { set_true(x); } else { set_false(x); } }
    inline rational const& get_number(expr* x) const { return m_numbers.find(x); }
    inline void set_number(expr* x, rational const& v) { set_v(x); TRACE("pdr_verbose", tout << mk_pp(x,m) << " " << v << "\n";); m_numbers.insert(x,v); }
    inline expr* get_value(expr* x) { return m_values.find(x); }
    inline void set_value(expr* x, expr* v) { set_v(x); m_refs.push_back(v); m_values.insert(x, v); }

    
protected:

    bool check_model(ptr_vector<expr> const & formulas);

public:
    model_evaluator(ast_manager& m) : m(m), m_arith(m), m_bv(m), m_refs(m) {}

    virtual void minimize_model(ptr_vector<expr> const & formulas, model_ref& mdl, expr_ref_vector& model);

    /**
       \brief extract literals from formulas that satisfy formulas.

       \pre model satisfies formulas
    */
    expr_ref_vector minimize_literals(ptr_vector<expr> const & formulas, model_ref& mdl);

    // for_each_expr visitor.
    void operator()(expr* e) {} 
};

void get_value_from_model(const model_core & mdl, func_decl * f, expr_ref& res);

}

#endif
