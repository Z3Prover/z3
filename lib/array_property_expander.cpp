/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    array_property_expander.cpp

Abstract:

    Expand array operations for the array property fragment formulas.

Author:

    Nikolaj Bjorner (nbjorner) 2010-16-12

Revision History:

--*/

#include"array_property_expander.h"
#include"obj_hashtable.h"
#include"var_subst.h"
#include"array_decl_plugin.h"
#include"for_each_expr.h"

array_property_expander::array_property_expander(ast_manager& m):
    m_manager(m) {
}

namespace array_property_exp {
    class proc {
        ast_manager& m_manager;
        unsigned&    m_offset;
        expr_ref_vector m_trail;
        family_id    m_fid;
        array_util   m_util;
        obj_map<expr, expr*> m_mem;


        void insert(expr* a, expr* b) {
            m_trail.push_back(b);
            m_mem.insert(a, b);
        }


    public:
        proc(ast_manager& m, unsigned& offset) : 
            m_manager(m),
            m_offset(offset),
            m_trail(m),
            m_fid(m.get_family_id("array")),
            m_util(m)
        {}

        expr* find(expr* e) {
            expr* result = 0;
            VERIFY(m_mem.find(e, result));
            return result;
        }

        void operator()(var* n) { insert(n, n); }

        void operator()(quantifier* q) {
            expr* e = find(q->get_expr());
            quantifier* q2 = m_manager.update_quantifier(q, e);
            insert(q, q2);
        }

        void operator()(app* n) {
            ast_manager& m = m_manager;
            unsigned num_args = n->get_num_args();
            ptr_buffer<expr> args;
            for (unsigned i = 0; i < num_args; ++i) {
                args.push_back(find(n->get_arg(i)));
            }
            if (m_manager.is_eq(n) && m_util.is_array(args[0])) {
                visit_eq(n);
                return;
            }
            if (m_manager.is_distinct(n) && num_args > 0 && m_util.is_array(args[0])) {
                ptr_buffer<expr> eqs;
                for (unsigned i = 0; i < num_args; ++i) {
                    for (unsigned j = i + 1; j < num_args; ++j) {
                        eqs.push_back(m.mk_not(m.mk_eq(args[i], args[j])));
                    }
                }
                insert(n, m.mk_and(eqs.size(), eqs.c_ptr()));               
                return;
            }

            if (m_util.is_select(n)) {
                SASSERT(num_args > 0);

                // select(store(A,i,v),j) -> ite(i = j, v, select(A,j))
                if (m_util.is_store(args[0])) {
                    app* a = to_app(args[0]);
                    expr* b = find(a->get_arg(0));
                    expr* v = find(a->get_arg(a->get_num_args()-1));
                    ptr_buffer<expr> eqs;
                    SASSERT(num_args + 1 == a->get_num_args());
                    for (unsigned i = 1; i < num_args; ++i) {
                        eqs.push_back(m.mk_eq(args[i], find(a->get_arg(i))));
                    }
                    expr* r = m.mk_ite(m.mk_and(eqs.size(), eqs.c_ptr()), v, mk_select(b, num_args-1, args.c_ptr()+1));
                    insert(n, r);
                    return;
                }

                // select(ite(a,b,c),i) -> ite(a, select(b,i), select(c, i))
                if (m.is_ite(args[0])) {
                    app* k = to_app(args[0]);
                    expr* a = k->get_arg(0);
                    expr* b = mk_select(k->get_arg(1), args.size()-1, args.c_ptr()+1);
                    expr* c = mk_select(k->get_arg(2), args.size()-1, args.c_ptr()+1);
                    expr* r = m.mk_ite(a, b, c);
                    insert(n, r);
                    return;
                }

                // select(map_f(A,B),i) -> f(select(A,i), select(B,i))
                if (m_util.is_map(args[0])) {
                    app* a = to_app(args[0]);
                    func_decl* f = a->get_decl(); 
                    SASSERT(f->get_num_parameters() == 1);
                    SASSERT(f->get_parameter(0).is_ast());
                    SASSERT(is_func_decl(f->get_parameter(0).get_ast()));                    
                    parameter p = f->get_parameter(0);
                    func_decl* d = to_func_decl(p.get_ast());
                    ptr_buffer<expr> args2;
                    for (unsigned i = 0; i < a->get_num_args(); ++i) {
                        args2.push_back(mk_select(find(a->get_arg(i)), args.size()-1, args.c_ptr()+1));
                    }
                    expr* r = m.mk_app(d, args2.size(), args2.c_ptr()); 
                    insert(n, r);
                    return;                    
                }

                // select(const v, i) -> v
                if (m_util.is_const(args[0])) {
                    insert(n, to_app(args[0])->get_arg(0));
                    return;
                }
            }       
            expr* r = m_manager.mk_app(n->get_decl(), args.size(), args.c_ptr());
            insert(n, r);
        }
        
    private:
        void visit_eq(app* eq) {
            ast_manager& m = m_manager;
            SASSERT(m.is_eq(eq));
            sort* s = m.get_sort(eq->get_arg(0));
            SASSERT(is_sort_of(s, m_fid, ARRAY_SORT));
            // sort* rng = get_array_range(s);
            unsigned arity = get_array_arity(s);
            shift_vars sh(m);
            expr_ref e1(m), e2(m);
            sh(find(eq->get_arg(0)), arity, e1);
            sh(find(eq->get_arg(1)), arity, e2);
            expr_ref_vector args(m);
            buffer<symbol> names;
            ptr_buffer<sort>   sorts;
            args.push_back(e1);
            for (unsigned i = 0; i < arity; ++i) {
                args.push_back(m.mk_var(i, get_array_domain(s, i)));
                sorts.push_back(get_array_domain(s, arity - i - 1));
                names.push_back(symbol(m_offset++));
            }
            e1 = mk_select(args.size(), args.c_ptr());
            args[0] = e2;
            e2 = mk_select(args.size(), args.c_ptr());
            e1 = m.mk_eq(e1, e2);
            
            e1 = m.mk_quantifier(true, arity, sorts.c_ptr(), names.c_ptr(), e1, 1);
            insert(eq, e1);
        }

        app* mk_select(unsigned n, expr* const* args) {
            return m_manager.mk_app(m_fid, OP_SELECT, 0, 0, n, args);
        }
        
        app* mk_select(expr* a, unsigned n, expr* const* args) {
            ptr_buffer<expr> args2;
            args2.push_back(a);
            args2.append(n, args);
            return mk_select(n+1, args2.c_ptr());
        }
    };
};

void array_property_expander::operator()(unsigned num_fmls, expr* const* fmls, expr_ref_vector& result) {
    ast_manager& m = m_manager;
    unsigned offset = 0;
    for (unsigned i = 0; i < num_fmls; ++i) {
        bool change = false;
        expr_ref e(m);
        result.push_back(fmls[i]);
        do {
            array_property_exp::proc p(m, offset);
            e = result[i].get();
            for_each_expr(p, e);
            result[i] = p.find(e);
            change = e != result[i].get();
        }
        while (change);        
    }
}

