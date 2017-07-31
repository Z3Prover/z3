/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    for_each_ast.h

Abstract:

    Visitor for AST nodes

Author:

    Leonardo de Moura (leonardo) 2006-10-18.

Revision History:

--*/
#ifndef FOR_EACH_AST_H_
#define FOR_EACH_AST_H_

#include "ast/ast.h"
#include "util/trace.h"
#include "util/map.h"

template<typename T>
bool for_each_ast_args(ptr_vector<ast> & stack, ast_mark & visited, unsigned num_args, T * const * args) {
    bool result = true;
    for (unsigned i = 0; i < num_args; i++) {
        T * arg = args[i];
        if (!visited.is_marked(arg)) {
            stack.push_back(arg);
            result = false;
        }
    }
    return result;
}

bool for_each_parameter(ptr_vector<ast> & stack, ast_mark & visited, unsigned num_args, parameter const * params);

template<typename ForEachProc>
void for_each_ast(ForEachProc & proc, ast_mark & visited, ast * n, bool visit_parameters = false) {
    ptr_vector<ast> stack;
    ast *           curr;

    stack.push_back(n);

    while (!stack.empty()) {
        curr = stack.back();
        TRACE("for_each_ast", tout << "visiting node: " << curr->get_id() << ", kind: " << get_ast_kind_name(curr->get_kind())
              << ", stack size: " << stack.size() << "\n";);

        if (visited.is_marked(curr)) {
            stack.pop_back();
            continue;
        }

        switch(curr->get_kind()) {
        case AST_SORT:
            if (visit_parameters && 
                !for_each_parameter(stack, visited, to_sort(curr)->get_num_parameters(), to_sort(curr)->get_parameters())) {
                break;
            }
            proc(to_sort(curr));
            visited.mark(curr, true);
            stack.pop_back();
            break;

        case AST_VAR: {
            var* v = to_var(curr);
            proc(v);
            visited.mark(curr, true);
            stack.pop_back();
            break;
        }

        case AST_FUNC_DECL:
            if (visit_parameters && 
                !for_each_parameter(stack, visited, to_func_decl(curr)->get_num_parameters(), to_func_decl(curr)->get_parameters())) {
                break;
            }
            if (!for_each_ast_args(stack, 
                                   visited, 
                                   to_func_decl(curr)->get_arity(), 
                                   to_func_decl(curr)->get_domain())) {
                break;
            }
            if (!visited.is_marked(to_func_decl(curr)->get_range())) {
                stack.push_back(to_func_decl(curr)->get_range());
                break;
            }
            proc(to_func_decl(curr));
            visited.mark(curr, true);
            stack.pop_back();
            break;
            
        case AST_APP:
            if (!visited.is_marked(to_app(curr)->get_decl())) {
                stack.push_back(to_app(curr)->get_decl());
                break;
            }
            if (for_each_ast_args(stack, visited, to_app(curr)->get_num_args(), to_app(curr)->get_args())) {
                proc(to_app(curr));
                visited.mark(curr, true);
                stack.pop_back();
            }
            break;
            
        case AST_QUANTIFIER:
            if (!for_each_ast_args(stack, visited, to_quantifier(curr)->get_num_patterns(), 
                                   to_quantifier(curr)->get_patterns())) {
                break;
            }
            if (!for_each_ast_args(stack, visited, to_quantifier(curr)->get_num_no_patterns(), 
                                    to_quantifier(curr)->get_no_patterns())) {
                break;
            }
            if (!visited.is_marked(to_quantifier(curr)->get_expr())) {
                stack.push_back(to_quantifier(curr)->get_expr());
                break;
            }
            proc(to_quantifier(curr));
            visited.mark(curr, true);
            stack.pop_back();
            break;
        }
    }
}

template<typename ForEachProc>
void for_each_ast(ForEachProc & proc, ast * n, bool visit_parameters = false) {
    ast_mark visited;
    for_each_ast(proc, visited, n, visit_parameters);
}

template<typename EscapeProc>
struct for_each_ast_proc : public EscapeProc {
    void operator()(ast * n) { EscapeProc::operator()(n); }
    void operator()(sort * n) { operator()(static_cast<ast *>(n)); }
    void operator()(func_decl * n) { operator()(static_cast<ast *>(n)); }
    void operator()(var * n) { operator()(static_cast<ast *>(n)); }
    void operator()(app * n) { operator()(static_cast<ast *>(n)); }
    void operator()(quantifier * n) { operator()(static_cast<ast *>(n)); }
};                     

unsigned get_num_nodes(ast * n);

template<class Visitor, class T, bool recurse_quantifier = true>
class recurse_ast {
    template<class T2>
    class mem_map : public map<ast*, T2*, obj_hash<ast>, ptr_eq<ast> > {};
    
public:
    static T* recurse(Visitor & visit, ast * aArg) {
        unsigned           arity;
        ast*               a;
        ast * const *      args;
        T*                 result;
        ptr_vector<ast>    stack;
        mem_map<T>         memoize;
        ptr_vector<T>      results;
        
        stack.push_back(aArg);
        
        while (!stack.empty()) {
            a = stack.back();                       
            
            results.reset();

            if (memoize.find(a, result)) {
                stack.pop_back();
                continue;
            }
            
            switch(a->get_kind()) {
                
            case AST_SORT:
                memoize.insert(a, visit.mk_sort(to_sort(a)));
                stack.pop_back();
                break;
                
            case AST_FUNC_DECL: {
                arity = to_func_decl(a)->get_arity();
                func_decl * func_decl_ast = to_func_decl(a);                
                args = (ast * const *)(func_decl_ast->get_domain());
                recurse_list(stack, arity, args, &memoize, results);
                if (!memoize.find(func_decl_ast->get_range(), result)) {
                    stack.push_back(func_decl_ast->get_range());
                }
                else if (results.size() == arity) {
                    result = visit.mk_func_decl(func_decl_ast, result, results);
                    memoize.insert(a, result);
                    stack.pop_back();
                }
                break;
            }

            case AST_APP: {
                app * app = to_app(a);     
                arity = app->get_num_args();
                args = (ast * const *)(app->get_args());           
                recurse_list(stack, arity, args, &memoize, results); 
                if (arity == results.size()) {
                    result = visit.mk_app(app, results);
                    memoize.insert(a, result);
                    stack.pop_back();
                }                
                break;
            }
                
            case AST_VAR:
                memoize.insert(a, visit.mk_var(to_var(a)));
                stack.pop_back();
                break;
                
            case AST_QUANTIFIER: {
                quantifier * quantifier_ast = to_quantifier(a);
                ptr_vector<T> decl_types;

                if (recurse_quantifier) {
                    args = (ast * const *) quantifier_ast->get_decl_sorts();
                    arity = quantifier_ast->get_num_decls();
                    ast* body = quantifier_ast->get_expr();
                    
                    recurse_list(stack, arity, args, &memoize, decl_types);
                    
                    if (!memoize.find(body, result)) {
                        stack.push_back(body);
                    }
                    else if (decl_types.size() == arity) {
                        result = visit.mk_quantifier(quantifier_ast, decl_types, result);
                        memoize.insert(a, result);
                        stack.pop_back();
                    }
                }
                else {
                    result = visit.mk_quantifier(quantifier_ast, decl_types, result);
                    memoize.insert(a, result);
                    stack.pop_back();
                }
                break;
            }
                
            default:
                UNREACHABLE();
                break;
            }
        }        
        
        if (!memoize.find(aArg, result)) {
            UNREACHABLE();
        }
        return result;
    }

private:

    template<typename AST>
    static void recurse_list(ptr_vector<ast> & stack, unsigned arity, AST * const * ast_list, mem_map<T> * memoize,
                             ptr_vector<T> & results) {
        T * result;
        for (unsigned i = 0; i < arity; ++i) {
            if (memoize->find(ast_list[i], result)) {
                results.push_back(result);
            }
            else {
                stack.push_back(ast_list[i]);
            }
        }
    }        
};

#endif /* FOR_EACH_AST_H_ */

