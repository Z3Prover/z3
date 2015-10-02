/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    used_symbols.h

Abstract:

    Collect the symbols used in an expression.

Author:

    Leonardo de Moura (leonardo) 2011-01-11.

Revision History:

--*/
#ifndef USED_SYMBOLS_H_
#define USED_SYMBOLS_H_

#include"ast.h"
#include"hashtable.h"
#include"obj_hashtable.h"

struct do_nothing_rename_proc {
    symbol operator()(symbol const & s) const { return s; }
};

/**
   \brief Functor for collecting the symbols used in an expression.
*/
template<typename RENAME_PROC=do_nothing_rename_proc>
class used_symbols : public RENAME_PROC { 
    typedef hashtable<symbol, symbol_hash_proc, symbol_eq_proc> symbol_set;

    symbol_set          m_used;
    obj_hashtable<expr> m_visited;
    ptr_vector<expr>    m_todo;

    void found(symbol const & s) { m_used.insert(RENAME_PROC::operator()(s)); }

    void visit(expr * n) {
        if (!m_visited.contains(n)) {
            m_visited.insert(n);
            m_todo.push_back(n);
        }
    }

public:
    used_symbols(RENAME_PROC const & p = RENAME_PROC()):
        RENAME_PROC(p) {
    }
    
    void operator()(expr * n, bool ignore_quantifiers = false) {
        m_visited.reset();
        m_used.reset();
        m_todo.reset();
        visit(n);
        while (!m_todo.empty()) {
            n = m_todo.back();
            m_todo.pop_back();
            unsigned j;
            switch (n->get_kind()) {
            case AST_APP:
                found(to_app(n)->get_decl()->get_name());
                j = to_app(n)->get_num_args();
                while (j > 0) {
                    --j;
                    visit(to_app(n)->get_arg(j));
                }
                break;
            case AST_QUANTIFIER:
                if (!ignore_quantifiers) {
                    found(to_quantifier(n)->get_qid());
                    unsigned num_decls = to_quantifier(n)->get_num_decls();
                    for (unsigned i = 0; i < num_decls; i++)
                        found(to_quantifier(n)->get_decl_name(i));
                    unsigned num_pats = to_quantifier(n)->get_num_patterns();
                    for (unsigned i = 0; i < num_pats; i++)
                        visit(to_quantifier(n)->get_pattern(i));
                    unsigned num_no_pats = to_quantifier(n)->get_num_no_patterns();
                    for (unsigned i = 0; i < num_no_pats; i++)
                        visit(to_quantifier(n)->get_no_pattern(i));
                    visit(to_quantifier(n)->get_expr());
                }
                break;
            default:
                break;
            }
        }
    }

    bool contains(symbol const & s) const { return m_used.contains(RENAME_PROC::operator()(s)); }

    bool contains_core(symbol const & s) const { return m_used.contains(s); }

    void insert(symbol const & s) { m_used.insert(RENAME_PROC::operator()(s)); }
    
    void insert_core(symbol const & s) { m_used.insert(s); }

    void erase_core(symbol const & s) { m_used.erase(s); }
};

#endif /* USED_SYMBOLS_H_ */
