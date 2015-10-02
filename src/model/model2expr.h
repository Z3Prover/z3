/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    model2expr.h

Abstract:

    Convert model to logical formula that forces it.

Author:

    Nikolaj Bjorner (nbjorner) 2012-09-17

Revision History:

--*/
#ifndef MODEL2EXPR_H_
#define MODEL2EXPR_H_

#include"model.h"

void model2expr(model& m, expr_ref& result);

inline void model2expr(model_ref& md, expr_ref& result) { model2expr(*md.get(), result); }

// TODO: move
typedef hashtable<symbol, symbol_hash_proc, symbol_eq_proc> symbol_set;

class mk_fresh_name {
    symbol_set m_symbols;
    char       m_char;
    unsigned   m_num;
public:
    mk_fresh_name(): m_char('A'), m_num(0) {}
    void add(ast* a);
    void add(symbol const& s) { m_symbols.insert(s); }
    symbol next();
    bool contains(symbol const& s) const { return m_symbols.contains(s); }
};


#endif /* MODEL2EXPR_H_ */

