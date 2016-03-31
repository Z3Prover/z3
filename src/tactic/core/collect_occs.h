/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    collect_cccs.h

Abstract:

    Collect variables by occurrences.

Author:

    Leonardo (leonardo) 2011-10-22

Notes:

--*/
#ifndef COLLECT_OCCS_H_
#define COLLECT_OCCS_H_

class collect_occs {
    expr_fast_mark1  m_visited;
    expr_fast_mark2  m_more_than_once;
    typedef std::pair<expr *, unsigned> frame;
    svector<frame>   m_stack;
    ptr_vector<app>  m_vars;
    
    bool visit(expr * t);
    void process(expr * t);
    
public:
    
    void operator()(goal const & g, obj_hashtable<expr> & r);

};

#endif
