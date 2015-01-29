/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ast_trail.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-02.

Revision History:

    Extracted AST specific features from trail.h
    nbjorner 2014-9-28

--*/
#ifndef _AST_TRAIL_H_
#define _AST_TRAIL_H_

#include"ast.h"
#include"trail.h"


template<typename S, typename T>
class ast2ast_trailmap {
    ref_vector<S, ast_manager> m_domain;
    ref_vector<T, ast_manager> m_range;
    obj_map<S, T*>             m_map;
public:
    ast2ast_trailmap(ast_manager& m):
        m_domain(m),
        m_range(m), 
        m_map()
    {}

    bool find(S* s, T*& t) {
        return m_map.find(s,t);
    }
    
    void insert(S* s, T* t) {
        SASSERT(!m_map.contains(s));
        m_domain.push_back(s);
        m_range.push_back(t);
        m_map.insert(s,t);
    }
    
    void pop() {
        SASSERT(!m_domain.empty());
        m_map.remove(m_domain.back());
        m_domain.pop_back();
        m_range.pop_back();
    }
};

template<typename Ctx, typename S, typename T>
class ast2ast_trail : public trail<Ctx> {
    ast2ast_trailmap<S,T>& m_map;
public:
    ast2ast_trail(ast2ast_trailmap<S,T>& m, S* s, T* t) : 
        m_map(m) {
        m.insert(s,t);
    }

    virtual void undo(Ctx& ctx) {
        m_map.pop();
    }    
};


#endif /* _AST_TRAIL_H_ */

