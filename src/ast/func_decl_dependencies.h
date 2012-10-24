/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    func_decl_dependencies.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-12-15.

Revision History:

--*/
#ifndef _FUNC_DECL_DEPENDENCIES_H_
#define _FUNC_DECL_DEPENDENCIES_H_

#include"ast.h"
#include"obj_hashtable.h"

// Set of dependencies
typedef obj_hashtable<func_decl> func_decl_set;

/**
   \brief Collect uninterpreted function declarations (with arity > 0) occurring in \c n.
*/
void collect_func_decls(ast_manager & m, expr * n, func_decl_set & r, bool ng_only = false);

/**
   \brief Auxiliary data-structure used for tracking dependencies between function declarations.

   The following pattern of use is expected:
   
   func_decl_dependencies & dm;
   func_decl_set * S = dm.mk_func_decl_set();
   dm.collect_func_decls(t_1, S);
   ...
   dm.collect_func_decls(t_n, S);
   dm.insert(f, S);
*/
class func_decl_dependencies {
    typedef obj_map<func_decl, func_decl_set *> dependency_graph;
    ast_manager &     m_manager;
    dependency_graph  m_deps;

    class top_sort;

public:
    func_decl_dependencies(ast_manager & m):m_manager(m) {}
    ~func_decl_dependencies() {
        reset();
    }
    
    void reset();

    /**
       \brief Create a dependecy set.
       This set should be populated using #collect_func_decls.
       After populating the set, it must be used as an argument for the #insert method.

       \remark The manager owns the set.

       \warning Failure to call #insert will produce a memory leak.
    */
    func_decl_set * mk_func_decl_set() { return alloc(func_decl_set); }
    
    /**
       \brief Store the uninterpreted function declarations used in \c n into \c s.
    */
    void collect_func_decls(expr * n, func_decl_set * s);
    
    /**
       \brief Store the uninterpreted function declarations (in non ground terms) used in \c n into \c s.
    */
    void collect_ng_func_decls(expr * n, func_decl_set * s);

    /**
       \brief Insert \c f in the manager with the given set of dependencies.
       The insertion succeeds iff 
            1- no cycle is created between the new entry and
            the already existing dependencies. 
            2- \c f was not already inserted into the manager.
       
       Return false in case of failure. 

       \remark The manager is the owner of the dependency sets.
    */
    bool insert(func_decl * f, func_decl_set * s);

    /**
       \brief Return true if \c f is registered in this manager.
    */
    bool contains(func_decl * f) const { return m_deps.contains(f); }

    func_decl_set * get_dependencies(func_decl * f) const { func_decl_set * r = 0; m_deps.find(f, r); return r; }

    /**
       \brief Erase \c f (and its dependencies) from the manager.
    */
    void erase(func_decl * f);

    void display(std::ostream & out);
};


#endif
