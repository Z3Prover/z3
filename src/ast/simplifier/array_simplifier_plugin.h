/*++
Copyright (c) 2008 Microsoft Corporation

Module Name:

    array_simplifier_plugin.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2008-05-05

Revision History:

--*/
#ifndef _ARRAY_SIMPLIFIER_PLUGIN_H_
#define _ARRAY_SIMPLIFIER_PLUGIN_H_

#include"ast.h"
#include"map.h"
#include"array_decl_plugin.h"
#include"simplifier_plugin.h"
#include"basic_simplifier_plugin.h"
#include"array_simplifier_params.h"
#include"simplifier.h"
#include"obj_hashtable.h"
#include"lbool.h"

class array_simplifier_plugin : public simplifier_plugin {

    typedef ptr_vector<expr> entry;

    struct entry_hash_proc { 
        unsigned operator()(ptr_vector<expr> * entry) const {
            return get_exprs_hash(entry->size(), entry->begin(), 0xbeef1010);
        }
    };

    struct entry_eq_proc {
        bool operator()(ptr_vector<expr> * entry1, ptr_vector<expr> * entry2) const {
            if (entry1->size() != entry2->size()) return false;
            return compare_arrays(entry1->begin(), entry2->begin(), entry1->size());
        }
    };

    typedef map<entry *, expr *, entry_hash_proc, entry_eq_proc> select_cache;

    struct args_entry {
        unsigned     m_arity;
        expr* const* m_args;
        args_entry(unsigned a, expr* const* args) : m_arity(a), m_args(args) {}
        args_entry() : m_arity(0), m_args(0) {}
    };

    struct args_entry_hash_proc {
        unsigned operator()(args_entry const& e) const {
            return get_exprs_hash(e.m_arity, e.m_args, 0xbeef1010);
        }
    };
    struct args_entry_eq_proc {
        bool operator()(args_entry const& e1, args_entry const& e2) const {
            if (e1.m_arity != e2.m_arity) return false;
            return compare_arrays(e1.m_args, e2.m_args, e1.m_arity);
        }
    };
    typedef hashtable<args_entry, args_entry_hash_proc, args_entry_eq_proc> arg_table;

    array_util         m_util;
    basic_simplifier_plugin& m_simp;
    simplifier&              m_simplifier;
    array_simplifier_params const&     m_params;
    select_cache       m_select_cache;
    ptr_vector<expr>   m_tmp;
    ptr_vector<expr>   m_tmp2;
    ptr_vector<expr>   m_todo;
    static const unsigned m_select_cache_max_size = 100000; 
    typedef obj_map<expr, expr*> const_map;
    class store_info {
        store_info();
        store_info(store_info const&);
    public:
        const_map         m_map;
        expr_ref          m_default;
        store_info(ast_manager& m, expr* d): m_default(d, m) {}
    };

    typedef obj_map<expr, store_info*> store_cache;
    store_cache          m_store_cache;
    unsigned             m_store_cache_size;
    static const unsigned m_store_cache_max_size = 10000; 
    static const unsigned m_const_store_threshold = 5;
    enum const_select_result {
        NOT_CACHED,
        FOUND_DEFAULT,
        FOUND_VALUE        
    };


public:
    array_simplifier_plugin(ast_manager & m, basic_simplifier_plugin& s, simplifier& simp, array_simplifier_params const& p);
    virtual ~array_simplifier_plugin();

    virtual bool reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);

    virtual bool reduce_eq(expr * lhs, expr * rhs, expr_ref & result);
    
    virtual bool reduce_distinct(unsigned num_args, expr * const * args, expr_ref & result);    
   
    virtual void flush_caches();

private:
    bool is_select(expr* n) const { return m_util.is_select(n); }
    bool is_store(expr * n) const { return m_util.is_store(n); }
    bool is_const_array(expr * n) const { return m_util.is_const(n); }
    bool is_as_array(expr * n) const { return m_util.is_as_array(n); }
    bool is_as_array_tree(expr * n) { return m_util.is_as_array_tree(n); }
    func_decl * get_as_array_func_decl(app * n) const { return m_util.get_as_array_func_decl(n); }
    void mk_select_as_array(unsigned num_args, expr * const * args, expr_ref & result);
    void mk_select_as_array_tree(unsigned num_args, expr * const * args, expr_ref & result);
    bool is_enumerated(expr* n, expr_ref& c, ptr_vector<expr>& keys, ptr_vector<expr>& vals);
    const_select_result mk_select_const(expr* m, app* index, expr_ref& result);
    void cache_store(unsigned num_stores, expr* nested_store);
    void cache_select(unsigned num_args, expr * const * args, expr * result);
    void prune_select_cache();
    void prune_store_cache();
    void flush_select_cache();
    void flush_store_cache();    
    void mk_set_difference(unsigned num_args, expr * const * args, expr_ref & result);
    void mk_empty_set(sort* ty, expr_ref & result);
    void mk_full_set(sort* ty, expr_ref & result);
    void mk_select(unsigned num_args, expr * const * args, expr_ref & result);
    void mk_store(func_decl* f, unsigned num_args, expr * const * args, expr_ref & result);
    void mk_map(func_decl* f, expr* a, expr* b, expr_ref & result);
    void mk_map(func_decl* f, expr* a, expr_ref & result);
    bool same_args(unsigned num_args, expr * const * args1, expr * const * args2);

    void get_stores(expr* n, unsigned& arity, expr*& m, ptr_vector<expr*const>& stores);
    lbool eq_default(expr* def, unsigned arity, unsigned num_st, expr*const* const* st);
    bool insert_table(expr* def, unsigned arity, unsigned num_st, expr*const* const* st, arg_table& table);
    lbool eq_stores(expr* def, unsigned arity, unsigned num_st1, expr*const* const* st1, unsigned num_st2, expr*const* const* st2);

    bool same_store(unsigned num_args, expr* const* args) const;    
    bool all_const_array(unsigned num_args, expr* const* args) const;    
    bool all_values(unsigned num_args, expr* const* args) const;
    bool lex_lt(unsigned num_args, expr* const* args1, expr* const* args2);

};


#endif /* _ARRAY_SIMPLIFIER_PLUGIN_H_ */

