/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    func_interp.h

Abstract:

    Support for function graphs (aka interpretations for functions).
    They are used during model construction, and for evaluating expressions
    modulo a model.

    Main goal: Remove some code duplication and make the evaluator more efficient.

    Example of code duplication that existed in Z3:
      - smt_model_generator was creating func_values that were essentially partial func_interps
      - smt_model_generator was creating if-then-else (lambda) exprs representing func_values
      - the model object was converting these lambdas back into func_graphs (a limited version of func_interps).
      - the smt_model_finder needs to manipulate func_interps, but the func_values in smt_model_generator
        were private and too restrictive.

Author:

    Leonardo de Moura (leonardo) 2010-12-30.

Revision History:

--*/
#pragma once

#include "ast/ast.h"
#include "ast/ast_translation.h"

class func_interp;

class func_entry {
    bool   m_args_are_values; //!< true if is_value(m_args[i]) is true for all i in [0, arity)

    // m_result and m_args[i] must be ground terms.

    expr * m_result;
    expr * m_args[];

    static unsigned get_obj_size(unsigned arity) { return sizeof(func_entry) + arity * sizeof(expr*); }
    func_entry(ast_manager & m, unsigned arity, expr * const * args, expr * result);

    friend class func_interp;

    void set_result(ast_manager & m, expr * r);

public:
    static func_entry * mk(ast_manager & m, unsigned arity, expr * const * args, expr * result);
    bool args_are_values() const { return m_args_are_values; }
    void deallocate(ast_manager & m, unsigned arity);
    expr * get_result() const { return m_result; }
    expr * get_arg(unsigned idx) const { return m_args[idx]; }
    expr * const * get_args() const { return m_args; }
    
    /**
       \brief Return true if m.are_equal(m_args[i], args[i]) for all i in [0, arity)
    */
    bool eq_args(ast_manager & m, unsigned arity, expr * const * args) const;
};

struct func_entry_eq {
    unsigned m_arity;
    func_entry_eq(unsigned arity) : m_arity(arity) {}
    bool operator()(func_entry* a, func_entry* b) const {
        for (unsigned i = 0; i < m_arity; ++i)
            if (a->get_arg(i) != b->get_arg(i))
                return false;        
        return true;
    }
};

struct func_entry_hash {
    unsigned m_arity;
    struct chasher {
        unsigned operator()(func_entry* e, unsigned idx) const {
            return e->get_arg(idx)->get_id();
        }
    };
    func_entry_hash(unsigned arity) : m_arity(arity) {}
    unsigned operator()(func_entry* e) const {
        return get_composite_hash(e, m_arity, default_kind_hash_proc<func_entry*>(), chasher());
    }
};

class func_interp {
    ast_manager &          m_manager;
    unsigned               m_arity;
    ptr_vector<func_entry> m_entries;
    expr *                 m_else;
    bool                   m_args_are_values; //!< true if forall e in m_entries e.args_are_values() == true

    expr *                 m_interp; //!< cache for representing the whole interpretation as a single expression (it uses ite terms).

    expr *                 m_array_interp; // <! interp with lambda abstraction

    using entry_table = ptr_hashtable<func_entry, func_entry_hash, func_entry_eq>;
    entry_table* m_entry_table = nullptr;
    func_entry* m_key = nullptr;

    void reset_interp_cache();

    expr * get_interp_core() const;

    expr_ref get_array_interp_core(func_decl * f) const;

public:
    func_interp(ast_manager & m, unsigned arity);
    ~func_interp();

    ast_manager & m () const { return m_manager; }

    func_interp * copy() const;

    unsigned get_arity() const { return m_arity; }

    bool is_partial() const { return m_else == nullptr; }
    // A function interpretation is said to be simple if m_else is ground.
    bool is_simple() const { return is_partial() || is_ground(m_else); }
    bool is_constant() const;
    // Return true if all arguments of the function graph are values.
    bool args_are_values() const { return m_args_are_values; }

    expr * get_else() const { return m_else; }
    void set_else(expr * e);

    void insert_entry(expr * const * args, expr * r);
    void insert_new_entry(expr * const * args, expr * r);
    func_entry * get_entry(expr * const * args) const;
    bool eval_else(expr * const * args, expr_ref & result) const;
    unsigned num_entries() const { return m_entries.size(); }
    ptr_vector<func_entry>::const_iterator begin() const { return m_entries.begin(); }
    ptr_vector<func_entry>::const_iterator end() const { return m_entries.end(); }
    func_entry const * const * get_entries() const { return m_entries.data(); }
    func_entry const * get_entry(unsigned idx) const { return m_entries[idx]; }
    void del_entry(unsigned idx);

    expr * get_max_occ_result() const;
    void compress();

    expr * get_interp() const;

    expr_ref get_array_interp(func_decl* f) const;

    func_interp * translate(ast_translation & translator) const;

private:
    bool is_fi_entry_expr(expr * e, ptr_vector<expr> & args);
    bool is_identity() const;
};

