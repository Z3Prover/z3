/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sat_smt.h

Abstract:

    Header for SMT theories over SAT solver

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/
#pragma once
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "sat/sat_solver.h"

namespace sat {
    
    struct eframe {
        expr* m_e;
        unsigned m_idx;
        eframe(expr* e) : m_e(e), m_idx(0) {}
    };

    class sat_internalizer {
    public:
        virtual ~sat_internalizer() {}
        virtual bool is_bool_op(expr* e) const = 0;
        virtual literal internalize(expr* e, bool learned) = 0;
        virtual bool_var to_bool_var(expr* e) = 0;
        virtual bool_var add_bool_var(expr* e)  = 0;
        virtual void cache(app* t, literal l) = 0;
        virtual void uncache(literal l) = 0;
        virtual void push() = 0;
        virtual void pop(unsigned n) = 0;
        virtual void set_expr2var_replay(obj_map<expr, sat::bool_var>* r) = 0;
    };
    
    class constraint_base {
        extension* m_ex;
        unsigned   m_mem[0];
        static size_t ext_size() {
            return sizeof(((constraint_base*)nullptr)->m_ex);
        }

    public:
        constraint_base(): m_ex(nullptr) {}
        void*  mem() { return m_mem; }

        static size_t obj_size(size_t sz) { 
            return ext_size() + sz; 
        }

        static extension* to_extension(size_t s) { 
            return from_index(s)->m_ex; 
        }

        static constraint_base* from_index(size_t s) {
            return reinterpret_cast<constraint_base*>(s);
        }

        size_t to_index() const { 
            return reinterpret_cast<size_t>(this); 
        }

        static constraint_base const* mem2base_ptr(void const* mem) {
            return reinterpret_cast<constraint_base const*>((unsigned char const*)(mem) - ext_size());
        }

        static constraint_base* mem2base_ptr(void* mem) {
            return reinterpret_cast<constraint_base*>((unsigned char*)(mem) - ext_size());
        }

        static size_t mem2base(void const* mem) { 
            return reinterpret_cast<size_t>(mem2base_ptr(mem));
        }

        static void initialize(void* ptr, extension* ext) {
            reinterpret_cast<constraint_base*>(ptr)->m_ex = ext;
        }

        static void* ptr2mem(void* ptr) {
            return reinterpret_cast<void*>(((unsigned char*) ptr) + ext_size());
        }   

        static void* idx2mem(size_t idx) {
            return ptr2mem(from_index(idx));
        }
            
    };
}
