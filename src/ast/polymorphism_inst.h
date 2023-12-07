/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    polymorphism_inst.h

Abstract:

    Utilities for instantiating polymorphic assertions.

Author:

    Nikolaj Bjorner (nbjorner) 2023-7-8


--*/
#pragma once

#include "util/trail.h"
#include "ast/ast.h"
#include "ast/polymorphism_util.h"

namespace polymorphism {
    
    struct instantiation {
        expr* orig;
        expr_ref inst;
        substitution* sub;
        instantiation(expr* orig, expr_ref& inst, substitution* s):
            orig(orig), inst(inst), sub(s) {}
    };
    
    class inst {
        ast_manager& m;
        trail_stack& t;
        util u;
        
        struct instances {
            ptr_vector<sort>               m_tvs;
            ptr_vector<func_decl>          m_poly_fns;
            substitutions*                 m_subst = nullptr;
        };
        
        func_decl_ref_vector m_poly_roots;
        obj_map<func_decl, ptr_vector<expr>> m_occurs;
        obj_map<expr, instances>      m_instances;
        func_decl_ref_vector          m_decl_queue;
        unsigned                      m_decl_qhead = 0;
        ast_mark                      m_in_decl_queue;
        expr_ref_vector               m_assertions;
        unsigned                      m_assertions_qhead = 0;
        obj_hashtable<expr>           m_from_instantiation;
                
        struct add_decl_queue : public trail {
            inst& i;
            add_decl_queue(inst& i): i(i) {}
            void undo() override {
                i.m_in_decl_queue.mark(i.m_decl_queue.back(), false);
                i.m_decl_queue.pop_back();
            };
        };

        struct remove_back : public trail {
            obj_map<func_decl, ptr_vector<expr>>& occ;
            func_decl* f;
            remove_back(obj_map<func_decl, ptr_vector<expr>>& occ, func_decl* f):
                occ(occ), f(f) {}
            void undo() override {
                occ.find(f).pop_back();
            }
        };

        void instantiate(func_decl* p, expr* e, vector<instantiation>& instances);

        void collect_instantiations(expr* e);

        void add_instantiations(expr* e, ptr_vector<func_decl> const& insts);

    public:
        inst(ast_manager& m, trail_stack& t):
            m(m), t(t), u(m), m_poly_roots(m), m_decl_queue(m), m_assertions(m) {}
        
        void add(expr* e);
        
        void instantiate(vector<instantiation>& instances);

        bool pending() const { return m_decl_qhead < m_decl_queue.size() || m_assertions_qhead < m_assertions.size(); }
        
    };
}
