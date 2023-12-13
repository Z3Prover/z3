/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    polymorphism_inst.cpp

Abstract:

    Utilities for instantiating polymorphic assertions.

Author:

    Nikolaj Bjorner (nbjorner) 2023-7-8


--*/
#include "ast/polymorphism_inst.h"
#include "ast/ast_pp.h"

namespace polymorphism {
    
    void inst::add(expr* e) {
        if (!m.has_type_vars())
            return;

        if (m_from_instantiation.contains(e))
            return;

        instances inst;
        u.collect_poly_instances(e, inst.m_poly_fns);
        if (inst.m_poly_fns.empty())
            return;
        if (m_instances.contains(e))
            return;
        
        add_instantiations(e, inst.m_poly_fns);

        if (!u.has_type_vars(e))
            return;
        
        // insert e into the occurs list for polymorphic roots
        ast_mark seen;
        for (auto* f : inst.m_poly_fns) {
            f = m.poly_root(f);
            if (seen.is_marked(f))
                continue;
            seen.mark(f, true);
            if (!m_occurs.contains(f)) {
                m_occurs.insert(f, ptr_vector<expr>());
                t.push(insert_map(m_occurs, f));
            }
            auto& es = m_occurs.find(f);
            es.push_back(e);
            t.push(remove_back(m_occurs, f));
        }
        m_assertions.push_back(e);
        t.push(push_back_vector(m_assertions));
        u.collect_type_vars(e, inst.m_tvs);
        inst.m_subst = alloc(substitutions);
        inst.m_subst->insert(alloc(substitution, m));
        m_instances.insert(e, inst);            
        t.push(new_obj_trail(inst.m_subst));
        t.push(insert_map(m_instances, e));        
    }

    void inst::collect_instantiations(expr* e) {
        ptr_vector<func_decl> instances;
        u.collect_poly_instances(e, instances);
        add_instantiations(e, instances);
    }

    void inst::add_instantiations(expr* e, ptr_vector<func_decl> const& instances) {
        for (auto* f : instances) {
            if (m_in_decl_queue.is_marked(f))
                continue;
            m_in_decl_queue.mark(f, true);
            m_decl_queue.push_back(f);
            t.push(add_decl_queue(*this));
        }
    }
    
    void inst::instantiate(vector<instantiation>& instances) {
        unsigned num_decls = m_decl_queue.size();
        if (m_assertions_qhead < m_assertions.size()) {
            t.push(value_trail(m_assertions_qhead));
            for (; m_assertions_qhead < m_assertions.size(); ++m_assertions_qhead) {
                expr* e = m_assertions.get(m_assertions_qhead);
                for (unsigned i = 0; i < num_decls; ++i)
                    instantiate(m_decl_queue.get(i), e, instances);
            }
        }       
        if (m_decl_qhead < num_decls) {
            t.push(value_trail(m_decl_qhead));
            for (; m_decl_qhead < num_decls; ++m_decl_qhead) {
                func_decl* p = m_decl_queue.get(m_decl_qhead);
                func_decl* r = m.poly_root(p);
                if (!m_occurs.contains(r))
                    continue;
                for (expr* e : m_occurs[r])
                    instantiate(p, e, instances);
            }
        }
    }

    void inst::instantiate(func_decl* f1, expr* e, vector<instantiation>& instances) {
        auto const& [tv, fns, substs] = m_instances[e];
                
        for (auto* f2 : fns) {
            substitution sub1(m), new_sub(m);
            if (!u.unify(f1, f2, sub1))
                continue;
            if (substs->contains(&sub1))
                continue;
            substitutions new_substs;
            for (auto* sub2 : *substs) {
                if (!u.unify(sub1, *sub2, new_sub))
                    continue;
                if (substs->contains(&new_sub))
                    continue;
                if (new_substs.contains(&new_sub))
                    continue;
                expr_ref e_inst = new_sub(e);
                if (!m_from_instantiation.contains(e_inst)) {
                    collect_instantiations(e_inst);
                    auto* new_sub1 = alloc(substitution, new_sub);
                    instances.push_back(instantiation(e, e_inst, new_sub1));
                    new_substs.insert(new_sub1);
                    m_from_instantiation.insert(e_inst);
                    m.inc_ref(e_inst);
                    t.push(insert_ref_map(m, m_from_instantiation, e_inst));
                }
            }
            for (auto* sub2 : new_substs) {
                SASSERT(!substs->contains(sub2));
                substs->insert(sub2);
                t.push(new_obj_trail(sub2));
                t.push(insert_map(*substs, sub2));
            }
        }        
    }
}
