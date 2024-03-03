/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    polymorphism_util.cpp

Abstract:

    Utilities for supporting polymorphic type signatures.

Author:

    Nikolaj Bjorner (nbjorner) 2023-7-8

--*/

#include "ast/polymorphism_util.h"
#include "ast/for_each_ast.h"
#include "ast/occurs.h"
#include "ast/ast_pp.h"

namespace polymorphism {

    sort_ref_vector substitution::operator()(sort_ref_vector const& s) {
        sort_ref_vector r(m);
        for (auto* srt : s)
            r.push_back((*this)(srt));
        return r;
    }
    
    sort_ref substitution::operator()(sort* s) {
        if (!m.has_type_var(s))
            return sort_ref(s, m);
        if (s->is_type_var()) {
            if (m_sub.find(s, s))
                return (*this)(s);
            return sort_ref(s, m);
        }
        unsigned n = s->get_num_parameters();
        vector<parameter> ps;
        for (unsigned i = 0; i < n; ++i) {
            auto &p = s->get_parameter(i);
            if (p.is_ast() && is_sort(p.get_ast())) {
                sort_ref s = (*this)(to_sort(p.get_ast()));
                ps.push_back(parameter(s.get()));
            }
            else
                ps.push_back(p);
        }
        sort_info si(s->get_family_id(), s->get_decl_kind(), n, ps.data(), s->private_parameters());
        return sort_ref(m.mk_sort(s->get_name(), si), m);
    }
    
    expr_ref substitution::operator()(expr* e) {
        ptr_vector<expr> todo;
        expr_ref_vector result(m);
        todo.push_back(e);
        auto in_cache = [&](expr* a) {
            return result.size() > a->get_id() && result.get(a->get_id());
        };
        ptr_buffer<expr> args;
        sort_ref_buffer domain(m);
        while (!todo.empty()) {
            expr* a = todo.back();
            if (in_cache(a)) {
                todo.pop_back();
                continue;
            }
            if (is_var(a)) {
                if (m.has_type_var(a->get_sort())) 
                    result.setx(a->get_id(), m.mk_var(to_var(a)->get_idx(), (*this)(a->get_sort())));                
                else
                    result.setx(a->get_id(), a);                
                todo.pop_back();
            }
            else if (is_quantifier(a)) {
                quantifier* q = to_quantifier(a);
                bool pending = false;
                if (!in_cache(q->get_expr())) {
                    todo.push_back(q->get_expr());
                    pending = true;
                }
                ptr_buffer<expr> patterns, no_patterns;
                unsigned np = q->get_num_patterns();
                for (unsigned i = 0; i < np; ++i) {
                    if (!in_cache(q->get_pattern(i))) {
                        todo.push_back(q->get_pattern(i));
                        pending = true;
                    }
                    else
                        patterns.push_back(result.get(q->get_pattern(i)->get_id()));
                }
                np = q->get_num_no_patterns();
                for (unsigned i = 0; i < np; ++i) {
                    if (!in_cache(q->get_no_pattern(i))) {
                        todo.push_back(q->get_no_pattern(i));
                        pending = true;
                    }
                    else
                        no_patterns.push_back(result.get(q->get_no_pattern(i)->get_id()));
                }
                if (pending)
                    continue;
                todo.pop_back();
                domain.reset();
                for (unsigned i = 0; i < q->get_num_decls(); ++i)
                    domain.push_back((*this)(q->get_decl_sort(i)));
                quantifier* q2 = 
                    m.mk_quantifier(q->get_kind(), q->get_num_decls(), domain.data(), q->get_decl_names(), result.get(q->get_expr()->get_id()),
                    q->get_weight(),
                    q->get_qid(), q->get_skid(), 
                    q->get_num_patterns(), patterns.data(), q->get_num_no_patterns(), no_patterns.data()
                    );
                result.setx(q->get_id(), q2);
            }
            else if (is_app(a)) {
                args.reset();
                unsigned n = todo.size();
                for (expr* arg : *to_app(a)) {
                    if (!in_cache(arg))
                        todo.push_back(arg);
                    else
                        args.push_back(result.get(arg->get_id()));
                }
                if (n < todo.size())
                    continue;
                func_decl* f = to_app(a)->get_decl();
                if (f->is_polymorphic()) {
                    domain.reset();
                    for (unsigned i = 0; i < f->get_arity(); ++i)
                        domain.push_back((*this)(f->get_domain(i)));
                    sort_ref range = (*this)(f->get_range());
                    f = m.instantiate_polymorphic(f, f->get_arity(), domain.data(), range);
                }
                result.setx(a->get_id(), m.mk_app(f, args));
                todo.pop_back();
            }
        }
        return expr_ref(result.get(e->get_id()), m);
    }
    
    bool substitution::unify(sort* s1, sort* s2) {
        if (s1 == s2)
            return true;
        if (s1->is_type_var() && m_sub.find(s1, s1))
            return unify(s1, s2);
        if (s2->is_type_var() && m_sub.find(s2, s2))
            return unify(s1, s2);
        if (s2->is_type_var() && !s1->is_type_var())
            std::swap(s1, s2);
        if (s1->is_type_var()) {
            auto s22 = (*this)(s2);
            if (occurs(s1, s22))
                return false;    
            m_trail.push_back(s22);
            m_trail.push_back(s1);
            m_sub.insert(s1, s22);
            return true;
        }
        if (s1->get_family_id() != s2->get_family_id())
            return false;
        if (s1->get_decl_kind() != s2->get_decl_kind())
            return false;
        if (s1->get_name() != s2->get_name())
            return false;
        if (s1->get_num_parameters() != s2->get_num_parameters())
            return false;
        for (unsigned i = s1->get_num_parameters(); i-- > 0;) {
            auto &p1 = s1->get_parameter(i);
            auto &p2 = s2->get_parameter(i);
            if (p1.is_ast() && is_sort(p1.get_ast())) {
                if (!p2.is_ast())
                    return false;
                if (!is_sort(p2.get_ast()))
                    return false;
                if (!unify(to_sort(p1.get_ast()), to_sort(p2.get_ast())))
                    return false;
                continue;
            }
            if (p1 != p2)
                return false;
        }
        return true;
    }    

    bool substitution::match(sort* s1, sort* s2) {
        if (s1 == s2)
            return true;
        if (s1->is_type_var() && m_sub.find(s1, s1))
            return match(s1, s2);
        if (s1->is_type_var()) {
            m_trail.push_back(s2);
            m_trail.push_back(s1);
            m_sub.insert(s1, s2);
            return true;
        }
        if (s1->get_family_id() != s2->get_family_id())
            return false;
        if (s1->get_decl_kind() != s2->get_decl_kind())
            return false;
        if (s1->get_name() != s2->get_name())
            return false;
        if (s1->get_num_parameters() != s2->get_num_parameters())
            return false;
        for (unsigned i = s1->get_num_parameters(); i-- > 0;) {
            auto &p1 = s1->get_parameter(i);
            auto &p2 = s2->get_parameter(i);
            if (p1.is_ast() && is_sort(p1.get_ast())) {
                if (!p2.is_ast())
                    return false;
                if (!is_sort(p2.get_ast()))
                    return false;
                if (!match(to_sort(p1.get_ast()), to_sort(p2.get_ast())))
                    return false;
                continue;
            }
            if (p1 != p2)
                return false;
        }
        return true;
    }     

    // util        
    bool util::unify(sort* s1, sort* s2, substitution& sub) {
        return sub.unify(s1, s2);
    }
        
    bool util::unify(func_decl* f1, func_decl* f2, substitution& sub) {
        if (f1 == f2)
            return true;
        if (!f1->is_polymorphic() || !f2->is_polymorphic())
            return false;
        if (m.poly_root(f1) != m.poly_root(f2))
            return false;
        for (unsigned i = f1->get_arity(); i-- > 0; )
            if (!sub.unify(fresh(f1->get_domain(i)), f2->get_domain(i)))
                return false;
        return sub.unify(fresh(f1->get_range()), f2->get_range());
    }
        
    bool util::unify(substitution const& s1, substitution const& s2,
                     substitution& sub) {
        sort* v2;
        for (auto const& [k, v] : s1)
            sub.insert(k, v);
        for (auto const& [k, v] : s2) {
            if (sub.find(k, v2)) {
                if (!sub.unify(sub(v), v2))
                    return false;
            }
            else
                sub.insert(k, sub(v));
        }
        return true;
    }

    bool util::match(substitution& sub, sort* s1, sort* s_ground) {
        return sub.match(s1, s_ground);
    }
     
    /**
    * Create fresh variables, but with caching. 
    * So "fresh" variables are not truly fresh globally.
    * This can block some unifications and therefore block some instantiations of
    * polymorphic assertions. A different caching scheme could be created to
    * ensure that fresh variables are introduced at the right time, or use other
    * tricks such as creating variable/offset pairs to distinguish name spaces without 
    * incurring costs.
    */
    sort_ref util::fresh(sort* s) {
        sort* s1;
        if (m_fresh.find(s, s1))
            return sort_ref(s1, m);

        if (m.is_type_var(s)) {
            s1 = m.mk_type_var(symbol("fresh!" + std::to_string(m_counter)));
            m_trail.push_back(s1);
            m_trail.push_back(s);
            m_fresh.insert(s, s1);
            return sort_ref(s1, m);
        }
        vector<parameter> params;
        for (unsigned i = 0; i < s->get_num_parameters(); ++i) {
            const parameter &p = s->get_parameter(i);
            if (p.is_ast() && is_sort(p.get_ast())) {
                sort_ref fs = fresh(to_sort(p.get_ast()));
                params.push_back(parameter(fs.get()));
            }
            else
                params.push_back(p);
        }
        sort_info info(s->get_family_id(), s->get_decl_kind(), params.size(), params.data(), s->private_parameters());
        s1 = m.mk_sort(s->get_name(), info);
        m_trail.push_back(s1);
        m_trail.push_back(s);
        m_fresh.insert(s, s1);
        return sort_ref(s1, m);
    }
        
    sort_ref_vector util::fresh(unsigned n, sort* const* s) {
        sort_ref_vector r(m);
        for (unsigned i = 0; i < n; ++i)
            r.push_back(fresh(s[i]));
        return r;
    }
     
    void util::collect_poly_instances(expr* e, ptr_vector<func_decl>& instances) {
        struct proc {
            ast_manager& m;
            ptr_vector<func_decl>& instances;
            proc(ast_manager& m, ptr_vector<func_decl>& instances) : m(m), instances(instances) {}
            void operator()(func_decl* f) {
                if (f->is_polymorphic() && !m.is_eq(f) && !is_decl_of(f, pattern_family_id, OP_PATTERN))
                    instances.push_back(f);
            }
            void operator()(ast* a) {}
        };
        proc proc(m, instances);
        for_each_ast(proc, e, false);        
    }
        
    bool util::has_type_vars(expr* e) {
        struct proc {
            ast_manager& m;
            bool found = false;
            proc(ast_manager& m) : m(m) {}
            void operator()(sort* f) {
                if (m.has_type_var(f))
                    found = true;
            }
            void operator()(ast* a) {}
        };
        proc proc(m);
        for_each_ast(proc, e, false);
        return proc.found;
    }
    
    void util::collect_type_vars(expr* e, ptr_vector<sort>& tvs) {
        struct proc {
            ast_manager& m;
            ptr_vector<sort>& tvs;
            proc(ast_manager& m, ptr_vector<sort>& tvs) : m(m), tvs(tvs) {}
            void operator()(sort* s) {
                if (m.is_type_var(s))
                    tvs.push_back(s);
            }
            void operator()(ast* a) {}
        };
        proc proc(m, tvs);
        for_each_ast(proc, e, true);
    }
}
