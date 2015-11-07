/*++
Copyright (c) 2008 Microsoft Corporation

Module Name:

    ast_translation.cpp

Abstract:

    AST translation functions

Author:

    Christoph Wintersteiger (t-cwinte) 2008-11-20

Revision History:

--*/
#include "arith_decl_plugin.h"
#include "bv_decl_plugin.h"
#include "datatype_decl_plugin.h"
#include "array_decl_plugin.h"
#include "format.h"
#include "ast_translation.h"
#include "ast_ll_pp.h"

ast_translation::~ast_translation() {
    reset_cache();
}

void ast_translation::cleanup() {
    reset_cache();
    m_cache.finalize();
    m_result_stack.finalize();
    m_frame_stack.finalize();
    m_extra_children_stack.finalize();
}

void ast_translation::reset_cache() {
    obj_map<ast, ast*>::iterator it  = m_cache.begin();
    obj_map<ast, ast*>::iterator end = m_cache.end();
    for (; it != end; ++it) {
        m_from_manager.dec_ref(it->m_key);
        m_to_manager.dec_ref(it->m_value);
    }
    m_cache.reset();
}

void ast_translation::cache(ast * s, ast * t) {
    SASSERT(!m_cache.contains(s));
    if (s->get_ref_count() > 1) {
        m_cache.insert(s, t);
        m_from_manager.inc_ref(s);
        m_to_manager.inc_ref(t);
    }
}

void ast_translation::collect_decl_extra_children(decl * d) {
    unsigned num_params = d->get_num_parameters();
    for (unsigned i = 0; i < num_params; i++) {
        parameter const & p = d->get_parameter(i);
        if (p.is_ast())
            m_extra_children_stack.push_back(p.get_ast());
    }
}

void ast_translation::push_frame(ast * n) {
    m_frame_stack.push_back(frame(n, 0, m_extra_children_stack.size(), m_result_stack.size()));
    switch (n->get_kind()) {
    case AST_SORT:
    case AST_FUNC_DECL:
        collect_decl_extra_children(to_decl(n));
        break;
    default:
        break;
    }
}

bool ast_translation::visit(ast * n) {        
    ast * r;
    if (n->get_ref_count() > 1 && m_cache.find(n, r)) {
        m_result_stack.push_back(r);
        return true;
    }
    push_frame(n);
    return false;
}

void ast_translation::copy_params(decl * d, unsigned rpos, buffer<parameter> & ps) {
    unsigned num = d->get_num_parameters();
    unsigned j   = rpos;
    for (unsigned i = 0; i < num; i++) {
        parameter const & p = d->get_parameter(i);
        if (p.is_ast()) {
            ps.push_back(parameter(m_result_stack[j]));
            j++;
        }
        else if (p.is_external()) {
            SASSERT(d->get_family_id() != null_family_id);
            decl_plugin & from_plugin = *(m_from_manager.get_plugin(d->get_family_id()));
            decl_plugin & to_plugin   = *(m_to_manager.get_plugin(d->get_family_id()));
            ps.push_back(from_plugin.translate(p, to_plugin));
        }
        else {
            ps.push_back(p);
        }
    }
}

void ast_translation::mk_sort(sort * s, frame & fr) {
    sort_info * si     = s->get_info();
    sort * new_s;
    if (si == 0) {
        // TODO: investigate: this branch is probably unreachable.
        // It became unreachable after we started using mk_uninterpreted_sort for creating uninterpreted sorts,
        // and mk_uninterpreted_sort actually creates a user_sort.
        new_s = m_to_manager.mk_uninterpreted_sort(s->get_name());
        SASSERT(m_result_stack.size() == fr.m_rpos);
    }
    else {
        buffer<parameter> ps;
        copy_params(s, fr.m_rpos, ps);
        new_s = m_to_manager.mk_sort(s->get_name(), sort_info(si->get_family_id(),
                                                              si->get_decl_kind(),
                                                              si->get_num_elements(),
                                                              si->get_num_parameters(),
                                                              ps.c_ptr(),
                                                              s->private_parameters()));
    }
    m_result_stack.shrink(fr.m_rpos);
    m_result_stack.push_back(new_s);
    m_extra_children_stack.shrink(fr.m_cpos);
    cache(s, new_s);
    m_frame_stack.pop_back();
}

void ast_translation::mk_func_decl(func_decl * f, frame & fr) {
    func_decl_info * fi   = f->get_info();
    SASSERT(fr.m_cpos <= m_extra_children_stack.size());
    unsigned num_extra = m_extra_children_stack.size() - fr.m_cpos;
    sort ** new_domain = reinterpret_cast<sort**>(m_result_stack.c_ptr() + fr.m_rpos + num_extra);
    sort *  new_range  = static_cast<sort*>(m_result_stack.back());  
    func_decl * new_f;
    if (fi == 0) {
        new_f = m_to_manager.mk_func_decl(f->get_name(),
                                          f->get_arity(),
                                          new_domain,
                                          new_range);
    }
    else {
        buffer<parameter> ps;
        copy_params(f, fr.m_rpos, ps);
        func_decl_info new_fi(fi->get_family_id(),
                              fi->get_decl_kind(),
                              fi->get_num_parameters(),
                              ps.c_ptr());

        new_fi.set_left_associative(fi->is_left_associative());
        new_fi.set_right_associative(fi->is_right_associative());
        new_fi.set_flat_associative(fi->is_flat_associative());
        new_fi.set_commutative(fi->is_commutative());
        new_fi.set_chainable(fi->is_chainable());
        new_fi.set_pairwise(fi->is_pairwise());
        new_fi.set_injective(fi->is_injective());
        new_fi.set_skolem(fi->is_skolem()); 
        new_fi.set_idempotent(fi->is_idempotent());

        new_f = m_to_manager.mk_func_decl(f->get_name(),
                                          f->get_arity(),
                                          new_domain,
                                          new_range,
                                          new_fi);
    }
    TRACE("ast_translation", 
          tout << f->get_name() << " "; if (fi) tout << *fi; tout << "\n";
          tout << "---->\n";
          tout << new_f->get_name() << " "; if (new_f->get_info()) tout << *(new_f->get_info()); tout << "\n";);

    m_result_stack.shrink(fr.m_rpos);
    m_result_stack.push_back(new_f);
    m_extra_children_stack.shrink(fr.m_cpos);
    cache(f, new_f);
    m_frame_stack.pop_back();
}

ast * ast_translation::process(ast const * _n) {
    if (!_n) return 0;
    SASSERT(m_result_stack.empty());
    SASSERT(m_frame_stack.empty());
    SASSERT(m_extra_children_stack.empty());
    
    if (!visit(const_cast<ast*>(_n))) {
        while (!m_frame_stack.empty()) {
        loop:
            frame & fr = m_frame_stack.back();
            ast * n = fr.m_n;
            ast * r;         
            TRACE("ast_translation", tout << mk_ll_pp(n, m_from_manager, false) << "\n";);
            if (fr.m_idx == 0 && n->get_ref_count() > 1 && m_cache.find(n, r)) {
                SASSERT(m_result_stack.size() == fr.m_rpos);
                m_result_stack.push_back(r);
                m_extra_children_stack.shrink(fr.m_cpos);
                m_frame_stack.pop_back();
                TRACE("ast_translation", tout << "hit\n";);
                continue;
            }
            switch (n->get_kind()) {
            case AST_VAR: {
                if (fr.m_idx == 0) {
                    fr.m_idx = 1;
                    if (!visit(to_var(n)->get_sort()))
                        goto loop;
                }
                sort * new_s  = to_sort(m_result_stack.back());
                var * new_var = m_to_manager.mk_var(to_var(n)->get_idx(), new_s);
                m_result_stack.pop_back();
                m_result_stack.push_back(new_var);
                cache(n, new_var);
                m_frame_stack.pop_back();
                break;
            }
            case AST_APP: {
                if (fr.m_idx == 0) {
                    fr.m_idx = 1;
                    if (!visit(to_app(n)->get_decl()))
                        goto loop;
                }
                unsigned num = to_app(n)->get_num_args();
                while (fr.m_idx <= num) {
                    expr * arg = to_app(n)->get_arg(fr.m_idx - 1);
                    fr.m_idx++;
                    if (!visit(arg))
                        goto loop;
                }
                func_decl * new_f   = to_func_decl(m_result_stack[fr.m_rpos]);
                expr ** new_args    = reinterpret_cast<expr **>(m_result_stack.c_ptr() + fr.m_rpos + 1);
                expr *  new_app     = m_to_manager.mk_app(new_f, num, new_args);
                m_result_stack.shrink(fr.m_rpos);
                m_result_stack.push_back(new_app);
                cache(n, new_app);
                m_frame_stack.pop_back();
                break;
            }
            case AST_QUANTIFIER: {
                unsigned num_decls = to_quantifier(n)->get_num_decls();
                unsigned num = num_decls + to_quantifier(n)->get_num_children();
                while (fr.m_idx < num) {
                    ast * child;
                    if (fr.m_idx < num_decls) 
                        child = to_quantifier(n)->get_decl_sort(fr.m_idx);
                    else
                        child = to_quantifier(n)->get_child(fr.m_idx - num_decls);
                    fr.m_idx++;
                    if (!visit(child))
                        goto loop;
                }
                symbol const * dnames = to_quantifier(n)->get_decl_names();
                sort **  dsorts       = reinterpret_cast<sort**>(m_result_stack.c_ptr() + fr.m_rpos);
                expr *   body         = static_cast<expr*>(m_result_stack[fr.m_rpos + num_decls]);
                unsigned num_pats     = to_quantifier(n)->get_num_patterns();
                expr **  pats         = reinterpret_cast<expr**>(m_result_stack.c_ptr() + fr.m_rpos + num_decls + 1);
                unsigned num_no_pats  = to_quantifier(n)->get_num_no_patterns();
                expr **  no_pats      = pats + num_pats;
                quantifier * new_q    = m_to_manager.mk_quantifier(to_quantifier(n)->is_forall(),
                                                                   num_decls,
                                                                   dsorts,
                                                                   dnames,
                                                                   body,
                                                                   to_quantifier(n)->get_weight(),
                                                                   to_quantifier(n)->get_qid(),
                                                                   to_quantifier(n)->get_skid(),
                                                                   num_pats, pats,
                                                                   num_no_pats, no_pats);
                m_result_stack.shrink(fr.m_rpos);
                m_result_stack.push_back(new_q);
                cache(n, new_q);
                m_frame_stack.pop_back();
                break;
            }
            case AST_SORT: {
                SASSERT(fr.m_cpos <= m_extra_children_stack.size());
                unsigned num = m_extra_children_stack.size() - fr.m_cpos;
                while (fr.m_idx < num) {
                    ast * c = m_extra_children_stack[fr.m_cpos + fr.m_idx];
                    fr.m_idx++;
                    if (!visit(c))
                        goto loop;
                }
                mk_sort(to_sort(n), fr);
                break;
            }
            case AST_FUNC_DECL: {
                SASSERT(fr.m_cpos <= m_extra_children_stack.size());
                unsigned num_extra = m_extra_children_stack.size() - fr.m_cpos;
                unsigned arity     = to_func_decl(n)->get_arity();
                unsigned num       = num_extra + arity + 1;
                while (fr.m_idx < num) {
                    ast * c;
                    if (fr.m_idx < num_extra)
                        c = m_extra_children_stack[fr.m_cpos + fr.m_idx];
                    else if (fr.m_idx < num_extra + arity)
                        c = to_func_decl(n)->get_domain(fr.m_idx - num_extra);
                    else
                        c = to_func_decl(n)->get_range();
                    fr.m_idx++;
                    if (!visit(c))
                        goto loop;
                }
                mk_func_decl(to_func_decl(n), fr);
                break;
            }
            default:
                UNREACHABLE();
                break;
            }
        }
    }
    SASSERT(m_result_stack.size() == 1);
    ast * r = m_result_stack.back();
    m_result_stack.reset();
    return r;
}

expr_dependency * expr_dependency_translation::operator()(expr_dependency * d) {
    if (d == 0)
        return d;
    m_buffer.reset();
    m_translation.from().linearize(d, m_buffer);
    unsigned sz = m_buffer.size();
    SASSERT(sz >= 1);
    for (unsigned i = 0; i < sz; i++) {
        m_buffer[i] = m_translation(m_buffer[i]);
    }
    return m_translation.to().mk_join(sz, m_buffer.c_ptr());
}
