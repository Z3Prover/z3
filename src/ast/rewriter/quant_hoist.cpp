/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    quant_hoist.cpp

Abstract:

    Quantifier hoisting utility.

Author:

    Nikolaj Bjorner (nbjorner) 2010-02-19

Revision History:

    Hoisted from quant_elim.

--*/

#include "quant_hoist.h"
#include "expr_functors.h"
#include "ast_smt_pp.h"
#include "bool_rewriter.h"
#include "var_subst.h"
#include "ast_pp.h"
#include "ast_counter.h"
#include "expr_safe_replace.h"

//
// Bring quantifiers of common type into prenex form.
// 
class quantifier_hoister::impl {
    ast_manager&        m;
    bool_rewriter       m_rewriter;
    
public:
    impl(ast_manager& m) :
        m(m),
        m_rewriter(m)
    {}
    
    void operator()(expr* fml, app_ref_vector& vars, bool& is_fa, expr_ref& result) {
        quantifier_type qt = Q_none_pos;
        pull_quantifier(fml, qt, vars, result);
        TRACE("qe_verbose", 
              tout << mk_pp(fml, m) << "\n";
              tout << mk_pp(result, m) << "\n";);
        SASSERT(is_positive(qt));
        is_fa = (Q_forall_pos == qt);
    }
    
    void pull_exists(expr* fml, app_ref_vector& vars, expr_ref& result) {
        quantifier_type qt = Q_exists_pos;
        pull_quantifier(fml, qt, vars, result);
        TRACE("qe_verbose", 
              tout << mk_pp(fml, m) << "\n";
              tout << mk_pp(result, m) << "\n";);
    }

    void pull_quantifier(bool is_forall, expr_ref& fml, app_ref_vector& vars) {
        quantifier_type qt = is_forall?Q_forall_pos:Q_exists_pos;
        expr_ref result(m);
        pull_quantifier(fml, qt, vars, result);
        TRACE("qe_verbose", 
              tout << mk_pp(fml, m) << "\n";
              tout << mk_pp(result, m) << "\n";);
        fml = result;
    }
    
    void extract_quantifier(quantifier* q, app_ref_vector& vars, expr_ref& result) {
        unsigned nd = q->get_num_decls();
        for (unsigned i = 0; i < nd; ++i) {
            sort* s = q->get_decl_sort(i);
            app* a = m.mk_fresh_const("x", s);
            vars.push_back(a);
        }
        expr * const * exprs = (expr* const*) (vars.c_ptr() + vars.size()- nd);
        instantiate(m, q, exprs, result);
    }

    unsigned pull_quantifier(bool is_forall, expr_ref& fml, ptr_vector<sort>* sorts, svector<symbol>* names) {
        unsigned index = var_counter().get_next_var(fml);
        while (is_quantifier(fml) && (is_forall == to_quantifier(fml)->is_forall())) {
            quantifier* q = to_quantifier(fml);
            index += q->get_num_decls();
            if (names) {
                names->append(q->get_num_decls(), q->get_decl_names());
            }
            if (sorts) {
                sorts->append(q->get_num_decls(), q->get_decl_sorts());
            }
            fml = q->get_expr();
        }
        if (!has_quantifiers(fml)) {
            return index;
        }
        app_ref_vector vars(m);
        pull_quantifier(is_forall, fml, vars);
        if (vars.empty()) {
            return index;
        }
        // replace vars by de-bruijn indices
        expr_safe_replace rep(m);
        svector<symbol> bound_names;
        ptr_vector<sort> bound_sorts;
        for (unsigned i = 0; i < vars.size(); ++i) {
            app* v = vars[i].get();
            if (names) {
                bound_names.push_back(v->get_decl()->get_name());
            }                
            if (sorts) {
                bound_sorts.push_back(m.get_sort(v));
            }
            rep.insert(v, m.mk_var(index++, m.get_sort(v)));
        }
        if (names && !bound_names.empty()) {
            bound_names.reverse();
            bound_names.append(*names);
            names->reset();
            names->append(bound_names);
        }
        if (sorts && !bound_sorts.empty()) {
            bound_sorts.reverse();
            bound_sorts.append(*sorts);
            sorts->reset();
            sorts->append(bound_sorts);
        }
        rep(fml);
        return index;
    }    
    
private:
    
    enum quantifier_type {
        Q_forall_pos = 0x10,
        Q_exists_pos = 0x20,
        Q_none_pos   = 0x40,
        Q_forall_neg = 0x11,
        Q_exists_neg = 0x21,
        Q_none_neg   = 0x41
    };
    
    void display(quantifier_type qt, std::ostream& out) {
        switch(qt) {
        case Q_forall_pos: out << "Forall+"; break;
        case Q_exists_pos: out << "Exists+"; break;
        case Q_none_pos:   out << "None+"; break;
        case Q_forall_neg: out << "Forall-"; break;
        case Q_exists_neg: out << "Exists-"; break;
        case Q_none_neg:   out << "None-"; break;
        }
    }
    
    quantifier_type& negate(quantifier_type& qt) {
        TRACE("qe", display(qt, tout); tout << "\n";);
        qt = static_cast<quantifier_type>(qt ^0x1);
        TRACE("qe", display(qt, tout); tout << "\n";);
        return qt;
    }
    
    static bool is_negative(quantifier_type qt) {
        return 0 != (qt & 0x1);
    }
    
    static bool is_positive(quantifier_type qt) {
        return 0 == (qt & 0x1);
    }
    
    static void set_quantifier_type(quantifier_type& qt, bool is_forall) {
        switch(qt) {
        case Q_forall_pos: SASSERT(is_forall); break;
        case Q_forall_neg: SASSERT(!is_forall); break;
        case Q_exists_pos: SASSERT(!is_forall); break;
        case Q_exists_neg: SASSERT(is_forall); break;
        case Q_none_pos: qt = is_forall?Q_forall_pos:Q_exists_pos; break;
        case Q_none_neg: qt = is_forall?Q_exists_neg:Q_forall_neg; break;
        }
    }
    
    bool is_compatible(quantifier_type qt, bool is_forall) {
        switch(qt) {
        case Q_forall_pos: return is_forall;
        case Q_forall_neg: return !is_forall;
        case Q_exists_pos: return !is_forall;
        case Q_exists_neg: return is_forall;
        case Q_none_pos: return true;
        case Q_none_neg: return true;
        default:
            UNREACHABLE();
        }
        return false;
    }
    
    
    void pull_quantifier(expr* fml, quantifier_type& qt, app_ref_vector& vars, expr_ref& result) {
        
        if (!has_quantifiers(fml)) {
            result = fml;
            return;
        }
        
        switch(fml->get_kind()) {
        case AST_APP: {
            expr_ref_vector args(m);
            expr_ref tmp(m);
            unsigned num_args = 0;
            app* a = to_app(fml);
            if (m.is_and(fml)) {
                num_args = a->get_num_args();
                for (unsigned i = 0; i < num_args; ++i) {
                    pull_quantifier(a->get_arg(i), qt, vars, tmp);
                    args.push_back(tmp);
                }
                m_rewriter.mk_and(args.size(), args.c_ptr(), result);
            }
            else if (m.is_or(fml)) {
                num_args = to_app(fml)->get_num_args();
                for (unsigned i = 0; i < num_args; ++i) {
                    pull_quantifier(to_app(fml)->get_arg(i), qt, vars, tmp);
                    args.push_back(tmp);
                }
                m_rewriter.mk_or(args.size(), args.c_ptr(), result);
            }
            else if (m.is_not(fml)) {
                pull_quantifier(to_app(fml)->get_arg(0), negate(qt), vars, tmp);
                negate(qt);
                result = m.mk_not(tmp);
            }
            else if (m.is_implies(fml)) {
                pull_quantifier(to_app(fml)->get_arg(0), negate(qt), vars, tmp);
                negate(qt);
                pull_quantifier(to_app(fml)->get_arg(1), qt, vars, result);
                result = m.mk_implies(tmp, result);
            }
            else if (m.is_ite(fml)) {
                pull_quantifier(to_app(fml)->get_arg(1), qt, vars, tmp);
                pull_quantifier(to_app(fml)->get_arg(2), qt, vars, result);
                result = m.mk_ite(to_app(fml)->get_arg(0), tmp, result);
            }
            else {
                // the formula contains a quantifier, but it is "inaccessible"
                result = fml;
            }
            break;
        }
        case AST_QUANTIFIER: {
            quantifier* q = to_quantifier(fml);
            expr_ref tmp(m);
            if (!is_compatible(qt, q->is_forall())) {
                result = fml;
                break;
            }
            set_quantifier_type(qt, q->is_forall());
            extract_quantifier(q, vars, tmp);
            pull_quantifier(tmp, qt, vars, result);
            break;
        }
        case AST_VAR:
            result = fml;
            break;
        default:
            UNREACHABLE();
            result = fml;
            break;
        }
    }

};   

quantifier_hoister::quantifier_hoister(ast_manager& m) {
    m_impl = alloc(impl, m);
}

quantifier_hoister::~quantifier_hoister() {
    dealloc(m_impl);
}

void quantifier_hoister::operator()(expr* fml, app_ref_vector& vars, bool& is_fa, expr_ref& result) {
    (*m_impl)(fml, vars, is_fa, result);
}

void quantifier_hoister::pull_exists(expr* fml, app_ref_vector& vars, expr_ref& result) {
    m_impl->pull_exists(fml, vars, result);
}

void quantifier_hoister::pull_quantifier(bool is_forall, expr_ref& fml, app_ref_vector& vars) {
    m_impl->pull_quantifier(is_forall, fml, vars);
}

unsigned quantifier_hoister::pull_quantifier(bool is_forall, expr_ref& fml, ptr_vector<sort>* sorts, svector<symbol>* names) {
    return m_impl->pull_quantifier(is_forall, fml, sorts, names);
}
