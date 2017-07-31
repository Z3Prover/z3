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

#include "ast/rewriter/quant_hoist.h"
#include "ast/expr_functors.h"
#include "ast/ast_smt_pp.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/rewriter/var_subst.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/ast_counter.h"
#include "ast/rewriter/expr_safe_replace.h"

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
    
    void operator()(expr* fml, app_ref_vector& vars, bool& is_fa, expr_ref& result, bool use_fresh, bool rewrite_ok) {
        quantifier_type qt = Q_none_pos;
        pull_quantifier(fml, qt, vars, result, use_fresh, rewrite_ok);
        TRACE("qe_verbose", 
              tout << mk_pp(fml, m) << "\n";
              tout << mk_pp(result, m) << "\n";);
        SASSERT(is_positive(qt));
        is_fa = (Q_forall_pos == qt);
    }
    
    void pull_exists(expr* fml, app_ref_vector& vars, expr_ref& result, bool use_fresh, bool rewrite_ok) {
        quantifier_type qt = Q_exists_pos;
        pull_quantifier(fml, qt, vars, result, use_fresh, rewrite_ok);
        TRACE("qe_verbose", 
              tout << mk_pp(fml, m) << "\n";
              tout << mk_pp(result, m) << "\n";);
    }

    void pull_quantifier(bool is_forall, expr_ref& fml, app_ref_vector& vars, bool use_fresh, bool rewrite_ok) {
        quantifier_type qt = is_forall?Q_forall_pos:Q_exists_pos;
        expr_ref result(m);
        pull_quantifier(fml, qt, vars, result, use_fresh, rewrite_ok);
        TRACE("qe_verbose", 
              tout << mk_pp(fml, m) << "\n";
              tout << mk_pp(result, m) << "\n";);
        fml = result;
    }
    
    void extract_quantifier(quantifier* q, app_ref_vector& vars, expr_ref& result, bool use_fresh) {
        unsigned nd = q->get_num_decls();
        for (unsigned i = 0; i < nd; ++i) {
            sort* s = q->get_decl_sort(i);
            symbol const& sym = q->get_decl_name (i);
            app* a = use_fresh ? m.mk_fresh_const(sym.str ().c_str (), s)
                               : m.mk_const (sym, s);
            vars.push_back(a);
        }
        expr * const * exprs = (expr* const*) (vars.c_ptr() + vars.size()- nd);
        instantiate(m, q, exprs, result);
    }

    unsigned pull_quantifier(bool is_forall, expr_ref& fml, ptr_vector<sort>* sorts, svector<symbol>* names, bool use_fresh, bool rewrite_ok) {
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
        pull_quantifier(is_forall, fml, vars, use_fresh, rewrite_ok);
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
        qt = static_cast<quantifier_type>(qt ^0x1);
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
    
    
    void pull_quantifier(expr* fml, quantifier_type& qt, app_ref_vector& vars, expr_ref& result, bool use_fresh, bool rewrite_ok) {
        
        if (!has_quantifiers(fml)) {
            result = fml;
            return;
        }
        
        switch(fml->get_kind()) {
        case AST_APP: {
            expr_ref_vector args(m);
            expr_ref tmp(m);
            expr* t1, *t2, *t3;
            unsigned num_args = 0;
            app* a = to_app(fml);
            if (m.is_and(fml)) {
                num_args = a->get_num_args();
                for (unsigned i = 0; i < num_args; ++i) {
                    pull_quantifier(a->get_arg(i), qt, vars, tmp, use_fresh, rewrite_ok);
                    args.push_back(tmp);
                }
                if (rewrite_ok) {
                m_rewriter.mk_and(args.size(), args.c_ptr(), result);
            }
                else {
                    result = m.mk_and (args.size (), args.c_ptr ());
                }
            }
            else if (m.is_or(fml)) {
                num_args = to_app(fml)->get_num_args();
                for (unsigned i = 0; i < num_args; ++i) {
                    pull_quantifier(to_app(fml)->get_arg(i), qt, vars, tmp, use_fresh, rewrite_ok);
                    args.push_back(tmp);
                }
                if (rewrite_ok) {
                m_rewriter.mk_or(args.size(), args.c_ptr(), result);
            }
                else {
                    result = m.mk_or (args.size (), args.c_ptr ());
                }
            }
            else if (m.is_not(fml)) {
                pull_quantifier(to_app(fml)->get_arg(0), negate(qt), vars, tmp, use_fresh, rewrite_ok);
                negate(qt);
                result = m.mk_not(tmp);
            }
            else if (m.is_implies(fml, t1, t2)) {
                pull_quantifier(t1, negate(qt), vars, tmp, use_fresh, rewrite_ok);
                negate(qt);
                pull_quantifier(t2, qt, vars, result, use_fresh, rewrite_ok);
                result = m.mk_implies(tmp, result);
            }
            else if (m.is_ite(fml, t1, t2, t3)) {
                expr_ref tt1(m), tt2(m), tt3(m), ntt1(m), nt1(m);
                pull_quantifier(t2, qt, vars, tt2, use_fresh, rewrite_ok);
                pull_quantifier(t3, qt, vars, tt3, use_fresh, rewrite_ok);
                if (has_quantifiers(t1)) {
                    pull_quantifier(t1, qt, vars, tt1, use_fresh, rewrite_ok);
                    nt1 = m.mk_not(t1);
                    pull_quantifier(nt1, qt, vars, ntt1, use_fresh, rewrite_ok);
                    result = m.mk_and(m.mk_or(ntt1, tt2), m.mk_or(tt1, tt3));
                }
                else {
                    result = m.mk_ite(t1, tt2, tt3);
                }
            }
            else if ((m.is_eq(fml, t1, t2) && m.is_bool(t1)) || m.is_iff(fml, t1, t2)) {
                expr_ref tt1(m), tt2(m), ntt1(m), ntt2(m), nt1(m), nt2(m);
                pull_quantifier(t1, qt, vars, tt1, use_fresh, rewrite_ok);
                pull_quantifier(t2, qt, vars, tt2, use_fresh, rewrite_ok);
                nt1 = m.mk_not(t1);
                nt2 = m.mk_not(t2);
                pull_quantifier(nt1, qt, vars, ntt1, use_fresh, rewrite_ok);
                pull_quantifier(nt2, qt, vars, ntt2, use_fresh, rewrite_ok);
                result = m.mk_and(m.mk_or(ntt1, tt2), m.mk_or(ntt2, tt1));
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
            extract_quantifier(q, vars, tmp, use_fresh);
            pull_quantifier(tmp, qt, vars, result, use_fresh, rewrite_ok);
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

void quantifier_hoister::operator()(expr* fml, app_ref_vector& vars, bool& is_fa, expr_ref& result, bool use_fresh, bool rewrite_ok) {
    (*m_impl)(fml, vars, is_fa, result, use_fresh, rewrite_ok);
}

void quantifier_hoister::pull_exists(expr* fml, app_ref_vector& vars, expr_ref& result, bool use_fresh, bool rewrite_ok) {
    m_impl->pull_exists(fml, vars, result, use_fresh, rewrite_ok);
}

void quantifier_hoister::pull_quantifier(bool is_forall, expr_ref& fml, app_ref_vector& vars, bool use_fresh, bool rewrite_ok) {
    m_impl->pull_quantifier(is_forall, fml, vars, use_fresh, rewrite_ok);
}

unsigned quantifier_hoister::pull_quantifier(bool is_forall, expr_ref& fml, ptr_vector<sort>* sorts, svector<symbol>* names, bool use_fresh, bool rewrite_ok) {
    return m_impl->pull_quantifier(is_forall, fml, sorts, names, use_fresh, rewrite_ok);
}
