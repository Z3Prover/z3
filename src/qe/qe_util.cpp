#include "qe_util.h"
#include "bool_rewriter.h"

namespace qe {
    void flatten_and(expr_ref_vector& result) {
        ast_manager& m = result.get_manager();
        expr* e1, *e2, *e3;
        for (unsigned i = 0; i < result.size(); ++i) {
            if (m.is_and(result[i].get())) {
                app* a = to_app(result[i].get());
                unsigned num_args = a->get_num_args();
                for (unsigned j = 0; j < num_args; ++j) {
                    result.push_back(a->get_arg(j));
                }
                result[i] = result.back();
                result.pop_back();
                --i;
            }
            else if (m.is_not(result[i].get(), e1) && m.is_not(e1, e2)) {
                result[i] = e2;
                --i;
            }
            else if (m.is_not(result[i].get(), e1) && m.is_or(e1)) {
                app* a = to_app(e1);
                unsigned num_args = a->get_num_args();
                for (unsigned j = 0; j < num_args; ++j) {
                    result.push_back(m.mk_not(a->get_arg(j)));
                }
                result[i] = result.back();
                result.pop_back();
                --i;                
            }
            else if (m.is_not(result[i].get(), e1) && m.is_implies(e1,e2,e3)) {
                result.push_back(e2);
                result[i] = m.mk_not(e3);
                --i;
            }
            else if (m.is_true(result[i].get()) ||
                     (m.is_not(result[i].get(), e1) &&
                      m.is_false(e1))) {
                result[i] = result.back();
                result.pop_back();
                --i;                
            }
            else if (m.is_false(result[i].get()) ||
                     (m.is_not(result[i].get(), e1) &&
                      m.is_true(e1))) {
                result.reset();
                result.push_back(m.mk_false());
                return;
            }
        }
    }

    void flatten_and(expr* fml, expr_ref_vector& result) {
        SASSERT(result.get_manager().is_bool(fml));
        result.push_back(fml);        
        flatten_and(result);
    }

    void flatten_or(expr_ref_vector& result) {
        ast_manager& m = result.get_manager();
        expr* e1, *e2, *e3;
        for (unsigned i = 0; i < result.size(); ++i) {
            if (m.is_or(result[i].get())) {
                app* a = to_app(result[i].get());
                unsigned num_args = a->get_num_args();
                for (unsigned j = 0; j < num_args; ++j) {
                    result.push_back(a->get_arg(j));
                }
                result[i] = result.back();
                result.pop_back();
                --i;
            }
            else if (m.is_not(result[i].get(), e1) && m.is_not(e1, e2)) {
                result[i] = e2;
                --i;
            }
            else if (m.is_not(result[i].get(), e1) && m.is_and(e1)) {
                app* a = to_app(e1);
                unsigned num_args = a->get_num_args();
                for (unsigned j = 0; j < num_args; ++j) {
                    result.push_back(m.mk_not(a->get_arg(j)));
                }
                result[i] = result.back();
                result.pop_back();
                --i;                
            }
            else if (m.is_implies(result[i].get(),e2,e3)) {
                result.push_back(e3);
                result[i] = m.mk_not(e2);
                --i;
            }
            else if (m.is_false(result[i].get()) ||
                     (m.is_not(result[i].get(), e1) &&
                      m.is_true(e1))) {
                result[i] = result.back();
                result.pop_back();
                --i;                
            }
            else if (m.is_true(result[i].get()) ||
                     (m.is_not(result[i].get(), e1) &&
                      m.is_false(e1))) {
                result.reset();
                result.push_back(m.mk_true());
                return;
            }
        }        
    }


    void flatten_or(expr* fml, expr_ref_vector& result) {
        SASSERT(result.get_manager().is_bool(fml));
        result.push_back(fml);        
        flatten_or(result);
    }

    expr_ref mk_and(expr_ref_vector const& fmls) {
        ast_manager& m = fmls.get_manager();
        expr_ref result(m);
        bool_rewriter(m).mk_and(fmls.size(), fmls.c_ptr(), result);
        return result;
    }

    expr_ref mk_or(expr_ref_vector const& fmls) {
        ast_manager& m = fmls.get_manager();
        expr_ref result(m);
        bool_rewriter(m).mk_or(fmls.size(), fmls.c_ptr(), result);
        return result;
    }

}
