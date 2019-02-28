/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    enum2bv_rewriter.cpp

Abstract:

    Conversion from enumeration types to bit-vectors.

Author:

    Nikolaj Bjorner (nbjorner) 2016-10-18

Notes:

--*/

#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/enum2bv_rewriter.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"

struct enum2bv_rewriter::imp {
    ast_manager&              m;
    params_ref                m_params;
    obj_map<func_decl, func_decl*> m_enum2bv;
    obj_map<func_decl, func_decl*> m_bv2enum;
    obj_map<func_decl, expr*> m_enum2def;
    expr_ref_vector           m_bounds;
    datatype_util             m_dt;
    func_decl_ref_vector      m_enum_consts;
    func_decl_ref_vector      m_enum_bvs;
    expr_ref_vector           m_enum_defs;
    unsigned_vector           m_enum_consts_lim;
    unsigned                  m_num_translated;
    i_sort_pred*              m_sort_pred;

    struct rw_cfg : public default_rewriter_cfg {
        imp&                 m_imp;
        ast_manager&         m;        
        datatype_util        m_dt;
        bv_util              m_bv;

        rw_cfg(imp& i, ast_manager & m) :
            m_imp(i),
            m(m),
            m_dt(m),
            m_bv(m)
        {}

        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            expr_ref a0(m), a1(m);
            expr_ref_vector _args(m);
            if (m.is_eq(f) && reduce_arg(args[0], a0) && reduce_arg(args[1], a1)) {
                result = m.mk_eq(a0, a1);
                return BR_DONE;
            }
            else if (m.is_distinct(f) && reduce_args(num, args, _args)) {
                result = m.mk_distinct(_args.size(), _args.c_ptr());
                return BR_DONE;
            }
            else if (m_dt.is_recognizer(f) && reduce_arg(args[0], a0)) {
                unsigned idx = m_dt.get_recognizer_constructor_idx(f);
                a1 = m_bv.mk_numeral(rational(idx), get_sort(a0));
                result = m.mk_eq(a0, a1);
                return BR_DONE;
            }
            else {
                check_for_fd(num, args);
                return BR_FAILED;
            }
        }

        bool reduce_args(unsigned sz, expr*const* as, expr_ref_vector& result) {
            expr_ref tmp(m);
            for (unsigned i = 0; i < sz; ++i) {
                if (!reduce_arg(as[i], tmp)) return false;
                result.push_back(tmp);
            }
            return true;
        }

        void throw_non_fd(expr* e) {
            std::stringstream strm;
            strm << "unable to handle nested data-type expression " << mk_pp(e, m);
            throw rewriter_exception(strm.str());
        }

        void check_for_fd(unsigned n, expr* const* args) {
            for (unsigned i = 0; i < n; ++i) {
                if (m_imp.is_fd(get_sort(args[i]))) {
                    throw_non_fd(args[i]);
                }
            }
        }

        bool reduce_arg(expr* a, expr_ref& result) {

            sort* s = get_sort(a);
            if (!m_imp.is_fd(s)) {
                return false;
            }
            unsigned bv_size = get_bv_size(s);

            if (is_var(a)) {
                result = m.mk_var(to_var(a)->get_idx(), m_bv.mk_sort(bv_size));
                return true;
            }
            SASSERT(is_app(a));
            func_decl* f = to_app(a)->get_decl();
            if (m_dt.is_constructor(f)) {
                unsigned idx = m_dt.get_constructor_idx(f);
                result = m_bv.mk_numeral(idx, bv_size);
            }
            else if (is_uninterp_const(a)) {
                func_decl* f_fresh;
                if (m_imp.m_enum2bv.find(f, f_fresh)) {
                    result = m.mk_const(f_fresh);
                    return true;
                }

                // create a fresh variable, add bounds constraints for it.
                unsigned nc = m_dt.get_datatype_num_constructors(s);
                result = m.mk_fresh_const(f->get_name().str().c_str(), m_bv.mk_sort(bv_size));
                f_fresh = to_app(result)->get_decl();
                if (!is_power_of_two(nc) || nc == 1) {
                    m_imp.m_bounds.push_back(m_bv.mk_ule(result, m_bv.mk_numeral(nc-1, bv_size)));
                }                
                expr_ref f_def(m);
                ptr_vector<func_decl> const& cs = *m_dt.get_datatype_constructors(s);
                f_def = m.mk_const(cs[nc-1]);
                for (unsigned i = nc - 1; i > 0; ) {
                    --i;
                    f_def = m.mk_ite(m.mk_eq(result, m_bv.mk_numeral(i,bv_size)), m.mk_const(cs[i]), f_def);
                }
                m_imp.m_enum2def.insert(f, f_def);
                m_imp.m_enum2bv.insert(f, f_fresh);
                m_imp.m_bv2enum.insert(f_fresh, f);
                m_imp.m_enum_consts.push_back(f);
                m_imp.m_enum_bvs.push_back(f_fresh);
                m_imp.m_enum_defs.push_back(f_def);
            }
            else {
                throw_non_fd(a);
            }
            ++m_imp.m_num_translated;
            return true;
        }

        ptr_buffer<sort> m_sorts;

        bool reduce_quantifier(
            quantifier * q,
            expr * old_body,
            expr * const * new_patterns,
            expr * const * new_no_patterns,
            expr_ref & result,
            proof_ref & result_pr) {

            if (q->get_kind() == lambda_k) return false;
            m_sorts.reset();
            expr_ref_vector bounds(m);
            bool found = false;
            for (unsigned i = 0; i < q->get_num_decls(); ++i) {
                sort* s = q->get_decl_sort(i);
                if (m_imp.is_fd(s)) {
                    unsigned bv_size = get_bv_size(s);
                    m_sorts.push_back(m_bv.mk_sort(bv_size));
                    unsigned nc = m_dt.get_datatype_num_constructors(s);
                    if (!is_power_of_two(nc) || nc == 1) {
                        bounds.push_back(m_bv.mk_ule(m.mk_var(q->get_num_decls()-i-1, m_sorts[i]), m_bv.mk_numeral(nc-1, bv_size)));
                    }                
                    found = true;
                }
                else {
                    m_sorts.push_back(s);
                }
            }
            if (!found) {
                return false;
            }
            expr_ref new_body_ref(old_body, m), tmp(m);
            if (!bounds.empty()) {
                switch (q->get_kind()) {
                case forall_k:
                    new_body_ref = m.mk_implies(mk_and(bounds), new_body_ref);
                    break;
                case exists_k:
                    bounds.push_back(new_body_ref);
                    new_body_ref = mk_and(bounds);
                    break;
                case lambda_k:
                    UNREACHABLE();
                    break;
                }
            }
            result = m.mk_quantifier(q->get_kind(), q->get_num_decls(), m_sorts.c_ptr(), q->get_decl_names(), new_body_ref, 
                                     q->get_weight(), q->get_qid(), q->get_skid(), 
                                     q->get_num_patterns(), new_patterns,
                                     q->get_num_no_patterns(), new_no_patterns);
            result_pr = nullptr;
            return true;
        }

        unsigned get_bv_size(sort* s) {
            unsigned nc = m_dt.get_datatype_num_constructors(s);
            unsigned bv_size = 1;
            while ((unsigned)(1 << bv_size) < nc) {
                ++bv_size;
            }
            return bv_size;
        }
    };

    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;

        rw(imp& t, ast_manager & m, params_ref const & p) :
            rewriter_tpl<rw_cfg>(m, m.proofs_enabled(), m_cfg),
            m_cfg(t, m) {
        }
    };

    rw m_rw;
    
    imp(ast_manager& m, params_ref const& p): 
        m(m), m_params(p), m_bounds(m),
        m_dt(m),
        m_enum_consts(m),
        m_enum_bvs(m),
        m_enum_defs(m),
        m_num_translated(0), 
        m_sort_pred(nullptr),
        m_rw(*this, m, p) {
    }

    void updt_params(params_ref const & p) {}
    unsigned get_num_steps() const { return m_rw.get_num_steps(); }
    void cleanup() { m_rw.cleanup(); }
    void operator()(expr * e, expr_ref & result, proof_ref & result_proof) {
        m_rw(e, result, result_proof);
    }
    void push() {
        m_enum_consts_lim.push_back(m_enum_consts.size());
    }
    void pop(unsigned num_scopes) {
        SASSERT(m_bounds.empty()); // bounds must be flushed before pop.
        if (num_scopes > 0) {
            SASSERT(num_scopes <= m_enum_consts_lim.size());
            unsigned new_sz = m_enum_consts_lim.size() - num_scopes;
            unsigned lim = m_enum_consts_lim[new_sz];
            for (unsigned i = m_enum_consts.size(); i > lim; ) {
                --i;
                func_decl* f = m_enum_consts[i].get();
                func_decl* f_fresh = m_enum2bv.find(f);
                m_bv2enum.erase(f_fresh);
                m_enum2bv.erase(f);
                m_enum2def.erase(f);
            }
            m_enum_consts_lim.resize(new_sz);
            m_enum_consts.resize(lim);
            m_enum_defs.resize(lim);
            m_enum_bvs.resize(lim);
        }
        m_rw.reset();
    }

    void flush_side_constraints(expr_ref_vector& side_constraints) { 
        side_constraints.append(m_bounds);  
        m_bounds.reset(); 
    }

    bool is_fd(sort* s) {
        return m_dt.is_enum_sort(s) && (!m_sort_pred || (*m_sort_pred)(s));
    }

    void set_is_fd(i_sort_pred* sp) {
        m_sort_pred = sp;
    }
};


enum2bv_rewriter::enum2bv_rewriter(ast_manager & m, params_ref const& p) {  m_imp = alloc(imp, m, p); }
enum2bv_rewriter::~enum2bv_rewriter() { dealloc(m_imp); }
void enum2bv_rewriter::updt_params(params_ref const & p) { m_imp->updt_params(p); }
ast_manager & enum2bv_rewriter::m() const { return m_imp->m; }
unsigned enum2bv_rewriter::get_num_steps() const { return m_imp->get_num_steps(); }
void enum2bv_rewriter::cleanup() { ast_manager& mgr = m(); params_ref p = m_imp->m_params; dealloc(m_imp); m_imp = alloc(imp, mgr, p);  }
obj_map<func_decl, func_decl*> const& enum2bv_rewriter::enum2bv() const { return m_imp->m_enum2bv; }
obj_map<func_decl, func_decl*> const& enum2bv_rewriter::bv2enum() const { return m_imp->m_bv2enum; }
obj_map<func_decl, expr*> const& enum2bv_rewriter::enum2def() const { return m_imp->m_enum2def; }
void enum2bv_rewriter::operator()(expr * e, expr_ref & result, proof_ref & result_proof) { (*m_imp)(e, result, result_proof); }
void enum2bv_rewriter::push() { m_imp->push(); }
void enum2bv_rewriter::pop(unsigned num_scopes) { m_imp->pop(num_scopes); }
void enum2bv_rewriter::flush_side_constraints(expr_ref_vector& side_constraints) { m_imp->flush_side_constraints(side_constraints); } 
unsigned enum2bv_rewriter::num_translated() const { return m_imp->m_num_translated; }
void enum2bv_rewriter::set_is_fd(i_sort_pred* sp) const { m_imp->set_is_fd(sp); }
