/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    max_bv_sharing.cpp

Abstract:

    Rewriter for "maximing" the number of shared terms.
    The idea is to rewrite AC terms to maximize sharing.
    This rewriter is particularly useful for reducing
    the number of Adders and Multipliers before "bit-blasting".

Author

    Leonardo de Moura (leonardo) 2011-12-29.

Revision History:

--*/

#include "ast/bv_decl_plugin.h"
#include "ast/rewriter/rewriter_def.h"
#include "util/obj_pair_hashtable.h"
#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/ast_lt.h"

class max_bv_sharing : public dependent_expr_simplifier {
    
    struct rw_cfg : public default_rewriter_cfg {
        typedef std::pair<expr *, expr *> expr_pair;
        typedef obj_pair_hashtable<expr, expr> set;
        bv_util            m_util;
        set                m_add_apps;
        set                m_mul_apps;
        set                m_xor_apps;
        set                m_or_apps;
        unsigned long long m_max_memory;
        unsigned           m_max_steps;
        unsigned           m_max_args;
        
        ast_manager & m() const { return m_util.get_manager(); }
        
        rw_cfg(ast_manager & m, params_ref const & p):
            m_util(m) {
            updt_params(p);
        }

        void cleanup() {
            m_add_apps.finalize();
            m_mul_apps.finalize();
            m_or_apps.finalize();
            m_xor_apps.finalize();
        }

        void updt_params(params_ref const & p) {
            m_max_memory     = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
            m_max_steps      = p.get_uint("max_steps", UINT_MAX);
            m_max_args       = p.get_uint("max_args", 128);
        }

        bool max_steps_exceeded(unsigned num_steps) const { 
            if (memory::get_allocation_size() > m_max_memory)
                throw rewriter_exception(Z3_MAX_MEMORY_MSG);
            return num_steps > m_max_steps;
        }

        set & f2set(func_decl * f) {
            switch (f->get_decl_kind()) {
            case OP_BADD: return m_add_apps;
            case OP_BMUL: return m_mul_apps;
            case OP_BXOR: return m_xor_apps;
            case OP_BOR:  return m_or_apps;
            default:
                UNREACHABLE();
                return m_or_apps; // avoid compilation error
            }
        }

        expr * reuse(set & s, func_decl * f, expr * arg1, expr * arg2) {
            if (s.contains(expr_pair(arg1, arg2)))
                return m().mk_app(f, arg1, arg2);
            if (s.contains(expr_pair(arg2, arg1)))
                return m().mk_app(f, arg2, arg1);
            return nullptr;
        }

        struct ref_count_lt {
            bool operator()(expr * t1, expr * t2) const {
                if (t1->get_ref_count() < t2->get_ref_count())
                    return true;
                return (t1->get_ref_count() == t2->get_ref_count()) && lt(t1, t2);
            }
        };

        br_status reduce_ac_app(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
            set & s = f2set(f);

            if (num_args == 2) {
                if (!m_util.is_numeral(args[0]) && !m_util.is_numeral(args[1]))
                    s.insert(expr_pair(args[0], args[1]));
                return BR_FAILED;
            }

            ptr_buffer<expr, 128> _args;
            bool first = false;
            expr * num = nullptr;
            for (unsigned i = 0; i < num_args; i++) {
                expr * arg = args[i];
                if (num == nullptr && m_util.is_numeral(arg)) {
                    if (i == 0) first = true;
                    num = arg;
                }
                else {
                    _args.push_back(arg);
                }
            }
            num_args = _args.size();


            // std::sort(_args.begin(), _args.end(), ref_count_lt());
            // std::sort(_args.begin(), _args.end(), ast_to_lt());
            
        try_to_reuse:
            if (num_args > 1 && num_args < m_max_args) {
                for (unsigned i = 0; i < num_args - 1; i++) {
                    for (unsigned j = i + 1; j < num_args; j++) {
                        expr * r = reuse(s, f, _args[i], _args[j]);
                        if (r != nullptr) {
                            TRACE("bv_sharing_detail", tout << "reusing args: " << i << " " << j << "\n";);
                            _args[i] = r;
                            SASSERT(num_args > 1);
                            for (unsigned w = j; w < num_args - 1; w++) {
                                _args[w] = _args[w+1];
                            }
                            num_args--;
                            goto try_to_reuse;
                        }
                    }
                }
            }
            
            // TODO: 
            // some benchmarks are more efficiently solved using a tree-like structure (better sharing)
            // other benchmarks are more efficiently solved using a chain-like structure (better propagation for arguments "closer to the output").
            // 
            // One possible solution is to do a global analysis that finds a good order that increases sharing without affecting
            // propagation.
            //
            // Another cheap trick is to create an option, and try both for a small amount of time.
#if 0
            SASSERT(num_args > 0);
            if (num_args == 1) {
                result = _args[0];
            }
            else {
                // ref_count_lt is not a total order on expr's
                std::stable_sort(_args.c_ptr(), _args.c_ptr() + num_args, ref_count_lt());
                result = m().mk_app(f, _args[0], _args[1]);
                for (unsigned i = 2; i < num_args; i++) {
                    result = m().mk_app(f, result.get(), _args[i]);
                }
            }
            if (num != 0) { 
                if (first)
                    result = m().mk_app(f, num, result);
                else
                    result = m().mk_app(f, result, num);
            }
            return BR_DONE;
#else       
            // Create "tree-like circuit"
            while (true) {
                TRACE("bv_sharing_detail", tout << "tree-loop: num_args: " << num_args << "\n";);
                unsigned j  = 0;
                for (unsigned i = 0; i < num_args; i += 2, j++) {
                    if (i == num_args - 1) {
                        _args[j] = _args[i];
                    }
                    else {
                        s.insert(expr_pair(_args[i], _args[i+1]));
                        _args[j] = m().mk_app(f, _args[i], _args[i+1]);
                    }
                }
                num_args = j;
                if (num_args == 1) {
                    if (num == nullptr) {
                        result = _args[0];
                    }
                    else {
                        if (first)
                            result = m().mk_app(f, num, _args[0]);
                        else
                            result = m().mk_app(f, _args[0], num);
                    }
                    return BR_DONE;
                }
            }
#endif
        }
        
        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            if (f->get_family_id() != m_util.get_family_id())
                return BR_FAILED;
            switch (f->get_decl_kind()) {
            case OP_BADD:
            case OP_BMUL:
            case OP_BOR:
            case OP_BXOR:
                result_pr = nullptr;
                return reduce_ac_app(f, num, args, result);
            default:
                return BR_FAILED;
            }
        }
    };

    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;

        rw(ast_manager & m, params_ref const & p):
            rewriter_tpl<rw_cfg>(m, m.proofs_enabled(), m_cfg),
            m_cfg(m, p) {
        }
    };

    rw                m_rw;
    unsigned          m_num_steps = 0;
        

    params_ref m_params;

public:
    max_bv_sharing(ast_manager & m, params_ref const & p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls),
        m_params(p),
        m_rw(m, p) {
    }       

    void updt_params(params_ref const & p) override {
        m_params.append(p);
        m_rw.cfg().updt_params(m_params);
    }

    void collect_param_descrs(param_descrs & r) override {
        insert_max_memory(r);
        insert_max_steps(r);
        r.insert("max_args", CPK_UINT, 
                 "(default: 128) maximum number of arguments (per application) that will be considered by the greedy (quadratic) heuristic.");
    }

    void reduce() override {
        expr_ref   new_curr(m);
        proof_ref  new_pr(m);
        for (unsigned idx = m_qhead; idx < m_fmls.size() && !m_fmls.inconsistent(); idx++) {
            auto [curr, d] = m_fmls[idx]();
            m_rw(curr, new_curr, new_pr);
            // Proof reconstruction: new_pr = m.mk_modus_ponens(old_pr, new_pr);
            m_num_steps += m_rw.get_num_steps();            
            m_fmls.update(idx, dependent_expr(m, new_curr, d));            
        }
        m_rw.cfg().cleanup();
        advance_qhead(m_fmls.size());
    }        
};

dependent_expr_simplifier * mk_max_bv_sharing(ast_manager & m, params_ref const & p, dependent_expr_state& fmls) {
    return alloc(max_bv_sharing, m, p, fmls);    
}

