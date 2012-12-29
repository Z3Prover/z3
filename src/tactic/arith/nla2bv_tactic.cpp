/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    nla2bv_tactic.cpp

Abstract:

    Convert quantified NIA problems to bounded bit-vector arithmetic problems.

Author:

    Nikolaj (nbjorner) 2011-05-3

Notes:
    Ported to tactic framework on 2012-02-28
    The original file was called qfnla2bv.cpp

--*/
#include "tactical.h"
#include "arith_decl_plugin.h"
#include "bv_decl_plugin.h"
#include "for_each_expr.h"
#include "expr_replacer.h"
#include "optional.h"
#include "bv2int_rewriter.h"
#include "bv2real_rewriter.h"
#include "extension_model_converter.h"
#include "filter_model_converter.h"
#include "bound_manager.h"
#include "obj_pair_hashtable.h"
#include "ast_smt2_pp.h"

//
// 
// 1. for each variable, determine bounds (s.t., non-negative variables
//    have unsigned bit-vectors).
// 
// 2. replace uninterpreted variables of sort int by 
//    expressions of the form +- bv2int(b) +- k
//    where k is a slack.
//   
// 3. simplify resulting assertion set to reduce occurrences of bv2int.
//    

class nla2bv_tactic : public tactic {
    class imp {
        typedef rational numeral;
        ast_manager &               m_manager; 
        bool                        m_is_sat_preserving;
        arith_util                  m_arith;
        bv_util                     m_bv;
        bv2real_util                m_bv2real;
        bv2int_rewriter_ctx         m_bv2int_ctx;
        bound_manager               m_bounds;
        expr_substitution           m_subst;
        func_decl_ref_vector        m_vars;
        expr_ref_vector             m_defs;
        expr_ref_vector             m_trail;
        unsigned                    m_num_bits;
        unsigned                    m_default_bv_size;
        ref<filter_model_converter> m_fmc;
        
    public:
        imp(ast_manager & m, params_ref const& p):
            m_manager(m), 
            m_is_sat_preserving(true), 
            m_arith(m), 
            m_bv(m), 
            m_bv2real(m, rational(p.get_uint("nla2bv_root",2)), rational(p.get_uint("nla2bv_divisor",2)), p.get_uint("nla2bv_max_bv_size", UINT_MAX)),
            m_bv2int_ctx(m, p),
            m_bounds(m), 
            m_subst(m), 
            m_vars(m), 
            m_defs(m),
            m_trail(m),
            m_fmc(0) {
            m_default_bv_size = m_num_bits = p.get_uint("nla2bv_bv_size", 4);
        }

        ~imp() {}
        
        
        void operator()(goal & g, model_converter_ref & mc) {
            TRACE("nla2bv", g.display(tout);
                  tout << "Muls: " << count_mul(g) << "\n";
                  );
            m_fmc = alloc(filter_model_converter, m_manager);
            m_bounds(g);
            collect_power2(g);
            if(!collect_vars(g)) {
                throw tactic_exception("goal is not in the fragment supported by nla2bv");
            }
            tactic_report report("nla->bv", g);
            substitute_vars(g);
            TRACE("nla2bv", g.display(tout << "substitute vars\n"););
            reduce_bv2int(g);
            reduce_bv2real(g);
            TRACE("nla2bv", g.display(tout << "after reduce\n"););
            extension_model_converter * evc = alloc(extension_model_converter, m_manager);
            mc = concat(m_fmc.get(), evc);
            for (unsigned i = 0; i < m_vars.size(); ++i) {
                evc->insert(m_vars[i].get(), m_defs[i].get());
            }
            for (unsigned i = 0; i < m_bv2real.num_aux_decls(); ++i) {
                m_fmc->insert(m_bv2real.get_aux_decl(i));
            }        
            IF_VERBOSE(TACTIC_VERBOSITY_LVL, verbose_stream() << "(nla->bv :sat-preserving " << m_is_sat_preserving << ")\n";);
            TRACE("nla2bv_verbose", g.display(tout););
            TRACE("nla2bv", tout << "Muls: " << count_mul(g) << "\n";);
            g.inc_depth();
            if (!is_sat_preserving())
                g.updt_prec(goal::UNDER);
        }
        
        bool const& is_sat_preserving() const { return m_is_sat_preserving; }
        
    private:
        void set_satisfiability_preserving(bool f) {
            m_is_sat_preserving = f;
        }
        
        void collect_power2(goal & g) {
            m_bv2int_ctx.collect_power2(g);
            obj_map<expr, expr*> const& p2 = m_bv2int_ctx.power2();
            if (p2.empty()) return;
            obj_map<expr, expr*>::iterator it = p2.begin(), end = p2.end();
            for (; it != end; ++it) {
                expr* v = it->m_value;
                unsigned num_bits = m_bv.get_bv_size(v);
                expr* w = m_bv.mk_bv2int(m_bv.mk_bv_shl(m_bv.mk_numeral(1, num_bits), v));
                m_trail.push_back(w);
                m_subst.insert(it->m_key, w);
                TRACE("nla2bv", tout << mk_ismt2_pp(it->m_key, m_manager) << " " << mk_ismt2_pp(w, m_manager) << "\n";);
            }
            // eliminate the variables that are power of two.
            substitute_vars(g);
            m_subst.reset();
        }
        
        
        // eliminate bv2int from formula
        void reduce_bv2int(goal & g) {
            bv2int_rewriter_star reduce(m_manager, m_bv2int_ctx);        
            expr_ref r(m_manager);
            for (unsigned i = 0; i < g.size(); ++i) {
                reduce(g.form(i), r);
                g.update(i, r);
            } 
            assert_side_conditions(g, m_bv2int_ctx.num_side_conditions(),
                                   m_bv2int_ctx.side_conditions());
        }
        
        // eliminate bv2real from formula
        void reduce_bv2real(goal & g) {
            bv2real_rewriter_star reduce(m_manager, m_bv2real);
            expr_ref r(m_manager);
            for (unsigned i = 0; i < g.size(); ++i) {
                reduce(g.form(i), r);
                if (m_bv2real.contains_bv2real(r)) {
                    throw tactic_exception("nla2bv could not eliminate reals");
                }
                g.update(i, r);
            } 
            assert_side_conditions(g, m_bv2real.num_side_conditions(),
                                   m_bv2real.side_conditions());
        }
        
        void assert_side_conditions(goal & g, unsigned sz, expr * const * conditions) {
            for (unsigned i = 0; i < sz; ++i) {
                g.assert_expr(conditions[i]);
                set_satisfiability_preserving(false);
            }
            TRACE("nla2bv", 
                  for (unsigned i = 0; i < sz; ++i) {
                      tout << mk_ismt2_pp(conditions[i], m_manager) << "\n";
                  });
        }
        
        // substitute variables by bit-vectors
        void substitute_vars(goal & g) {
            scoped_ptr<expr_replacer> er = mk_default_expr_replacer(m_manager);
            er->set_substitution(&m_subst);
            expr_ref r(m_manager);
            for (unsigned i = 0; i < g.size(); ++i) {
                (*er)(g.form(i), r);
                g.update(i, r);
            }        
        }
        
        // -----------------
        // collect uninterpreted variables in problem.
        // create a substitution from the variables to
        // bit-vector terms.
        //
        void add_var(app* n) {
            if (m_arith.is_int(n)) {
                add_int_var(n);
            }
            else {
                SASSERT(m_arith.is_real(n));
                add_real_var(n);
            }
        }
        
        void add_int_var(app* n) {
            expr_ref s_bv(m_manager);
            sort_ref bv_sort(m_manager);
            optional<numeral> low, up;
            numeral tmp;
            bool is_strict;
            if (m_bounds.has_lower(n, tmp, is_strict)) {
                SASSERT(!is_strict);
                low = tmp;
            }
            if (m_bounds.has_upper(n, tmp, is_strict)) {
                SASSERT(!is_strict); 
                up = tmp;
            }
            //
            // [low .. up]
            // num_bits = log2(1 + |up - low|) or m_num_bits
            //
            unsigned num_bits = m_num_bits;
            if (up && low) {
                num_bits = log2(abs(*up - *low)+numeral(1));
            }
            else {
                TRACE("nla2bv", tout << "no bounds for " << mk_ismt2_pp(n, m_manager) << "\n";);
                set_satisfiability_preserving(false);
            }
            bv_sort = m_bv.mk_sort(num_bits);
            std::string name = n->get_decl()->get_name().str();
            s_bv = m_manager.mk_fresh_const(name.c_str(), bv_sort);
            m_fmc->insert(to_app(s_bv)->get_decl());
            s_bv = m_bv.mk_bv2int(s_bv);
            if (low) {
                if (!(*low).is_zero()) {
                    //    low <= s_bv 
                    // ~>
                    //    replace s_bv by s_bv + low 
                    //    add 'low' to model for n.
                    // 
                    s_bv = m_arith.mk_add(s_bv, m_arith.mk_numeral(*low, true));
                }
            }
            else if (up) {
                //   s_bv <= up
                // ~>
                //   replace s_bv by up - s_bv
                // 
                s_bv = m_arith.mk_sub(m_arith.mk_numeral(*up, true), s_bv);
            }
            else {
                s_bv = m_arith.mk_sub(s_bv, m_arith.mk_numeral(rational::power_of_two(num_bits-1), true));
            }
            
            m_trail.push_back(s_bv);
            m_subst.insert(n, s_bv);
            m_vars.push_back(n->get_decl());
            m_defs.push_back(s_bv);
        }
        
        void add_real_var(app* n) {
            expr_ref s_bv(m_manager), s_bvr(m_manager), s(m_manager), t(m_manager);
            sort_ref bv_sort(m_manager);
            bv_sort = m_bv.mk_sort(m_num_bits);
            set_satisfiability_preserving(false);
            std::string name = n->get_decl()->get_name().str();
            s = m_manager.mk_fresh_const(name.c_str(), bv_sort);
            name += "_r";
            t = m_manager.mk_fresh_const(name.c_str(), bv_sort);
            m_fmc->insert(to_app(s)->get_decl());
            m_fmc->insert(to_app(t)->get_decl());
            s_bv = m_bv2real.mk_bv2real(s, t);
            m_trail.push_back(s_bv);
            m_subst.insert(n, s_bv);
            m_vars.push_back(n->get_decl());
            
            // use version without bv2real function.
            m_bv2real.mk_bv2real_reduced(s, t, s_bvr);
            m_defs.push_back(s_bvr);
        }
        
        
        // update number of bits based on the largest constant used.
        void update_num_bits(app* n) {
            bool is_int;
            numeral nm;
            if (m_arith.is_numeral(n, nm, is_int) && is_int) {
                nm = abs(nm);
                unsigned l = log2(nm);
                if (m_num_bits <= l) {
                    m_num_bits = l+1;
                }
            }
        }
        
        unsigned log2(rational const& n) {
            rational pow(1), two(2);
            unsigned sz = 0;
            while (pow < n) {
                ++sz;
                pow *= two;
            }
            if (sz == 0) sz = 1;
            return sz;
        }
        
        class get_uninterp_proc {
            imp& m_imp;
            ptr_vector<app> m_vars;
            bool m_in_supported_fragment;
        public:
            get_uninterp_proc(imp& s): m_imp(s), m_in_supported_fragment(true) {}
            ptr_vector<app> const& vars() { return m_vars; }
            void operator()(var * n) { 
                m_in_supported_fragment = false; 
            }
            void operator()(app* n) { 
                arith_util& a = m_imp.m_arith;
                ast_manager& m = a.get_manager();
                if (a.is_int(n) &&
                    is_uninterp_const(n)) {
                    m_vars.push_back(n);
                }
                else if (a.is_real(n) &&
                         is_uninterp_const(n)) {
                    m_vars.push_back(n);
                }
                else if (m.is_bool(n) && is_uninterp_const(n)) {
                    
                }
                else if (!(a.is_mul(n) ||
                           a.is_add(n) ||
                           a.is_sub(n) ||
                           a.is_le(n) ||
                           a.is_lt(n) ||
                           a.is_ge(n) ||
                           a.is_gt(n) ||
                           a.is_numeral(n) ||
                           a.is_uminus(n) ||
                           m_imp.m_bv2real.is_pos_le(n) ||
                           m_imp.m_bv2real.is_pos_lt(n) ||
                           n->get_family_id() == a.get_manager().get_basic_family_id())) {
                    TRACE("nla2bv", tout << "Not supported: " << mk_ismt2_pp(n, a.get_manager()) << "\n";);
                    m_in_supported_fragment = false;
                }
                m_imp.update_num_bits(n);
            }
            void operator()(quantifier* q) { 
                m_in_supported_fragment = false; 
            }
            bool is_supported() const { return m_in_supported_fragment; }
        };
        
        bool collect_vars(goal const & g) {
            get_uninterp_proc fe_var(*this);
            for_each_expr_at(fe_var, g);
            for (unsigned i = 0; i < fe_var.vars().size(); ++i) {
                add_var(fe_var.vars()[i]);
            }
            return fe_var.is_supported() && !fe_var.vars().empty();
        }
        
        class count_mul_proc {
            imp& m_imp;
            unsigned m_count;
        public:
            count_mul_proc(imp& s): m_imp(s), m_count(0) {}
            unsigned count() const { return m_count; }
            void operator()(var * n) {}
            void operator()(app* n) { 
                if (m_imp.m_arith.is_mul(n)) {
                    m_count += n->get_num_args()-1;
                }
                if (m_imp.m_bv.is_bv_mul(n)) {
                    unsigned num_vars = 0;
                    for (unsigned j = 0; j < n->get_num_args(); ++j) {
                        if (!m_imp.m_bv.is_numeral(n->get_arg(j))) {
                            ++num_vars;
                        }
                    }
                    if (num_vars > 1) {
                        m_count += num_vars - 1;
                    }
                }
            }
            void operator()(quantifier* q) {}
        };
        
        unsigned count_mul(goal const & g) {
            count_mul_proc c(*this);
            for_each_expr_at(c, g);
            return c.count();
        }
    };

    params_ref      m_params;
    imp *           m_imp;

    struct scoped_set_imp {
        nla2bv_tactic & m_owner; 
        scoped_set_imp(nla2bv_tactic & o, imp & i):
            m_owner(o) {
            #pragma omp critical (tactic_cancel)
            {
                m_owner.m_imp = &i;
            }
        }

        ~scoped_set_imp() {
            #pragma omp critical (tactic_cancel)
            {
                m_owner.m_imp = 0;
            }
        }
    };
    
public:
    nla2bv_tactic(params_ref const & p):
        m_params(p),
        m_imp(0) {
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(nla2bv_tactic, m_params);
    }

    virtual ~nla2bv_tactic() {
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
    }

    virtual void collect_param_descrs(param_descrs & r) { 
        r.insert("nla2bv_max_bv_size", CPK_UINT, "(default: inf) maximum bit-vector size used by nla2bv tactic");
        r.insert("nla2bv_bv_size", CPK_UINT, "(default: 4) default bit-vector size used by nla2bv tactic.");
        r.insert("nla2bv_root", CPK_UINT, "(default: 2) nla2bv tactic encodes reals into bit-vectors using expressions of the form a+b*sqrt(c), this parameter sets the value of c used in the encoding.");
        r.insert("nla2bv_divisor", CPK_UINT, "(default: 2) nla2bv tactic parameter.");
    }
    
    /**
       \brief Modify a goal to use bounded bit-vector 
       arithmetic in place of non-linear integer arithmetic.
       \return false if transformation is not possible.
    */
    virtual void operator()(goal_ref const & g,
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        SASSERT(g->is_well_sorted());
        fail_if_proof_generation("nla2bv", g);
        fail_if_unsat_core_generation("nla2bv", g);
        mc = 0; pc = 0; core = 0; result.reset();

        imp proc(g->m(), m_params);
        scoped_set_imp setter(*this, proc);
        proc(*(g.get()), mc);
        
        result.push_back(g.get());
        SASSERT(g->is_well_sorted());
    }
    
    virtual void cleanup(void) {
    }
};

tactic * mk_nla2bv_tactic(ast_manager & m, params_ref const & p) {
    return alloc(nla2bv_tactic, p);
}






