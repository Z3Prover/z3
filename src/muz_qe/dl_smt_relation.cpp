/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    dl_smt_relation.cpp

Abstract:

    Relation based on SMT signature.
    

Author:

    Nikolaj Bjorner (nbjorner) 2010-10-10

Revision History:

--*/
#include <sstream>
#include "debug.h"
#include "ast_pp.h"
#include "dl_context.h"
#include "dl_smt_relation.h"
#include "expr_abstract.h"
#include "smt_kernel.h"
#include "th_rewriter.h"
#include "qe.h"
#include "datatype_decl_plugin.h"
#include "bv_decl_plugin.h"
#include "ast_ll_pp.h"
#include "expr_context_simplifier.h"
#include "has_free_vars.h"
#include "ast_smt_pp.h"

namespace datalog {
       

    smt_relation::smt_relation(smt_relation_plugin & p, const relation_signature & s, expr* r) 
        : relation_base(p, s),
          m_rel(r, p.get_ast_manager()),
          m_bound_vars(p.get_ast_manager())
    {
        ast_manager& m = p.get_ast_manager();
        for (unsigned i = 0; m_bound_vars.size() < s.size(); ++i) {
            unsigned j = s.size() - i - 1;
            m_bound_vars.push_back(m.mk_const(symbol(j), s[j]));
        }
        SASSERT(is_well_formed());
    }    

    smt_relation::~smt_relation() {
    }

    bool smt_relation::is_well_formed() const {
        ast_manager& m = get_manager();
        ptr_vector<sort> bound_sorts;
        for (unsigned i = 0; i < m_bound_vars.size(); ++i) {
            bound_sorts.push_back(m.get_sort(m_bound_vars[i]));
        }
        return is_well_formed_vars(bound_sorts, get_relation());
    }

    void smt_relation::instantiate(expr* r, expr_ref& result) const {
        ast_manager& m = get_manager();
        var_subst subst(m);
        ptr_vector<sort> bound_sorts;
        for (unsigned i = 0; i < m_bound_vars.size(); ++i) {
            bound_sorts.push_back(m.get_sort(m_bound_vars[i]));
        }
        TRACE("smt_relation", 
            tout << mk_ll_pp(r, m) << "\n";
            for (unsigned i = 0; i < bound_sorts.size(); ++i) {
                tout << mk_pp(bound_sorts[i], m) << " ";       
            }
            tout << "\n";
        );
        SASSERT(is_well_formed_vars(bound_sorts, r));
        
        subst(r, m_bound_vars.size(), m_bound_vars.c_ptr(), result);
    }

    void smt_relation::mk_abstract(expr* r, expr_ref& result) const {
        ast_manager& m = get_manager();
        TRACE("smt_relation", tout << mk_ll_pp(r, m) << "\n";);
        expr_abstract(m, 0, m_bound_vars.size(), m_bound_vars.c_ptr(), r, result);
        TRACE("smt_relation", tout << mk_ll_pp(result, m) << "\n";);        
        ptr_vector<sort> bound_sorts;
        for (unsigned i = 0; i < m_bound_vars.size(); ++i) {
            bound_sorts.push_back(m.get_sort(m_bound_vars[i]));
        }
        SASSERT(is_well_formed_vars(bound_sorts, r));
    }

    void smt_relation::set_relation(expr* r) {
        m_rel = r;
        is_well_formed();
    }

    void smt_relation::add_relation(expr* s) {
        ast_manager& m = get_manager();
        m_rel = m.mk_or(m_rel, s);
        is_well_formed();
    }

    void smt_relation::filter_relation(expr* s) {
        ast_manager& m = get_manager();
        m_rel = m.mk_and(m_rel, s);
        is_well_formed();
    }

    expr* smt_relation::get_relation() const { 
        return m_rel.get();
    }

    void smt_relation::simplify(expr_ref& fml) const {
        th_rewriter rw(get_manager());
        rw(fml);     
    }

    bool smt_relation::empty() const {
        ast_manager& m = get_manager();
        expr* r = get_relation();
        if (m.is_true(r)) {
            return false;
        }
        if (m.is_false(r)) {
            return true;
        }
        IF_VERBOSE(10, verbose_stream() << "Checking emptiness...\n"; );

        front_end_params& params = get_plugin().get_fparams();
        flet<bool> flet2(params.m_der, true);
        smt::kernel ctx(m, params);
        expr_ref tmp(m); 
        instantiate(r, tmp);
        ctx.assert_expr(tmp);
        if (get_plugin().get_fparams().m_dump_goal_as_smt) {
            static unsigned n = 0;
            std::ostringstream strm;
            strm << "File" << n << ".smt2";
            std::ofstream out(strm.str().c_str());
            ast_smt_pp pp(m);
            pp.display_smt2(out, tmp);
            ++n;
        }
        return l_false == ctx.check();
    }
    
    void smt_relation::add_fact(const relation_fact & f) {
        SASSERT(f.size() == size());
        ast_manager& m = get_manager();
        expr_ref_vector eqs(m);
        for (unsigned i = 0; i < f.size(); ++i) {
            eqs.push_back(m.mk_eq(m.mk_var(i,m.get_sort(f[i])), f[i]));
        }
        expr_ref e1(m.mk_and(eqs.size(), eqs.c_ptr()), m);
        add_relation(e1);
    }


    bool smt_relation::contains_fact(const relation_fact & f) const {
        ast_manager& m = get_manager();
        expr_ref_vector eqs(m);
        expr_ref cond(m);
        for (unsigned i = 0; i < f.size(); ++i) {
            eqs.push_back(m.mk_eq(m.mk_var(i,m.get_sort(f[i])), f[i]));
        }
        cond = m.mk_and(eqs.size(), eqs.c_ptr());
        return const_cast<smt_relation*>(this)->contains(cond);
    }

    //
    // facts in Rel iff
    // facts => Rel iff 
    // facts & not Rel is unsat
    // 
    bool smt_relation::contains(expr* facts) {
        ast_manager& m = get_manager();
        expr_ref fml_free(m), fml_inst(m);
        fml_free = m.mk_and(facts, m.mk_not(get_relation()));
        instantiate(fml_free, fml_inst);
        front_end_params& params = get_plugin().get_fparams();
        flet<bool> flet0(params.m_quant_elim, true);
        flet<bool> flet1(params.m_nnf_cnf, false);
        flet<bool> flet2(params.m_der, true);
        smt::kernel ctx(m, params);
        ctx.assert_expr(fml_inst);
        lbool result = ctx.check();
        TRACE("smt_relation",
                display(tout);
                tout << mk_pp(facts, m) << "\n";
                tout << ((result == l_false)?"true":"false") << "\n";);
        return result == l_false;        
    }
    
    smt_relation * smt_relation::clone() const {
        return alloc(smt_relation, get_plugin(), get_signature(), get_relation());
    }

    smt_relation * smt_relation::complement(func_decl* p) const {
        ast_manager& m = get_manager();
        smt_relation* result = alloc(smt_relation, get_plugin(), get_signature(), m.mk_not(get_relation()));
        TRACE("smt_relation", 
            display(tout<<"src:\n");
            result->display(tout<<"complement:\n"););
        return result;
    }
            
    void smt_relation::display(std::ostream & out) const {
        if (is_finite_domain()) {
            display_finite(out);    
        }
        else {
            out << mk_ll_pp(get_relation(), get_manager()) << "\n";
        }
    }
    
    smt_relation_plugin & smt_relation::get_plugin() const {
        return static_cast<smt_relation_plugin &>(relation_base::get_plugin());
    }

    bool smt_relation::is_finite_domain() const {
        relation_signature const& sig = get_signature();
        for (unsigned i = 0; i < sig.size(); ++i) {
            if (!get_plugin().is_finite_domain(sig[i])) {
                return false;
            }
        }
        return true;
    }


    void smt_relation::display_finite(std::ostream & out) const {
        ast_manager& m = get_manager();
        front_end_params& params = get_plugin().get_fparams();
        expr* r = get_relation();
        expr_ref tmp(m);
        expr_ref_vector values(m), eqs(m);
        unsigned num_vars = m_bound_vars.size();
        values.resize(num_vars);
        eqs.resize(num_vars);
        instantiate(r, tmp);
        flet<bool> flet4(params.m_model, true);
        smt::kernel ctx(m, params);
        ctx.assert_expr(tmp);
        
        while (true) {
            lbool is_sat = ctx.check();
            if (is_sat == l_false) {
                break;
            }
            model_ref mod;
            ctx.get_model(mod);
            for (unsigned i = 0; i < num_vars; ++i) {    
                mod->eval(m_bound_vars[i], tmp, true);
                values[i] = tmp;
                eqs[i] = m.mk_eq(values[i].get(), m_bound_vars[i]);
                
            }
            out << " (";
            for (unsigned i = 0; i < num_vars; ++i) {
                unsigned j = num_vars - 1 - i;
                out << mk_pp(values[j].get(), m);
                if (i + 1 < num_vars) {
                    out << " ";
                }
            }
            out << ")\n";
            tmp = m.mk_not(m.mk_and(num_vars, eqs.c_ptr()));
            ctx.assert_expr(tmp);
        }
    }

    // -----------------------------------
    //
    // smt_relation_plugin
    //
    // -----------------------------------


    smt_relation_plugin::smt_relation_plugin(relation_manager & m) 
        : relation_plugin(smt_relation_plugin::get_name(), m), m_counter(0) {}


    relation_base * smt_relation_plugin::mk_empty(const relation_signature & s) {
        return alloc(smt_relation, *this, s, get_ast_manager().mk_false());
    }
    

    class smt_relation_plugin::join_fn : public convenient_relation_join_fn {
        smt_relation_plugin& m_plugin;
        expr_ref_vector      m_conjs;
    public:
        join_fn(smt_relation_plugin& p, const relation_signature & o1_sig, const relation_signature & o2_sig, unsigned col_cnt,
                const unsigned * cols1, const unsigned * cols2) 
            : convenient_relation_join_fn(o1_sig, o2_sig, col_cnt, cols1, cols2),
              m_plugin(p), 
              m_conjs(p.get_ast_manager()) {
            ast_manager& m = p.get_ast_manager();
            unsigned sz = m_cols1.size();
            for (unsigned i = 0; i < sz; ++i) {
                unsigned col1 = m_cols1[i];
                unsigned col2 = m_cols2[i];                
                var* v1 = m.mk_var(col1, o1_sig[col1]);
                var* v2 = m.mk_var(col2 + o1_sig.size(), o2_sig[col2]);
                m_conjs.push_back(m.mk_eq(v1, v2));
            }            
        }

        virtual relation_base * operator()(const relation_base & r1, const relation_base & r2) {
            ast_manager& m = m_plugin.get_ast_manager();
            expr_ref e2(m), res(m);
            shift_vars sh(m);
            sh(get(r2).get_relation(), r1.get_signature().size(), e2);
            m_conjs.push_back(get(r1).get_relation());
            m_conjs.push_back(e2);
            res = m.mk_and(m_conjs.size(), m_conjs.c_ptr());
            m_conjs.pop_back();
            m_conjs.pop_back();            
            smt_relation* result = alloc(smt_relation, m_plugin, get_result_signature(), res);
            TRACE("smt_relation",                   
                  get(r1).display(tout << "src1:\n");
                  get(r2).display(tout << "src2:\n");
                  for (unsigned i = 0; i < m_conjs.size(); ++i) {
                      tout << m_cols1[i] << " = " << m_cols2[i] << " -- ";
                      tout << mk_pp(m_conjs[i].get(), m) << "\n";
                  }
                  result->display(tout << "dst:\n");
                  );
            return result;
        }
    };

    relation_join_fn * smt_relation_plugin::mk_join_fn(const relation_base & r1, const relation_base & r2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
        if (!check_kind(r1) || !check_kind(r2)) {
            return 0;
        }
        return alloc(join_fn, *this, r1.get_signature(), r2.get_signature(), col_cnt, cols1, cols2);
    }

    class smt_relation_plugin::project_fn : public convenient_relation_project_fn {
        smt_relation_plugin& m_plugin;
        expr_ref_vector      m_subst;
        sort_ref_vector      m_sorts;
        svector<symbol>      m_names;
    public:
        project_fn(smt_relation_plugin& p,
                   const relation_signature & orig_sig, unsigned removed_col_cnt, const unsigned * removed_cols) 
            : convenient_relation_project_fn(orig_sig, removed_col_cnt, removed_cols),
              m_plugin(p),
              m_subst(p.get_ast_manager()),
              m_sorts(p.get_ast_manager()) {
            ast_manager& m = p.get_ast_manager();
            unsigned_vector const& cols = m_removed_cols;
            unsigned num_cols = cols.size();
            
            unsigned lo = 0, hi = num_cols;
            for (unsigned i = 0, c = 0; i < orig_sig.size(); ++i) {
                SASSERT(c <= num_cols);
                if (c == num_cols) {
                    SASSERT(lo == num_cols); 
                    m_subst.push_back(m.mk_var(hi, orig_sig[i]));
                    ++hi;
                    continue;
                }
                SASSERT(c < num_cols);
                unsigned col = cols[c];
                SASSERT(i <= col);
                if (i == col) {
                    m_names.push_back(symbol(p.fresh_name()));
                    m_sorts.push_back(orig_sig[col]);
                    m_subst.push_back(m.mk_var(lo, orig_sig[i]));
                    ++lo;
                    ++c;
                    continue;
                }
                m_subst.push_back(m.mk_var(hi, orig_sig[i]));
                ++hi;
            }
            m_subst.reverse();
            m_sorts.reverse();
            m_names.reverse();
        }

        virtual relation_base * operator()(const relation_base & r) {
            ast_manager& m = m_plugin.get_ast_manager();            
            expr_ref tmp1(m), tmp2(m);
            var_subst subst(m);
            smt_relation* result = 0;
            tmp1 = get(r).get_relation();
            subst(tmp1, m_subst.size(), m_subst.c_ptr(), tmp2);
            tmp2 = m.mk_exists(m_sorts.size(), m_sorts.c_ptr(), m_names.c_ptr(), tmp2);            
            result = alloc(smt_relation, m_plugin, get_result_signature(), tmp2);
            TRACE("smt_relation",
                  tout << "Signature: ";
                  for (unsigned i = 0; i < r.get_signature().size(); ++i) {
                      tout << mk_pp(r.get_signature()[i], m) << " ";
                  }
                  tout << "Remove: ";
                  for (unsigned i = 0; i < m_removed_cols.size(); ++i) {
                      tout << m_removed_cols[i] << " ";
                  }
                  tout << "\n";
                  tout << "Subst: ";
                  for (unsigned i = 0; i < m_subst.size(); ++i) {
                      tout << mk_pp(m_subst[i].get(), m) << " ";
                  }
                  tout << "\n";
                  get(r).display(tout);
                  tout << " --> \n";
                  result->display(tout););
            return result;
        }
    };

    relation_transformer_fn * smt_relation_plugin::mk_project_fn(const relation_base & r, 
            unsigned col_cnt, const unsigned * removed_cols) {
        return alloc(project_fn, *this, r.get_signature(), col_cnt, removed_cols);
    }


    class smt_relation_plugin::rename_fn : public convenient_relation_rename_fn {
        smt_relation_plugin& m_plugin;
        expr_ref_vector      m_subst;
    public:
        rename_fn(smt_relation_plugin& p, const relation_signature & orig_sig, unsigned cycle_len, const unsigned * cycle) 
            : convenient_relation_rename_fn(orig_sig, cycle_len, cycle),
              m_plugin(p),
              m_subst(p.get_ast_manager()) {

            ast_manager& m = p.get_ast_manager();
            for (unsigned i = 0; i < orig_sig.size(); ++i) {
                m_subst.push_back(m.mk_var(i, orig_sig[i]));
            }
            unsigned col1, col2;
            for (unsigned i = 0; i +1 < cycle_len; ++i) {
                col1 = cycle[i];
                col2 = cycle[i+1];
                m_subst[col2] = m.mk_var(col1, orig_sig[col2]);
            }
            col1 = cycle[cycle_len-1];
            col2 = cycle[0];
            m_subst[col2] = m.mk_var(col1, orig_sig[col2]);
            m_subst.reverse();
        }

        virtual relation_base * operator()(const relation_base & r) {
            ast_manager& m = m_plugin.get_ast_manager();
            expr_ref res(m);
            var_subst subst(m);
            subst(get(r).get_relation(), m_subst.size(), m_subst.c_ptr(), res);
            TRACE("smt_relation3", 
                    tout << "cycle: ";
                    for (unsigned i = 0; i < m_cycle.size(); ++i) {
                        tout << m_cycle[i] << " ";
                    }
                    tout << "\n";
                    tout << "old_sig: ";
                    for (unsigned i = 0; i < r.get_signature().size(); ++i) {
                        tout << mk_pp(r.get_signature()[i], m) << " ";
                    }                    
                    tout << "\n";
                    tout << "new_sig: ";
                    for (unsigned i = 0; i < get_result_signature().size(); ++i) {
                        tout << mk_pp(get_result_signature()[i], m) << " ";
                    }                    
                    tout << "\n";
                    tout << "subst: ";
                    for (unsigned i = 0; i < m_subst.size(); ++i) {
                        tout << mk_pp(m_subst[i].get(), m) << " ";
                    }                    
                    tout << "\n";
                    get(r).display(tout << "src:\n");
                    tout << "dst:\n" << mk_ll_pp(res, m) << "\n";
                    );
            smt_relation* result = alloc(smt_relation, m_plugin, get_result_signature(), res);

            return result;
        }
    };

    relation_transformer_fn * smt_relation_plugin::mk_rename_fn(const relation_base & r, 
            unsigned cycle_len, const unsigned * permutation_cycle) {
        if(!check_kind(r)) {
            return 0;
        }
        return alloc(rename_fn, *this, r.get_signature(), cycle_len, permutation_cycle);
    }


    class smt_relation_plugin::union_fn : public relation_union_fn {
        smt_relation_plugin& m_plugin;
        
    public:
        union_fn(smt_relation_plugin& p) :
            m_plugin(p) {            
        }

        virtual void operator()(relation_base & r, const relation_base & src, relation_base * delta) {
            ast_manager& m = m_plugin.get_ast_manager();     
            expr* srcE = get(src).get_relation();
            TRACE("smt_relation",
                    tout << "dst:\n";
                    get(r).display(tout);
                    tout << "src:\n";
                    get(src).display(tout););

            SASSERT(get(src).is_well_formed());
            SASSERT(get(r).is_well_formed());

            if (delta) {
                //
                // delta(a) <- 
                //      exists x . srcE(a, x) & not rE(a, y)


                expr_ref rInst(m), srcInst(m), tmp(m), tmp1(m);
                expr_ref notR(m), srcGround(m);
                front_end_params& fparams = get(r).get_plugin().get_fparams();
                params_ref const& params = get(r).get_plugin().get_params();
                
                get(r).instantiate(get(r).get_relation(), rInst);
                get(src).instantiate(get(src).get_relation(), srcInst);
                qe::expr_quant_elim_star1 qe(m, fparams);                

                IF_VERBOSE(10, verbose_stream() << "Computing delta...\n"; );
                     
                if (params.get_bool(":smt-relation-ground-recursive", false)) { 
                    // ensure R is ground. Simplify S using assumption not R
                    if (!is_ground(rInst)) {
                        proof_ref pr(m);
                        qe(rInst, tmp, pr);
                        rInst = tmp;
                        get(r).set_relation(rInst);
                    }
                    SASSERT(is_ground(rInst));
                    notR = m.mk_not(rInst);
                    qe.reduce_with_assumption(notR, srcInst, tmp);   
                    SASSERT(is_ground(tmp));
                }
                else {
                    // Simplify not R usng assumption Exists x . S.
                    expr_ref srcGround(srcInst, m);
                    app_ref_vector srcVars(m);
                    qe::hoist_exists(srcGround, srcVars);
                    SASSERT(is_ground(srcGround));
                    notR = m.mk_not(rInst);
                    qe.reduce_with_assumption(srcGround, notR, tmp1);
                    tmp = m.mk_and(srcInst, tmp1);                             
                    SASSERT(!has_free_vars(tmp));
                    TRACE("smt_relation", 
                        tout << "elim_exists result:\n" << mk_ll_pp(tmp, m) << "\n";);   
                }

                SASSERT(!has_free_vars(tmp)); 
                get(r).simplify(tmp);
            
                get(src).mk_abstract(tmp, tmp1);
                TRACE("smt_relation", tout << "abstracted:\n"; tout << mk_ll_pp(tmp1, m) << "\n";);  
                get(*delta).set_relation(tmp1);
                get(r).add_relation(tmp1); 
            }
            else {
                get(r).add_relation(srcE);                
            }
            TRACE("smt_relation", get(r).display(tout << "dst':\n"););
        }
    };

    relation_union_fn * smt_relation_plugin::mk_union_fn(const relation_base & tgt, const relation_base & src,
        const relation_base * delta) {
        if (!check_kind(tgt) || !check_kind(src) || (delta && !check_kind(*delta))) {
            return 0;
        }
        return alloc(union_fn, *this);
    }

    relation_union_fn * smt_relation_plugin::mk_widen_fn(const relation_base & tgt, const relation_base & src,
        const relation_base * delta) {
        if (!check_kind(tgt) || !check_kind(src) || (delta && !check_kind(*delta))) {
            return 0;
        }
        return alloc(union_fn, *this);
    }

    class smt_relation_plugin::filter_interpreted_fn : public relation_mutator_fn {
        smt_relation_plugin& m_plugin;
        app_ref              m_condition;
    public:
        filter_interpreted_fn(smt_relation_plugin& p, app * condition) 
            : m_plugin(p),
              m_condition(condition, p.get_ast_manager()) {
        }

        virtual void operator()(relation_base & r) {
            SASSERT(m_plugin.check_kind(r));
            get(r).filter_relation(m_condition);
            TRACE("smt_relation",
                    tout << mk_pp(m_condition, m_plugin.get_ast_manager()) << "\n";
                    get(r).display(tout);
            );
        }
    };

    relation_mutator_fn * smt_relation_plugin::mk_filter_interpreted_fn(const relation_base & r, app * condition) {
        if(!check_kind(r)) {
            return 0;
        }
        return alloc(filter_interpreted_fn, *this, condition);
    }

    relation_mutator_fn * smt_relation_plugin::mk_filter_equal_fn(const relation_base & r, 
        const relation_element & value, unsigned col) {
        if(!check_kind(r)) {
            return 0;
        }
        ast_manager& m = get_ast_manager();
        app_ref condition(m);
        expr_ref var(m.mk_var(col, r.get_signature()[col]), m);
        condition = m.mk_eq(var, value);
        return mk_filter_interpreted_fn(r, condition);
    }

    class smt_relation_plugin::filter_identical_fn : public relation_mutator_fn {
        smt_relation_plugin& m_plugin;
        expr_ref             m_condition;
    public:
        filter_identical_fn(smt_relation_plugin& p, const relation_signature & sig, unsigned col_cnt, const unsigned * identical_cols) 
            : m_plugin(p),
              m_condition(p.get_ast_manager()) {
            if (col_cnt <= 1) {
                return;
            }
            ast_manager& m = p.get_ast_manager();
            unsigned col = identical_cols[0];
            expr_ref v0(m.mk_var(col, sig[col]), m);
            expr_ref_vector eqs(m);
            for (unsigned i = 1; i < col_cnt; ++i) {
                col = identical_cols[i];
                eqs.push_back(m.mk_eq(v0, m.mk_var(col, sig[col])));
            }
            m_condition = m.mk_and(eqs.size(), eqs.c_ptr());
        }

        virtual void operator()(relation_base & r) {
            get(r).filter_relation(m_condition);
            TRACE("smt_relation",
                    tout << mk_pp(m_condition, m_plugin.get_ast_manager()) << "\n";
                    get(r).display(tout);
            );
        }
    };

    relation_mutator_fn * smt_relation_plugin::mk_filter_identical_fn(const relation_base & r, 
        unsigned col_cnt, const unsigned * identical_cols) {
        if (!check_kind(r)) {
            return 0;
        }
        return alloc(filter_identical_fn, *this, r.get_signature(), col_cnt, identical_cols);
    }


    class smt_relation_plugin::negation_filter_fn : public convenient_relation_negation_filter_fn {
        smt_relation_plugin& m_plugin;
        expr_ref_vector      m_conjs;
    public:
        negation_filter_fn(smt_relation_plugin& p, 
                           const relation_base & tgt, const relation_base & neg_t, 
                           unsigned joined_col_cnt, const unsigned * t_cols, const unsigned * negated_cols) : 
            convenient_negation_filter_fn(tgt, neg_t, joined_col_cnt, t_cols, negated_cols),
            m_plugin(p),
            m_conjs(p.get_ast_manager()) {
            ast_manager& m = p.get_ast_manager();
            unsigned sz = m_cols1.size();
            for (unsigned i = 0; i < sz; ++i) {
                unsigned col1 = m_cols1[i];
                unsigned col2 = m_cols2[i];                
                var* v1 = m.mk_var(col1, tgt.get_signature()[col1]);
                var* v2 = m.mk_var(col2, neg_t.get_signature()[col2]);
                m_conjs.push_back(m.mk_eq(v1, v2));
            }            
        }

        void operator()(relation_base & t, const relation_base & negated_obj) {
            // TBD: fixme.
            NOT_IMPLEMENTED_YET();
            ast_manager& m = m_plugin.get_ast_manager();
            expr_ref res(m), e2(m);
            shift_vars sh(m);
            sh(get(negated_obj).get_relation(), t.get_signature().size(), e2);
            m_conjs.push_back(get(t).get_relation());
            m_conjs.push_back(m.mk_not(e2));
            res = m.mk_and(m_conjs.size(), m_conjs.c_ptr());
            m_conjs.pop_back();
            m_conjs.pop_back();
            // TBD: free variables in negation?
        }
    };

    relation_intersection_filter_fn * smt_relation_plugin::mk_filter_by_negation_fn(const relation_base & t, 
            const relation_base & negated_obj, unsigned joined_col_cnt, 
            const unsigned * t_cols, const unsigned * negated_cols) {
        if (!check_kind(t) || !check_kind(negated_obj)) {
            return 0;
        }
        return alloc(negation_filter_fn, *this, t, negated_obj, joined_col_cnt, t_cols, negated_cols);
    }


    smt_relation& smt_relation_plugin::get(relation_base& r) { return dynamic_cast<smt_relation&>(r); }

    smt_relation const & smt_relation_plugin::get(relation_base const& r) { return dynamic_cast<smt_relation const&>(r); }

    bool smt_relation_plugin::can_handle_signature(relation_signature const& sig) {
        // TBD: refine according to theories handled by quantifier elimination
        return get_manager().is_non_explanation(sig);
    }

    // TBD: when relations are finite domain, they also support table iterators.

    symbol smt_relation_plugin::fresh_name() {
        return symbol(m_counter++);
    }

    front_end_params& smt_relation_plugin::get_fparams() { 
        return const_cast<front_end_params&>(get_manager().get_context().get_fparams()); 
    }

    params_ref const& smt_relation_plugin::get_params() { 
        return get_manager().get_context().get_params(); 
    }

    bool smt_relation_plugin::is_finite_domain(sort *s) const {
        ast_manager& m = get_ast_manager();
        if (m.is_bool(s)) {
            return true;
        }
        bv_util bv(m);
        if (bv.is_bv_sort(s)) {
            return true;
        }
        datatype_util dt(m);
        if (dt.is_datatype(s) && !dt.is_recursive(s)) {
            ptr_vector<func_decl> const& constrs = *dt.get_datatype_constructors(s);
            for (unsigned i = 0; i < constrs.size(); ++i) {
                func_decl* f = constrs[i];
                for (unsigned j = 0; j < f->get_arity(); ++j) {
                    if (!is_finite_domain(f->get_domain(j))) {
                        return false;
                    }
                }
            }
            return true;
        }
        return false;
    }
};
    
