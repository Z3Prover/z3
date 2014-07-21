/**
   MaxRes (weighted) max-sat algorithm by Nina and Bacchus, AAAI 2014.
   
*/

#include "solver.h"
#include "maxsmt.h"
#include "maxres.h"
#include "ast_pp.h"
#include "mus.h"

using namespace opt;

struct maxres::imp {
    ast_manager&    m;
    solver&         s;
    expr_ref_vector m_B;
    expr_ref_vector m_D;
    expr_ref_vector m_asms;    
    app_ref_vector  m_clss;
    model_ref       m_model;
    expr_ref_vector m_soft_constraints;
    volatile bool   m_cancel;
    rational        m_lower;
    rational        m_upper;
    obj_map<expr, app*> m_asm2cls;

    imp(ast_manager& m, solver& s, expr_ref_vector& soft_constraints):
        m(m), s(s), m_B(m), m_D(m), m_asms(m), m_clss(m), m_soft_constraints(soft_constraints),
        m_cancel(false)
    {
    }

    bool is_literal(expr* l) {
        return 
            is_uninterp_const(l) ||
            m.is_not(l, l) && is_uninterp_const(l);
    }

    void add_soft(expr* e) {
        TRACE("opt", tout << mk_pp(e, m) << "\n";);
        expr_ref asum(m), fml(m);
        app_ref cls(m);
        cls = mk_cls(e);
        m_clss.push_back(cls);
        if (is_literal(e)) {
            m_asms.push_back(e);
        }
        else {
            asum = m.mk_fresh_const("soft", m.mk_bool_sort());
            fml = m.mk_iff(asum, e);
            s.assert_expr(fml);
            m_asms.push_back(asum);
        }
        m_asm2cls.insert(m_asms.back(), cls.get());
    }

    lbool operator()() {
        expr_ref fml(m);
        ptr_vector<expr> core, new_core;
        solver::scoped_push _sc(s);
        for (unsigned i = 0; i < m_soft_constraints.size(); ++i) {
            add_soft(m_soft_constraints[i].get());
        }
        m_upper = rational(m_soft_constraints.size());
        while (true) {
            TRACE("opt", 
                  display_vec(tout, m_asms.size(), m_asms.c_ptr());
                  s.display(tout);
                  tout << "\n";
                  );
            lbool is_sat = s.check_sat(m_asms.size(), m_asms.c_ptr());
            if (m_cancel) {
                return l_undef;
            }
            switch (is_sat) {
            case l_true: 
                s.get_model(m_model);
                m_upper = m_lower;
                return l_true;
            case l_undef:
                return l_undef;
            default:
                core.reset();
                s.get_unsat_core(core);
                TRACE("opt", display_vec(tout << "core: ", core.size(), core.c_ptr()););
                SASSERT(!core.empty());
                if (core.empty()) {
                    return l_false;
                }
#if 1
                // minimize core:
                mus ms(s, m);
                for (unsigned i = 0; i < core.size(); ++i) {
                    app* cls = 0; 
                    VERIFY(m_asm2cls.find(core[i], cls));
                    SASSERT(cls);
                    SASSERT(m.is_or(cls));
                    ms.add_soft(core[i], cls->get_num_args(), cls->get_args());
                }
                unsigned_vector mus_idx;
                is_sat = ms.get_mus(mus_idx);
                if (is_sat != l_true) {
                    return is_sat;
                }
                new_core.reset();
                for (unsigned i = 0; i < mus_idx.size(); ++i) {
                    new_core.push_back(core[mus_idx[i]]);
                }
                core.reset();
                core.append(new_core);
                
#endif
                TRACE("opt", display_vec(tout << "minimized core: ", core.size(), core.c_ptr()););
                max_resolve(core);
                fml = m.mk_not(m.mk_and(m_B.size(), m_B.c_ptr()));
                s.assert_expr(fml);
                m_lower += rational::one();
                break;
            }
            IF_VERBOSE(1, verbose_stream() << "(opt.max_res lower: " << m_lower << ")\n";);
        }
        return l_true;
    }

    void display_vec(std::ostream& out, unsigned sz, expr* const* args) {
        for (unsigned i = 0; i < sz; ++i) {
            out << mk_pp(args[i], m) << " ";
        }
        out << "\n";
    }

    void max_resolve(ptr_vector<expr>& core) {
        SASSERT(!core.empty());
        expr_ref fml(m), asum(m);
        app_ref cls(m);
        m_B.reset();
        m_D.reset();
        m_D.resize(core.size());
        m_B.append(core.size(), core.c_ptr());
        m_D[core.size()-1] = m.mk_false();
        //
        // d_{sz-1} := false
        // d_i := (!core_{i+1} or d_{i+1})    for i = 0...sz-2
        // soft (!d_i or core_i) 
        //
        remove_core(core);
        for (unsigned i = core.size()-1; i > 0; ) {
            --i;
            expr* d_i1 = m_D[i+1].get();
            expr* b_i = m_B[i].get();
            expr* b_i1 = m_B[i+1].get();
            m_D[i] = m.mk_implies(b_i1, d_i1);
            expr* d_i = m_D[i].get();
            asum = m.mk_fresh_const("a", m.mk_bool_sort());
            cls = m.mk_implies(d_i, b_i);
            fml = m.mk_iff(asum, cls);
            s.assert_expr(fml);
            m_asms.push_back(asum);
            cls = mk_cls(cls);
            m_clss.push_back(cls);
            m_asm2cls.insert(asum, cls);
        }
    }

    app_ref mk_cls(expr* e) {
        expr_ref_vector disj(m), todo(m);
        expr_ref f(m);
        app_ref result(m);
        expr* e1, *e2;
        todo.push_back(e);
        while (!todo.empty()) {
            f = todo.back();
            todo.pop_back();
            if (m.is_implies(f, e1, e2)) {
                todo.push_back(m.mk_not(e1));
                todo.push_back(e2);
            }
            else if (m.is_not(f, e1) && m.is_not(e1, e2)) {
                todo.push_back(e2);
            }
            else if (m.is_or(f)) {
                todo.append(to_app(f)->get_num_args(), to_app(f)->get_args());
            }
            else if (m.is_not(f, e1) && m.is_and(e1)) {
                for (unsigned i = 0; i < to_app(e1)->get_num_args(); ++i) {
                    todo.push_back(m.mk_not(to_app(e1)->get_arg(i)));
                }
            }
            else {
                disj.push_back(f);
            }
        }
        result = m.mk_or(disj.size(), disj.c_ptr());
        return result;
    }

    void remove_core(ptr_vector<expr> const& core) {
        for (unsigned i = 0; i < m_asms.size(); ++i) {
            if (core.contains(m_asms[i].get())) {
                m_asms[i] = m_asms.back();
                m_clss[i] = m_clss.back();
                m_asms.pop_back();
                m_clss.pop_back();
                --i;
            }
        }
    }

    rational get_lower() const {
        return m_lower;
    }

    rational get_upper() const {        
        return m_upper;
    }

    bool get_assignment(unsigned index) const {
        expr_ref tmp(m);
        m_model->eval(m_soft_constraints[index], tmp);
        return m.is_true(tmp);
    }
    void set_cancel(bool f) {
        m_cancel = f;
    }
    void collect_statistics(statistics& st) const {
    }
    void get_model(model_ref& mdl) {
        mdl = m_model;
    }
    void updt_params(params_ref& p) {
        ;
    }

};

maxres::maxres(ast_manager& m, solver& s, expr_ref_vector& soft_constraints) {
    m_imp = alloc(imp, m, s, soft_constraints);
}

maxres::~maxres() {
    dealloc(m_imp);
}


lbool maxres::operator()() {
    return (*m_imp)();
}

rational maxres::get_lower() const {
    return m_imp->get_lower();
}
rational maxres::get_upper() const {
    return m_imp->get_upper();
}
bool maxres::get_assignment(unsigned index) const {
    return m_imp->get_assignment(index);
}
void maxres::set_cancel(bool f) {
    m_imp->set_cancel(f);
}
void maxres::collect_statistics(statistics& st) const {
    m_imp->collect_statistics(st);
}
void maxres::get_model(model_ref& mdl) {
    m_imp->get_model(mdl);
}
void maxres::updt_params(params_ref& p) {
    m_imp->updt_params(p);
}
