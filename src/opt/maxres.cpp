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
    struct info {
        app*     m_cls;
        rational m_weight;
        info(app* cls, rational const& w):
            m_cls(cls), m_weight(w) {}
        info(): m_cls(0) {}
    };
    ast_manager&     m;
    solver&          s;
    expr_ref_vector  m_B;
    expr_ref_vector  m_D;
    expr_ref_vector  m_asms;    
    model_ref        m_model;
    expr_ref_vector  m_soft_constraints;
    volatile bool    m_cancel;
    rational         m_lower;
    rational         m_upper;
    obj_map<expr, info> m_asm2info;
    ptr_vector<expr> m_new_core;
    mus              m_mus;
    expr_ref_vector  m_trail;

    imp(ast_manager& m, solver& s, expr_ref_vector& soft_constraints, vector<rational> const& weights):
        m(m), s(s), m_B(m), m_D(m), m_asms(m), m_soft_constraints(m),
        m_cancel(false),
        m_mus(s, m),
        m_trail(m)
    {
        // TBD: this introduces an assertion to solver.
        init_soft(weights, soft_constraints);
    }

    bool is_literal(expr* l) {
        return 
            is_uninterp_const(l) ||
            (m.is_not(l, l) && is_uninterp_const(l));
    }

    void add_soft(expr* e, rational const& w) {
        TRACE("opt", tout << mk_pp(e, m) << "\n";);
        expr_ref asum(m), fml(m);
        app_ref cls(m);
        cls = mk_cls(e);
        m_trail.push_back(cls);
        if (is_literal(e)) {
            asum = e;
        }
        else {
            asum = m.mk_fresh_const("soft", m.mk_bool_sort());
            fml = m.mk_iff(asum, e);
            s.assert_expr(fml);
        }
        new_assumption(asum, cls, w);
        m_upper += w;
    }

    void new_assumption(expr* e, app* cls, rational const& w) {
        info inf(cls, w);
        m_asm2info.insert(e, inf);
        m_asms.push_back(e);
        m_trail.push_back(e);        
    }

    lbool operator()() {
        expr_ref fml(m);
        ptr_vector<expr> core;
        solver::scoped_push _sc(s);
        while (true) {
            TRACE("opt", 
                  display_vec(tout, m_asms.size(), m_asms.c_ptr());
                  s.display(tout);
                  tout << "\n";
                  display(tout);
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
                is_sat = minimize_core(core);
                SASSERT(!core.empty());
                if (core.empty()) {
                    return l_false;
                }
                if (is_sat != l_true) {
                    return is_sat;
                }
                remove_core(core);
                rational w = split_core(core);
                TRACE("opt", display_vec(tout << "minimized core: ", core.size(), core.c_ptr()););
                max_resolve(core, w);
                fml = m.mk_not(m.mk_and(m_B.size(), m_B.c_ptr()));
                s.assert_expr(fml);
                m_lower += w; 
                break;
            }
            IF_VERBOSE(1, verbose_stream() << "(opt.max_res lower: " << m_lower << ")\n";);
        }
        return l_true;
    }

    lbool minimize_core(ptr_vector<expr>& core) {
        m_mus.reset();
        for (unsigned i = 0; i < core.size(); ++i) {
            app* cls = get_clause(core[i]);
            SASSERT(cls);
            SASSERT(m.is_or(cls));
            m_mus.add_soft(core[i], cls->get_num_args(), cls->get_args());
        }
        unsigned_vector mus_idx;
        lbool is_sat = m_mus.get_mus(mus_idx);
        if (is_sat != l_true) {
            return is_sat;
        }
        m_new_core.reset();
        for (unsigned i = 0; i < mus_idx.size(); ++i) {
            m_new_core.push_back(core[mus_idx[i]]);
        }
        core.reset();
        core.append(m_new_core);
        return l_true;
    }

    rational get_weight(expr* e) {
        return m_asm2info.find(e).m_weight;
    }

    app* get_clause(expr* e) {
        return m_asm2info.find(e).m_cls;
    }

    rational split_core(ptr_vector<expr> const& core) {

        // find the minimal weight:
        SASSERT(!core.empty());
        rational w = get_weight(core[0]);
        for (unsigned i = 1; i < core.size(); ++i) {
            rational w2 = get_weight(core[i]);
            if (w2 < w) {
                w = w2;
            }
        }
        // add fresh soft clauses for weights that are above w.
        for (unsigned i = 0; i < core.size(); ++i) {
            rational w2 = get_weight(core[i]);
            if (w2 > w) {
                new_assumption(core[i], get_clause(core[i]), w2 - w);
            }
        }
        return w;
    }

    void display_vec(std::ostream& out, unsigned sz, expr* const* args) {
        for (unsigned i = 0; i < sz; ++i) {
            out << mk_pp(args[i], m) << " ";
        }
        out << "\n";
    }

    void display(std::ostream& out) {
        for (unsigned i = 0; i < m_asms.size(); ++i) {
            expr* a = m_asms[i].get();
            out << mk_pp(a, m) << " : " << get_weight(a) << "\n";
        }
    }

    void max_resolve(ptr_vector<expr>& core, rational const& w) {
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
            cls = mk_cls(cls);
            m_trail.push_back(cls);
            new_assumption(asum, cls, w);
            s.assert_expr(fml);
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
                m_asms.pop_back();
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
        VERIFY(m_model->eval(m_soft_constraints[index], tmp));
        return m.is_true(tmp);
    }
    void set_cancel(bool f) {
        m_cancel = f;
        m_mus.set_cancel(f);
    }
    void collect_statistics(statistics& st) const {
    }
    void get_model(model_ref& mdl) {
        mdl = m_model;
    }
    void updt_params(params_ref& p) {
        ;
    }

    void init_soft(vector<rational> const& weights, expr_ref_vector const& soft) {
        m_soft_constraints.reset();
        m_upper.reset();
        m_lower.reset();
        m_asm2info.reset();
        m_trail.reset();
        m_soft_constraints.append(soft);
        for (unsigned i = 0; i < m_soft_constraints.size(); ++i) {
            add_soft(m_soft_constraints[i].get(), weights[i]);
        }
    }

};

maxres::maxres(ast_manager& m, solver& s, expr_ref_vector& soft_constraints, vector<rational> const& weights) {
    m_imp = alloc(imp, m, s, soft_constraints, weights);
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
