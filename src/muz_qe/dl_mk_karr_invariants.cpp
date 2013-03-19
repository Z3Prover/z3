/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_mk_karr_invariants.cpp

Abstract:

    Extract integer linear invariants.

    The linear invariants are extracted according to Karr's method.
    A short description is in 
    Nikolaj Bjørner, Anca Browne and Zohar Manna. Automatic Generation 
    of Invariants and Intermediate Assertions, in CP 95.

    The algorithm is here adapted to Horn clauses.
    The idea is to maintain two data-structures for each recursive relation.
    We call them R and RD
    - R  - set of linear congruences that are true of R.
    - RD - the dual basis of of solutions for R.

    RD is updated by accumulating basis vectors for solutions 
    to R (the homogeneous dual of R)
    R is updated from the inhomogeneous dual of RD.

Author:

    Nikolaj Bjorner (nbjorner) 2013-03-09

Revision History:
           
--*/

#include"dl_mk_karr_invariants.h"

namespace datalog {

    mk_karr_invariants::mk_karr_invariants(context & ctx, unsigned priority):
        rule_transformer::plugin(priority, false),
        m_ctx(ctx),
        m(ctx.get_manager()), 
        rm(ctx.get_rule_manager()),
        a(m) {
    }

    mk_karr_invariants::~mk_karr_invariants() {
        obj_map<func_decl, matrix*>::iterator it = m_constraints.begin(), end = m_constraints.end();
        for (; it != end; ++it) {
            dealloc(it->m_value);
        }
        it = m_dual_constraints.begin();
        end = m_dual_constraints.end();
        for (; it != end; ++it) {
            dealloc(it->m_value);
        }
    }

    mk_karr_invariants::matrix& mk_karr_invariants::matrix::operator=(matrix const& other) {
        reset();
        append(other);
        return *this;
    }

    void mk_karr_invariants::matrix::display(std::ostream& out) const {
        for (unsigned i = 0; i < A.size(); ++i) {
            for (unsigned j = 0; j < A[i].size(); ++j) {
                out << A[i][j] << " ";
            }
            out << (eq[i]?" = ":" >= ") << -b[i] << "\n";
        }
    }

    bool mk_karr_invariants::is_linear(expr* e, vector<rational>& row, rational& b, rational const& mul) {
        if (!a.is_int(e)) {
            return false;
        }
        if (is_var(e)) {
            row[to_var(e)->get_idx()] += mul;
            return true;
        }
        if (!is_app(e)) {
            return false;
        }
        rational n;
        if (a.is_numeral(e, n)) {
            b += mul*n;
            return true;
        }
        if (a.is_add(e)) {
            for (unsigned i = 0; i < to_app(e)->get_num_args(); ++i) {
                if (!is_linear(to_app(e)->get_arg(i), row, b, mul)) {
                    return false;
                }
            }
            return true;
        }
        expr* e1, *e2;
        if (a.is_sub(e, e1, e2)) {
            return is_linear(e1, row, b, mul) && is_linear(e2, row, b, -mul);
        }
        if (a.is_mul(e, e1, e2) && a.is_numeral(e1, n)) {
            return is_linear(e2, row, b, mul*n);
        }
        if (a.is_mul(e, e1, e2) && a.is_numeral(e2, n)) {
            return is_linear(e1, row, b, mul*n);
        }
        if (a.is_uminus(e, e1)) {
            return is_linear(e1, row, b, -mul);
        }
        return false;        
    }

    mk_karr_invariants::matrix* mk_karr_invariants::get_constraints(func_decl* p) {
        matrix* result = 0;
        m_constraints.find(p, result);
        return result;
    }

    mk_karr_invariants::matrix& mk_karr_invariants::get_dual_constraints(func_decl* p) {
        matrix* result = 0;
        if (!m_dual_constraints.find(p, result)) {
            result = alloc(matrix);
            m_dual_constraints.insert(p, result);
        }
        return *result;
    }

    bool mk_karr_invariants::is_eq(expr* e, var*& v, rational& n) {
        expr* e1, *e2;
        if (!m.is_eq(e, e1, e2)) {
            return false;
        }
        if (!is_var(e1)) {
            std::swap(e1, e2);
        }
        if (!is_var(e1)) {
            return false;
        }
        v = to_var(e1);
        if (!a.is_numeral(e2, n)) {
            return false;
        }
        return true;
    }
    
    bool mk_karr_invariants::get_transition_relation(rule const& r, matrix& M) {
        unsigned num_vars = rm.get_counter().get_max_rule_var(r)+1;
        unsigned arity = r.get_decl()->get_arity();
        unsigned num_columns = arity + num_vars;        
        unsigned utsz = r.get_uninterpreted_tail_size();
        unsigned tsz  = r.get_tail_size();
        M.reset();
        
        for (unsigned i = 0; i < utsz; ++i) {
            matrix const* Mp = get_constraints(r.get_decl(i));
            if (!Mp) {
                return false;
            }
            TRACE("dl", Mp->display(tout << "Intersect\n"););
            intersect_matrix(r.get_tail(i), *Mp, num_columns, M);
        }

        rational one(1), mone(-1);
        expr* e1, *e2, *en;
        var* v, *w;
        rational n1, n2;
        expr_ref_vector conjs(m);
        for (unsigned i = utsz; i < tsz; ++i) {
            conjs.push_back(r.get_tail(i));
        }
        datalog::flatten_and(conjs);

        for (unsigned i = 0; i < conjs.size(); ++i) {
            expr* e = conjs[i].get();
            rational b(0);
            vector<rational> row;
            row.resize(num_columns, rational(0));
            bool processed = true;
            if (m.is_eq(e, e1, e2) && is_linear(e1, row, b, one) && is_linear(e2, row, b, mone)) {
                M.A.push_back(row);
                M.b.push_back(b);
                M.eq.push_back(true);
            }
            else if ((a.is_le(e, e1, e2) || a.is_ge(e, e2, e1)) && is_linear(e1, row, b, mone) && is_linear(e2, row, b, one)) {
                M.A.push_back(row);
                M.b.push_back(b);
                M.eq.push_back(false);
            }
            else if ((a.is_lt(e, e1, e2) || a.is_gt(e, e2, e1)) && is_linear(e1, row, b, mone) && is_linear(e2, row, b, one)) {
                M.A.push_back(row);
                M.b.push_back(b + rational(1));
                M.eq.push_back(false);
            }
            else if (m.is_not(e, en) && (a.is_lt(en, e2, e1) || a.is_gt(en, e1, e2)) && is_linear(e1, row, b, mone) && is_linear(e2, row, b, one)) {
                M.A.push_back(row);
                M.b.push_back(b);
                M.eq.push_back(false);
            }
            else if (m.is_not(e, en) && (a.is_le(en, e2, e1) || a.is_ge(en, e1, e2)) && is_linear(e1, row, b, mone) && is_linear(e2, row, b, one)) {
                M.A.push_back(row);
                M.b.push_back(b + rational(1));
                M.eq.push_back(false);
            }
            else if (m.is_or(e, e1, e2) && is_eq(e1, v, n1) && is_eq(e2, w, n2) && v == w) {
                if (n1 > n2) {
                    std::swap(n1, n2);
                }
                SASSERT(n1 <= n2);
                row[v->get_idx()] = rational(1);
                // v - n1 >= 0
                M.A.push_back(row);
                M.b.push_back(-n1);
                M.eq.push_back(false);
                // -v + n2 >= 0
                row[v->get_idx()] = rational(-1);
                M.A.push_back(row);
                M.b.push_back(n2);
                M.eq.push_back(false);
            }
            else {
                processed = false;
            }
            TRACE("dl", tout << (processed?"+ ":"- ") << mk_pp(e, m) << "\n";);
        }
        // intersect with the head predicate.
        app* head = r.get_head();
        unsigned sz0 = M.A.size();
        for (unsigned i = 0; i < arity; ++i) {
            rational n;
            expr* arg = head->get_arg(i);
            if (!a.is_int(arg)) { 
                // no-op
            }
            else if (is_var(arg)) {
                vector<rational> row;
                row.resize(num_columns, rational(0));
                unsigned idx = to_var(arg)->get_idx();
                row[idx] = rational(-1);
                row[num_vars + i] = rational(1);
                M.A.push_back(row);
                M.b.push_back(rational(0));
                M.eq.push_back(true);
            }
            else if (a.is_numeral(arg, n)) {
                vector<rational> row;
                row.resize(num_columns, rational(0));
                row[num_vars + i] = rational(1);
                M.A.push_back(row);
                M.b.push_back(-n);
                M.eq.push_back(true);
            }
            else {
                UNREACHABLE();
            }
        }
        if (M.A.size() == sz0) {
            return false;
        }

        TRACE("dl", M.display(tout << r.get_decl()->get_name() << "\n"););
        matrix MD;
        dualizeI(MD, M);
        M.reset();
        // project for variables in head.
        for (unsigned i = 0; i < MD.size(); ++i) {
            vector<rational> row;
            row.append(arity, MD.A[i].c_ptr() + num_vars);
            M.A.push_back(row);
            M.b.push_back(MD.b[i]);
            M.eq.push_back(true);
        }
        
        return true;
    }

    void mk_karr_invariants::intersect_matrix(app* p, matrix const& Mp, unsigned num_columns, matrix& M) {
        for (unsigned j = 0; j < Mp.size(); ++j) {
            rational b = Mp.b[j], n;
            vector<rational> row;
            row.resize(num_columns, rational(0));
            for (unsigned i = 0; i < p->get_num_args(); ++i) {
                expr* arg = p->get_arg(i);
                if (!a.is_int(arg)) {
                    // no-op
                }
                else if (is_var(arg)) {
                    unsigned idx = to_var(arg)->get_idx();
                    row[idx] += Mp.A[j][i];
                }
                else if (a.is_numeral(arg, n)) {
                    b += Mp.A[j][i]*n;
                }
                else {
                    UNREACHABLE();
                }
            }
            M.A.push_back(row);
            M.b.push_back(b);
            M.eq.push_back(Mp.eq[j]);
        }
    }

    // treat src as a homogeneous matrix.
    void mk_karr_invariants::dualizeH(matrix& dst, matrix const& src) {
        dst.reset();
        if (src.size() == 0) {
            return;
        }
        m_hb.reset();
        for (unsigned i = 0; i < src.size(); ++i) {
            vector<rational> v(src.A[i]);
            v.append(src.b[i]);
            if (src.eq[i]) {
                m_hb.add_eq(v, rational(0));
            }
            else {
                m_hb.add_ge(v, rational(0));
            }
        }
        for (unsigned i = 0; i < 1 + src.A[0].size(); ++i) {
            m_hb.set_is_int(i);
        }
        lbool is_sat = m_hb.saturate();
        TRACE("dl", m_hb.display(tout););
        SASSERT(is_sat == l_true);
        unsigned basis_size = m_hb.get_basis_size();
        for (unsigned i = 0; i < basis_size; ++i) {
            bool is_initial;
            vector<rational> soln;
            m_hb.get_basis_solution(i, soln, is_initial);
            if (!is_initial) {
                dst.b.push_back(soln.back());
                dst.eq.push_back(true);
                soln.pop_back();
                dst.A.push_back(soln);
            }
        }
    }

    // treat src as an inhomegeneous matrix.
    void mk_karr_invariants::dualizeI(matrix& dst, matrix const& src) {
        m_hb.reset();
        for (unsigned i = 0; i < src.size(); ++i) {
            if (src.eq[i]) {
                m_hb.add_eq(src.A[i], -src.b[i]);
            }
            else {
                m_hb.add_ge(src.A[i], -src.b[i]);
            }
        }
        for (unsigned i = 0; !src.A.empty() && i < src.A[0].size(); ++i) {
            m_hb.set_is_int(i);
        }
        lbool is_sat = m_hb.saturate();
        TRACE("dl", m_hb.display(tout););
        SASSERT(is_sat == l_true);
        dst.reset();
        unsigned basis_size = m_hb.get_basis_size();
        bool first_initial = true;
        for (unsigned i = 0; i < basis_size; ++i) {
            bool is_initial;
            vector<rational> soln;
            m_hb.get_basis_solution(i, soln, is_initial);
            if (is_initial && first_initial) {
                dst.A.push_back(soln);
                dst.b.push_back(rational(1));
                dst.eq.push_back(true);
                first_initial = false;
            }
            else if (!is_initial) {
                dst.A.push_back(soln);
                dst.b.push_back(rational(0));
                dst.eq.push_back(true);
            }
        }
    }

    void mk_karr_invariants::update_body(rule_set& rules, rule& r){
        unsigned utsz = r.get_uninterpreted_tail_size();
        unsigned tsz  = r.get_tail_size();
        app_ref_vector tail(m);
        for (unsigned i = 0; i < tsz; ++i) {
            tail.push_back(r.get_tail(i));
        }
        for (unsigned i = 0; i < utsz; ++i) {
            func_decl* q = r.get_decl(i);            
            matrix* N = get_constraints(q);
            if (!N) {
                continue;
            }
            expr_ref zero(m), lhs(m);
            zero = a.mk_numeral(rational(0), true);
            for (unsigned j = 0; j < N->size(); ++j) {
                rational n;
                SASSERT(N->A[j].size() == q->get_arity());
                expr_ref_vector sum(m);
                for (unsigned k = 0; k < N->A[j].size(); ++k) {
                    n = N->A[j][k];
                    if (!n.is_zero()) {
                        expr* arg = r.get_tail(i)->get_arg(k);
                        sum.push_back(a.mk_mul(a.mk_numeral(n, true), arg));
                    }
                }
                n = N->b[j];
                if (!n.is_zero()) {
                    sum.push_back(a.mk_numeral(n, true));
                }               
                lhs = a.mk_add(sum.size(), sum.c_ptr());
                if (N->eq[j]) {
                    tail.push_back(m.mk_eq(lhs, zero));
                }
                else {
                    tail.push_back(a.mk_ge(lhs, zero));
                }
            }            
        }
        rule* new_rule = &r;
        if (tail.size() != tsz) {
            new_rule = rm.mk(r.get_head(), tail.size(), tail.c_ptr(), 0, r.name());
        }
        rules.add_rule(new_rule);
    }

    class mk_karr_invariants::add_invariant_model_converter : public model_converter {
        ast_manager&          m;
        arith_util            a;
        func_decl_ref_vector  m_funcs;
        ptr_vector<matrix>    m_invs;
    public:
        
        add_invariant_model_converter(ast_manager& m): m(m), a(m), m_funcs(m) {}

        virtual ~add_invariant_model_converter() {
            for (unsigned i = 0; i < m_invs.size(); ++i) {
                dealloc(m_invs[i]);
            }
        }

        void add(func_decl* p, matrix& M) {
            m_funcs.push_back(p);
            m_invs.push_back(alloc(matrix, M));
        }

        virtual void operator()(model_ref & mr) {
            for (unsigned i = 0; i < m_funcs.size(); ++i) {
                func_decl* p = m_funcs[i].get();
                func_interp* f = mr->get_func_interp(p);
                expr_ref body(m);                
                unsigned arity = p->get_arity();
                SASSERT(0 < arity);
                if (f) {
                    matrix const& M = *m_invs[i];
                    mk_body(M, body);
                    SASSERT(f->num_entries() == 0);
                    if (!f->is_partial()) {
                        body = m.mk_and(f->get_else(), body);
                    }
                }
                else {
                    f = alloc(func_interp, m, arity);
                    mr->register_decl(p, f);
                    body = m.mk_false();  // fragile: assume that relation was pruned by being infeasible.
                }
                f->set_else(body);
            }            
        }
    
        virtual model_converter * translate(ast_translation & translator) {
            add_invariant_model_converter* mc = alloc(add_invariant_model_converter, m);
            for (unsigned i = 0; i < m_funcs.size(); ++i) {
                mc->add(translator(m_funcs[i].get()), *m_invs[i]);
            }
            return mc;
        }

    private:
        void mk_body(matrix const& M, expr_ref& body) {
            expr_ref_vector conj(m);
            for (unsigned i = 0; i < M.size(); ++i) {
                mk_body(M.A[i], M.b[i], M.eq[i], conj);
            }
            body = m.mk_and(conj.size(), conj.c_ptr());
        }

        void mk_body(vector<rational> const& row, rational const& b, bool is_eq, expr_ref_vector& conj) {
            expr_ref_vector sum(m);
            expr_ref zero(m), lhs(m);
            zero = a.mk_numeral(rational(0), true);

            for (unsigned i = 0; i < row.size(); ++i) {
                if (row[i].is_zero()) {
                    continue;
                }
                var* var = m.mk_var(i, a.mk_int());
                if (row[i].is_one()) {
                    sum.push_back(var);
                }
                else {
                    sum.push_back(a.mk_mul(a.mk_numeral(row[i], true), var));
                }
            }
            if (!b.is_zero()) {
                sum.push_back(a.mk_numeral(b, true));
            }
            lhs = a.mk_add(sum.size(), sum.c_ptr());
            if (is_eq) {
                conj.push_back(m.mk_eq(lhs, zero));
            }
            else {
                conj.push_back(a.mk_ge(lhs, zero));
            }
        }

    };

    void mk_karr_invariants::cancel() {
        rule_transformer::plugin::cancel();
        m_hb.set_cancel(true);
    }
    
    rule_set * mk_karr_invariants::operator()(rule_set const & source, model_converter_ref& mc, proof_converter_ref& pc) {
        if (!m_ctx.get_params().karr()) {
            return 0;
        }
        rule_set::iterator it = source.begin(), end = source.end();
        for (; it != end; ++it) {
            rule const& r = **it;
            if (r.has_negation()) {
                return 0;
            }
        }
        bool change = true, non_empty = false;
        while (!m_cancel && change) {
            change = false;
            it = source.begin();            
            for (; it != end; ++it) {
                rule const& r = **it;
                TRACE("dl", r.display(m_ctx, tout););
                matrix MD, P;
                if (!get_transition_relation(r, MD)) {
                    continue;
                }
                non_empty = true;
                func_decl* p = r.get_decl();
                matrix& ND = get_dual_constraints(p);
                matrix* N  = get_constraints(p);
                ND.append(MD);
                dualizeH(P, ND);

                TRACE("dl",
                           MD.display(tout << "MD\n");
                           P.display(tout << "P\n"););

                if (!N) {
                    change = true;
                    N = alloc(matrix, P);
                    m_constraints.insert(p, N);
                }
                else if (P.size() != N->size()) {
                    change = true;
                    *N = P;
                }
            }
        }

        if (!non_empty) {
            return 0;
        }

        if (m_cancel) {
            return 0;
        }

        TRACE("dl",
                   rule_set::decl2rules::iterator git  = source.begin_grouped_rules();
                   rule_set::decl2rules::iterator gend = source.end_grouped_rules();
                   for (; git != gend; ++git) {
                       func_decl* p = git->m_key;
                       matrix* M = get_constraints(p);
                       tout << p->get_name() << "\n";
                       if (M) {
                           M->display(tout);
                       }
                   });
        
        rule_set* rules = alloc(rule_set, m_ctx);
        it = source.begin();            
        for (; it != end; ++it) {
            update_body(*rules, **it);
        }
        if (mc) {
            add_invariant_model_converter* kmc = alloc(add_invariant_model_converter, m);
            rule_set::decl2rules::iterator git  = source.begin_grouped_rules();
            rule_set::decl2rules::iterator gend = source.end_grouped_rules();
            for (; git != gend; ++git) {
                func_decl* p = git->m_key;
                matrix* M = get_constraints(p);
                if (M) {
                    kmc->add(p, *M);
                }
            }
            mc = concat(mc.get(), kmc);
        }
        TRACE("dl", rules->display(tout););
        return rules;
    }

};

