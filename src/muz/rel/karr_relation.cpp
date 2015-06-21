
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "karr_relation.h"
#include "bool_rewriter.h"

namespace datalog {
    class karr_relation : public relation_base {              
        friend class karr_relation_plugin;
        friend class karr_relation_plugin::filter_equal_fn;

        karr_relation_plugin& m_plugin;
        ast_manager&          m;
        mutable arith_util    a;
        func_decl_ref         m_fn;
        mutable bool          m_empty;
        mutable matrix        m_ineqs;
        mutable bool          m_ineqs_valid;
        mutable matrix        m_basis;
        mutable bool          m_basis_valid;

    public:
        karr_relation(karr_relation_plugin& p, func_decl* f, relation_signature const& s, bool is_empty):
            relation_base(p, s),
            m_plugin(p),
            m(p.get_ast_manager()),
            a(m),
            m_fn(f, m),
            m_empty(is_empty),
            m_ineqs_valid(!is_empty),
            m_basis_valid(false)
        {
        }

        virtual bool empty() const { 
            return m_empty;
        }

        virtual bool is_precise() const { return false; }

        virtual void add_fact(const relation_fact & f) {
            SASSERT(m_empty);
            SASSERT(!m_basis_valid);
            m_empty = false;
            m_ineqs_valid = true;
            for (unsigned i = 0; i < f.size(); ++i) {
                rational n;
                if (a.is_numeral(f[i], n) && n.is_int()) {
                    vector<rational> row;
                    row.resize(f.size());
                    row[i] = rational(1);
                    m_ineqs.A.push_back(row);
                    m_ineqs.b.push_back(-n);
                    m_ineqs.eq.push_back(true);
                }
            }
        }

        virtual bool contains_fact(const relation_fact & f) const {            
            UNREACHABLE();
            return false;
        }

        virtual void display(std::ostream & out) const {
            if (m_fn) {
                out << m_fn->get_name() << "\n";
            }
            if (empty()) {
                out << "empty\n";
            }
            else {
                if (m_ineqs_valid) {
                    m_ineqs.display(out << "ineqs:\n");
                }
                if (m_basis_valid) {
                    m_basis.display(out << "basis:\n");
                }
            }
        }

        virtual karr_relation * clone() const {
            karr_relation* result = alloc(karr_relation, m_plugin, m_fn, get_signature(), m_empty);
            result->copy(*this);
            return result;
        }

        virtual karr_relation * complement(func_decl*) const {
            UNREACHABLE();
            return 0;
        }

        virtual void to_formula(expr_ref& fml) const {
            if (empty()) {
                fml = m.mk_false();
            }
            else {
                matrix const& M = get_ineqs();
                expr_ref_vector conj(m);
                for (unsigned i = 0; i < M.size(); ++i) {
                    to_formula(M.A[i], M.b[i], M.eq[i], conj);
                }
                bool_rewriter(m).mk_and(conj.size(), conj.c_ptr(), fml);
            }
        }

        karr_relation_plugin& get_plugin() const { return m_plugin; }

        void filter_interpreted(app* cond) {
            rational one(1), mone(-1);
            expr* e1, *e2, *en;
            var* v, *w;
            rational n1, n2;
            expr_ref_vector conjs(m);
            qe::flatten_and(cond, conjs);
            matrix& M = get_ineqs();
            unsigned num_columns = get_signature().size();

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
                else if ((a.is_le(e, e1, e2) || a.is_ge(e, e2, e1)) && 
                         is_linear(e1, row, b, mone) && is_linear(e2, row, b, one)) {
                    M.A.push_back(row);
                    M.b.push_back(b);
                    M.eq.push_back(false);
                }
                else if ((a.is_lt(e, e1, e2) || a.is_gt(e, e2, e1)) && 
                         is_linear(e1, row, b, mone) && is_linear(e2, row, b, one)) {
                    M.A.push_back(row);
                    M.b.push_back(b - rational(1));
                    M.eq.push_back(false);
                }
                else if (m.is_not(e, en) && (a.is_lt(en, e2, e1) || a.is_gt(en, e1, e2)) && 
                         is_linear(e1, row, b, mone) && is_linear(e2, row, b, one)) {
                    M.A.push_back(row);
                    M.b.push_back(b);
                    M.eq.push_back(false);
                }
                else if (m.is_not(e, en) && (a.is_le(en, e2, e1) || a.is_ge(en, e1, e2)) && 
                         is_linear(e1, row, b, mone) && is_linear(e2, row, b, one)) {
                    M.A.push_back(row);
                    M.b.push_back(b - rational(1));
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
                TRACE("dl", tout << (processed?"+ ":"- ") << mk_pp(e, m) << "\n";
                      if (processed) matrix::display_ineq(tout, row, M.b.back(), M.eq.back());
                      );
            }
            TRACE("dl", display(tout););
        }

        void mk_join(karr_relation const& r1, karr_relation const& r2, 
                     unsigned col_cnt, unsigned const* cols1, unsigned const* cols2) {
            if (r1.empty() || r2.empty()) {
                m_empty = true;
                return;
            }
            matrix const& M1 = r1.get_ineqs();
            matrix const& M2 = r2.get_ineqs();
            unsigned sig1_size = r1.get_signature().size();
            unsigned sig_size = get_signature().size();
            m_ineqs.reset();
            for (unsigned i = 0; i < M1.size(); ++i) {
                vector<rational> row;
                row.append(M1.A[i]);
                row.resize(sig_size);
                m_ineqs.A.push_back(row);
                m_ineqs.b.push_back(M1.b[i]);
                m_ineqs.eq.push_back(M1.eq[i]);
            }
            for (unsigned i = 0; i < M2.size(); ++i) {
                vector<rational> row;
                row.resize(sig_size);
                for (unsigned j = 0; j < M2.A[i].size(); ++j) {
                    row[sig1_size + j] = M2.A[i][j];
                }
                m_ineqs.A.push_back(row);
                m_ineqs.b.push_back(M2.b[i]);
                m_ineqs.eq.push_back(M2.eq[i]);
            }
            for (unsigned i = 0; i < col_cnt; ++i) {
                vector<rational> row;
                row.resize(sig_size);
                row[cols1[i]] = rational(1);
                row[sig1_size + cols2[i]] = rational(-1);
                m_ineqs.A.push_back(row);
                m_ineqs.b.push_back(rational(0));
                m_ineqs.eq.push_back(true);
            }
            m_ineqs_valid = true;
            m_basis_valid = false;
            m_empty = false;
            if (r1.m_fn) {
                m_fn = r1.m_fn;
            }
            if (r2.m_fn) {
                m_fn = r2.m_fn;
            }
        }

        void mk_project(karr_relation const& r, unsigned cnt, unsigned const* cols) {
            if (r.m_empty) {
                m_empty = true;
                return;
            }
            matrix const& M = r.get_basis();
            m_basis.reset();
            for (unsigned i = 0; i < M.size(); ++i) {
                vector<rational> row;
                unsigned k = 0;
                for (unsigned j = 0; j < M.A[i].size(); ++j) {
                    if (k < cnt && j == cols[k]) {
                        ++k;
                    }
                    else {
                        row.push_back(M.A[i][j]);
                    }
                }
                SASSERT(row.size() + cnt == M.A[i].size());
                SASSERT(M.eq[i]);
                m_basis.A.push_back(row);
                m_basis.b.push_back(M.b[i]);
                m_basis.eq.push_back(true);
            }
            m_basis_valid = true;
            m_ineqs_valid = false;
            m_empty = false;
            m_fn = r.m_fn;
            
            TRACE("dl", 
                  for (unsigned i = 0; i < cnt; ++i) {
                      tout << cols[i] << " ";
                  }
                  tout << "\n";
                  r.display(tout); 
                  display(tout););
        }

        void mk_rename(const karr_relation & r, unsigned col_cnt, const unsigned * cols) {
            if (r.empty()) {
                m_empty = true;
                return;
            }
            m_ineqs.reset();
            m_basis.reset();
            m_ineqs_valid = r.m_ineqs_valid;
            m_basis_valid = r.m_basis_valid;
            if (m_ineqs_valid) {
                m_ineqs.append(r.m_ineqs);
                mk_rename(m_ineqs, col_cnt, cols);
            }
            if (m_basis_valid) {
                m_basis.append(r.m_basis);
                mk_rename(m_basis, col_cnt, cols);
            }
            m_fn = r.m_fn;
            TRACE("dl", r.display(tout); display(tout););
        }

        void mk_union(karr_relation const& src, karr_relation* delta) {
            if (src.empty()) {
                if (delta) {
                    delta->m_empty = true;
                }
                return;
            }
            matrix const& M = src.get_basis();
            if (empty()) {
                m_basis = M;
                m_basis_valid = true;
                m_empty = false;
                m_ineqs_valid = false;
                if (delta) {
                    delta->copy(*this);
                }
                return;
            }
            matrix& N = get_basis();
            unsigned N_size = N.size();
            for (unsigned i = 0; i < M.size(); ++i) {
                bool found = false;
                for (unsigned j = 0; !found && j < N_size; ++j) {
                    found = 
                        same_row(M.A[i], N.A[j]) &&
                        M.b[i] == N.b[j] &&
                        M.eq[i] == N.eq[j];
                }
                if (!found) {
                    N.A.push_back(M.A[i]);
                    N.b.push_back(M.b[i]);
                    N.eq.push_back(M.eq[i]);
                }
            }
            m_ineqs_valid = false;
            if (N_size != N.size()) {
                if (delta) {
                    delta->copy(*this);
                }
            }
        }

        matrix const& get_basis() const {
            init_basis();
            return m_basis;
        }

        matrix& get_basis() {
            init_basis();
            return m_basis;
        }

        matrix const& get_ineqs() const {   
            init_ineqs();
            return m_ineqs;
        }

        matrix & get_ineqs() {    
            init_ineqs();
            return m_ineqs;
        }

    private:

        void copy(karr_relation const& other) {
            m_ineqs = other.m_ineqs;
            m_basis = other.m_basis;
            m_basis_valid = other.m_basis_valid;
            m_ineqs_valid = other.m_ineqs_valid;
            m_empty = other.m_empty;
        }

        bool same_row(vector<rational> const& r1, vector<rational> const& r2) const {
            SASSERT(r1.size() == r2.size());
            for (unsigned i = 0; i < r1.size(); ++i) {
                if (r1[i] != r2[i]) {
                    return false;
                }
            }
            return true;
        }

        void mk_rename(matrix& M, unsigned col_cnt, unsigned const* cols) {
            for (unsigned j = 0; j < M.size(); ++j) {
                vector<rational> & row = M.A[j];
                rational tmp = row[cols[0]];
                for (unsigned i = 0; i + 1 < col_cnt; ++i) {
                    row[cols[i]] = row[cols[i+1]];
                }
                row[cols[col_cnt-1]] = tmp;
            }
        }

        bool is_eq(expr* e, var*& v, rational& n) {
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

        bool is_linear(expr* e, vector<rational>& row, rational& b, rational const& mul) {
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

        void init_ineqs() const {
            if (!m_ineqs_valid) {
                SASSERT(m_basis_valid);
                m_plugin.dualizeH(m_ineqs, m_basis);
                m_ineqs_valid = true;
            }
        }

        void init_basis() const {
            if (!m_basis_valid) {
                SASSERT(m_ineqs_valid);
                if (m_plugin.dualizeI(m_basis, m_ineqs)) {
                    m_basis_valid = true;
                }
                else {
                    m_empty = true;
                }
            }
        }

        void to_formula(vector<rational> const& row, rational const& b, bool is_eq, expr_ref_vector& conj) const {
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


    karr_relation& karr_relation_plugin::get(relation_base& r) {
        return dynamic_cast<karr_relation&>(r);
    }

    karr_relation const & karr_relation_plugin::get(relation_base const& r) {
        return dynamic_cast<karr_relation const&>(r);
    }  

    void karr_relation_plugin::set_cancel(bool f) {
        m_hb.set_cancel(f);
    }

    relation_base * karr_relation_plugin::mk_empty(const relation_signature & s) {
        return alloc(karr_relation, *this, 0, s, true);
    }

    relation_base * karr_relation_plugin::mk_full(func_decl* p, const relation_signature & s) {
        return alloc(karr_relation, *this, p, s, false);
    }

    class karr_relation_plugin::join_fn : public convenient_relation_join_fn {
    public:
        join_fn(const relation_signature & o1_sig, const relation_signature & o2_sig, unsigned col_cnt,
                const unsigned * cols1, const unsigned * cols2) 
            : convenient_relation_join_fn(o1_sig, o2_sig, col_cnt, cols1, cols2){
        }
        
        virtual relation_base * operator()(const relation_base & _r1, const relation_base & _r2) {
            karr_relation const& r1 = get(_r1);
            karr_relation const& r2 = get(_r2);
            karr_relation_plugin& p = r1.get_plugin();
            karr_relation* result = dynamic_cast<karr_relation*>(p.mk_full(0, get_result_signature()));            
            result->mk_join(r1, r2, m_cols1.size(), m_cols1.c_ptr(), m_cols2.c_ptr());
            return result;
        }
    };

    relation_join_fn * karr_relation_plugin::mk_join_fn(
        const relation_base & t1, const relation_base & t2,
        unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
        if (!check_kind(t1) || !check_kind(t2)) {
            return 0;
        }
        return alloc(join_fn, t1.get_signature(), t2.get_signature(), col_cnt, cols1, cols2);
    }


    class karr_relation_plugin::project_fn : public convenient_relation_project_fn {
    public:
        project_fn(const relation_signature & orig_sig, unsigned removed_col_cnt, const unsigned * removed_cols) 
            : convenient_relation_project_fn(orig_sig, removed_col_cnt, removed_cols) {
        }

        virtual relation_base * operator()(const relation_base & _r) {
            karr_relation const& r = get(_r);
            karr_relation_plugin& p = r.get_plugin();
            karr_relation* result = dynamic_cast<karr_relation*>(p.mk_full(0, get_result_signature()));            
            result->mk_project(r, m_removed_cols.size(), m_removed_cols.c_ptr());
            return result;
        }
    };

    relation_transformer_fn * karr_relation_plugin::mk_project_fn(const relation_base & r, 
            unsigned col_cnt, const unsigned * removed_cols) {
        return alloc(project_fn, r.get_signature(), col_cnt, removed_cols);
    }
   
    class karr_relation_plugin::rename_fn : public convenient_relation_rename_fn {
    public:
        rename_fn(karr_relation_plugin& p, const relation_signature & orig_sig, unsigned cycle_len, const unsigned * cycle) 
            : convenient_relation_rename_fn(orig_sig, cycle_len, cycle) {}

        virtual relation_base * operator()(const relation_base & _r) {
            karr_relation const& r = get(_r);
            karr_relation_plugin& p = r.get_plugin();
            karr_relation* result = dynamic_cast<karr_relation*>(p.mk_full(0, get_result_signature()));
            result->mk_rename(r, m_cycle.size(), m_cycle.c_ptr());
            return result;
        }
    };

    relation_transformer_fn * karr_relation_plugin::mk_rename_fn(const relation_base & r, 
            unsigned cycle_len, const unsigned * permutation_cycle) {
        if (!check_kind(r)) {
            return 0;
        }
        return alloc(rename_fn, *this, r.get_signature(), cycle_len, permutation_cycle);
    }

    bool karr_relation_plugin::dualizeI(matrix& dst, matrix const& src) {
        dst.reset();
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
        lbool is_sat = l_undef;

        try {
            is_sat = m_hb.saturate();
        }
        catch (...) {
            is_sat = l_undef;
        }
        TRACE("dl_verbose", m_hb.display(tout););
        if (is_sat == l_false) {
            return false;
        }
        if (is_sat == l_undef) {
            return true;
        }
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
        return true;
    }

    void karr_relation_plugin::dualizeH(matrix& dst, matrix const& src) {
        dst.reset();
        if (src.size() == 0) {
            return;
        }
        m_hb.reset();
        for (unsigned i = 0; i < src.size(); ++i) {
            vector<rational> v(src.A[i]);
            v.push_back(src.b[i]);
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
        lbool is_sat = l_undef;
        try {
            is_sat = m_hb.saturate();
        }
        catch (...) {
            is_sat = l_undef;
        }
        if (is_sat != l_true) {
            return;
        }
        TRACE("dl_verbose", m_hb.display(tout););
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


    class karr_relation_plugin::union_fn : public relation_union_fn {
    public:
        union_fn() {}

        virtual void operator()(relation_base & _r, const relation_base & _src, relation_base * _delta) {

            karr_relation& r = get(_r);
            karr_relation const& src = get(_src);
            TRACE("dl", r.display(tout << "dst:\n"); src.display(tout  << "src:\n"););

            if (_delta) {
                karr_relation& d = get(*_delta);
                r.mk_union(src, &d);
            }
            else {
                r.mk_union(src, 0);
            }            
            TRACE("dl", r.display(tout << "result:\n"););
        }
    };

    relation_union_fn * karr_relation_plugin::mk_union_fn(const relation_base & tgt, const relation_base & src,
        const relation_base * delta) {
        if (!check_kind(tgt) || !check_kind(src) || (delta && !check_kind(*delta))) {
            return 0;
        }
        return alloc(union_fn);
    }

    class karr_relation_plugin::filter_identical_fn : public relation_mutator_fn {
        unsigned_vector m_identical_cols;
    public:
        filter_identical_fn(unsigned col_cnt, const unsigned * identical_cols) 
            : m_identical_cols(col_cnt, identical_cols) {}

        virtual void operator()(relation_base & _r) {
            karr_relation & r = get(_r);
            TRACE("dl", r.display(tout << "src:\n"););
            r.get_ineqs();
            for (unsigned i = 1; i < m_identical_cols.size(); ++i) {
                unsigned c1 = m_identical_cols[0];
                unsigned c2 = m_identical_cols[i];
                vector<rational> row;
                row.resize(r.get_signature().size());
                row[c1] = rational(1);
                row[c2] = rational(-1);
                r.m_ineqs.A.push_back(row);
                r.m_ineqs.b.push_back(rational(0));
                r.m_ineqs.eq.push_back(true);
                r.m_basis_valid = false;
            }
            TRACE("dl", r.display(tout << "result:\n"););
        }
    };

    relation_mutator_fn * karr_relation_plugin::mk_filter_identical_fn(
        const relation_base & t, unsigned col_cnt, const unsigned * identical_cols) {
        if(!check_kind(t)) {
            return 0;
        }
        return alloc(filter_identical_fn, col_cnt, identical_cols);
    }


    class karr_relation_plugin::filter_equal_fn : public relation_mutator_fn {
        unsigned m_col;
        rational m_value;
        bool    m_valid;
    public:
        filter_equal_fn(relation_manager & m, const relation_element & value, unsigned col) 
            : m_col(col) {
            arith_util arith(m.get_context().get_manager());
            m_valid = arith.is_numeral(value, m_value) && m_value.is_int();
        }

        virtual void operator()(relation_base & _r) {
            karr_relation & r = get(_r);
            if (m_valid) {
                r.get_ineqs();
                vector<rational> row;
                row.resize(r.get_signature().size());
                row[m_col] = rational(1);
                r.m_ineqs.A.push_back(row);
                r.m_ineqs.b.push_back(rational(-1));
                r.m_ineqs.eq.push_back(true);
                r.m_basis_valid = false;
            }
            TRACE("dl", tout << m_value << "\n"; r.display(tout););            
        }
    };

    relation_mutator_fn * karr_relation_plugin::mk_filter_equal_fn(const relation_base & r, 
        const relation_element & value, unsigned col) {
        if (check_kind(r)) {
            return alloc(filter_equal_fn, get_manager(), value, col);
        }
        return 0;
    }


    class karr_relation_plugin::filter_interpreted_fn : public relation_mutator_fn {
        app_ref m_cond;
    public:
        filter_interpreted_fn(karr_relation const& t, app* cond):
            m_cond(cond, t.get_plugin().get_ast_manager()) {
        }

        void operator()(relation_base& t) {
            get(t).filter_interpreted(m_cond);
            TRACE("dl", tout << mk_pp(m_cond, m_cond.get_manager()) << "\n"; t.display(tout););
        }
    };

    relation_mutator_fn * karr_relation_plugin::mk_filter_interpreted_fn(const relation_base & t, app * condition) {
        if (check_kind(t)) {
            return alloc(filter_interpreted_fn, get(t), condition);
        }
        return 0;
    }
};
