/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    dl_bound_relation.cpp

Abstract:

    Basic (strict upper) bound relation.

Author:

    Nikolaj Bjorner (nbjorner) 2010-2-11

Revision History:

--*/

#include "muz/rel/dl_bound_relation.h"
#include "util/debug.h"
#include "ast/ast_pp.h"

namespace datalog {

    bound_relation_plugin::bound_relation_plugin(relation_manager& m):
        relation_plugin(bound_relation_plugin::get_name(), m), 
        m_arith(get_ast_manager()),
        m_bsimp(get_ast_manager()) {
    }

    bool bound_relation_plugin::can_handle_signature(const relation_signature & sig) {
        for (unsigned i = 0; i < sig.size(); ++i) {
            if (!m_arith.is_int(sig[i]) && !m_arith.is_real(sig[i])) {
                return false;
            }
        }
        return true;
    }

    bound_relation& bound_relation_plugin::get(relation_base& r) {
        return dynamic_cast<bound_relation&>(r);
    }

    bound_relation const & bound_relation_plugin::get(relation_base const& r) {
        return dynamic_cast<bound_relation const&>(r);
    }

    bound_relation* bound_relation_plugin::get(relation_base* r) {
        return dynamic_cast<bound_relation*>(r);
    }

    bool bound_relation_plugin::is_interval_relation(relation_base const& r) {       
        return symbol("interval_relation") == r.get_plugin().get_name();
    }

    interval_relation& bound_relation_plugin::get_interval_relation(relation_base& r) {
        SASSERT(is_interval_relation(r));
        return dynamic_cast<interval_relation&>(r);
    }

    interval_relation const& bound_relation_plugin::get_interval_relation(relation_base const& r) {
        SASSERT(is_interval_relation(r));
        return dynamic_cast<interval_relation const&>(r);
    }

    relation_base * bound_relation_plugin::mk_empty(const relation_signature & s) {
        return alloc(bound_relation, *this, s, true);
    }

    relation_base * bound_relation_plugin::mk_full(func_decl* p, const relation_signature & s) {
        return alloc(bound_relation, *this, s, false);
    }

    class bound_relation_plugin::join_fn : public convenient_relation_join_fn {
    public:
        join_fn(const relation_signature & o1_sig, const relation_signature & o2_sig, unsigned col_cnt,
                const unsigned * cols1, const unsigned * cols2) 
            : convenient_relation_join_fn(o1_sig, o2_sig, col_cnt, cols1, cols2) {
        }

        relation_base * operator()(const relation_base & _r1, const relation_base & _r2) override {
            bound_relation const& r1 = get(_r1);
            bound_relation const& r2 = get(_r2);
            bound_relation_plugin& p = r1.get_plugin();
            bound_relation* result = dynamic_cast<bound_relation*>(p.mk_full(nullptr, get_result_signature()));
            result->mk_join(r1, r2, m_cols1.size(), m_cols1.c_ptr(), m_cols2.c_ptr());
            return result;
        }
    };

    relation_join_fn * bound_relation_plugin::mk_join_fn(const relation_base & r1, const relation_base & r2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
        if (!check_kind(r1) || !check_kind(r2)) {
            return nullptr;
        }
        return alloc(join_fn, r1.get_signature(), r2.get_signature(), col_cnt, cols1, cols2);
    }


    class bound_relation_plugin::project_fn : public convenient_relation_project_fn {
    public:
        project_fn(const relation_signature & orig_sig, unsigned removed_col_cnt, const unsigned * removed_cols) 
            : convenient_relation_project_fn(orig_sig, removed_col_cnt, removed_cols) {
        }

        relation_base * operator()(const relation_base & _r) override {
            bound_relation const& r = get(_r);
            bound_relation_plugin& p = r.get_plugin();
            bound_relation* result = get(p.mk_full(nullptr, get_result_signature()));
            result->mk_project(r, m_removed_cols.size(), m_removed_cols.c_ptr());
            return result;
        }
    };

    relation_transformer_fn * bound_relation_plugin::mk_project_fn(const relation_base & r, 
            unsigned col_cnt, const unsigned * removed_cols) {
        return alloc(project_fn, r.get_signature(), col_cnt, removed_cols);
    }
   
    class bound_relation_plugin::rename_fn : public convenient_relation_rename_fn {
    public:
        rename_fn(const relation_signature & orig_sig, unsigned cycle_len, const unsigned * cycle) 
            : convenient_relation_rename_fn(orig_sig, cycle_len, cycle) {
        }

        relation_base * operator()(const relation_base & _r) override {
            bound_relation const& r = get(_r);
            bound_relation_plugin& p = r.get_plugin();
            bound_relation* result = get(p.mk_full(nullptr, get_result_signature()));
            result->mk_rename(r, m_cycle.size(), m_cycle.c_ptr());
            return result;
        }
    };

    relation_transformer_fn * bound_relation_plugin::mk_rename_fn(const relation_base & r, 
            unsigned cycle_len, const unsigned * permutation_cycle) {
        if(check_kind(r)) {
            return alloc(rename_fn, r.get_signature(), cycle_len, permutation_cycle);
        }
        return nullptr;
    }
     

    class bound_relation_plugin::union_fn : public relation_union_fn {
        bool m_is_widen;
    public:
        union_fn(bool is_widen) :
            m_is_widen(is_widen) {            
        }
        void operator()(relation_base & _r, const relation_base & _src, relation_base * _delta) override {
            TRACE("bound_relation", _r.display(tout << "dst:\n"); _src.display(tout  << "src:\n"););
            get(_r).mk_union(get(_src), get(_delta), m_is_widen);
        }
    };

    class bound_relation_plugin::union_fn_i : public relation_union_fn {
        bool m_is_widen;
    public:
        union_fn_i(bool is_widen) :
            m_is_widen(is_widen) {            
        }
        void operator()(relation_base & _r, const relation_base & _src, relation_base * _delta) override {
            TRACE("bound_relation", _r.display(tout << "dst:\n"); _src.display(tout  << "src:\n"););   
            get(_r).mk_union_i(get_interval_relation(_src), get(_delta), m_is_widen);
            TRACE("bound_relation", _r.display(tout << "dst':\n"););
        }
    };
    

    relation_union_fn * bound_relation_plugin::mk_union_fn(const relation_base & tgt, const relation_base & src,
        const relation_base * delta) {
        if (check_kind(tgt) && is_interval_relation(src) && (!delta || check_kind(*delta))) {
            return alloc(union_fn_i, false);
        }
        if (check_kind(tgt) && check_kind(src) && (!delta || check_kind(*delta))) {
            return alloc(union_fn, false);
        }
        return nullptr;
    }

    relation_union_fn * bound_relation_plugin::mk_widen_fn(
        const relation_base & tgt, const relation_base & src, 
        const relation_base * delta) {
        if (check_kind(tgt) && is_interval_relation(src) && (!delta || check_kind(*delta))) {
            return alloc(union_fn_i, true);
        }
        if (check_kind(tgt) && check_kind(src) && (!delta || check_kind(*delta))) {
            return alloc(union_fn, true);
        }
        return nullptr;
    }

    class bound_relation_plugin::filter_identical_fn : public relation_mutator_fn {
        unsigned_vector m_cols;
    public:
        filter_identical_fn(unsigned col_cnt, const unsigned * identical_cols) 
            : m_cols(col_cnt, identical_cols) {}

        void operator()(relation_base & r) override {
            for (unsigned i = 1; i < m_cols.size(); ++i) {
                get(r).equate(m_cols[0], m_cols[i]);
            }
        }
    };

    relation_mutator_fn * bound_relation_plugin::mk_filter_identical_fn(
        const relation_base & t, unsigned col_cnt, const unsigned * identical_cols) {
        if(check_kind(t)) {
            return alloc(filter_identical_fn, col_cnt, identical_cols);
        }
        return nullptr;
    }

    class bound_relation_plugin::filter_equal_fn : public relation_mutator_fn {
    public:
        filter_equal_fn(relation_element const& value, unsigned col) {}

        void operator()(relation_base & r) override { }
    };

    relation_mutator_fn * bound_relation_plugin::mk_filter_equal_fn(const relation_base & r, 
        const relation_element & value, unsigned col) {
        if (check_kind(r)) {
            return alloc(filter_equal_fn, value, col);
        }
        return nullptr;
    }

    class bound_relation_plugin::filter_interpreted_fn : public relation_mutator_fn {
        enum kind_t { NOT_APPLICABLE, EQ_VAR, EQ_SUB, LT_VAR, LE_VAR, K_FALSE };
        app_ref            m_cond;
        app_ref            m_lt;
        arith_util         m_arith;
        interval_relation* m_interval;
        unsigned_vector    m_vars;
        kind_t             m_kind;

        unsigned get_var(expr* a) {
            SASSERT(is_var(a));
            return to_var(a)->get_idx();
        }
        
        // x = z - y
        void mk_sub_eq(expr* x, expr* z, expr* y) {
            SASSERT(is_var(x));
            SASSERT(is_var(z));
            SASSERT(is_var(y));
            m_vars.push_back(get_var(x));
            m_vars.push_back(get_var(z));
            m_vars.push_back(get_var(y));
            m_kind = EQ_SUB;
        }

        void mk_lt(expr* l, expr* r) {
            SASSERT(is_var(l));
            SASSERT(is_var(r));
            m_vars.push_back(get_var(l));
            m_vars.push_back(get_var(r));
            m_lt = m_arith.mk_lt(l, r);
            m_kind = LT_VAR;
        }


        void mk_le(expr* l, expr* r) {
            SASSERT(is_var(l));
            SASSERT(is_var(r));
            m_vars.push_back(get_var(l));
            m_vars.push_back(get_var(r));
            m_kind = LE_VAR;
        }

        void mk_eq(expr* l, expr* r) {
            m_vars.push_back(get_var(l));
            m_vars.push_back(get_var(r));
            m_kind = EQ_VAR;
        }

    public:

        filter_interpreted_fn(ast_manager& m, app* cond) : 
            m_cond(cond, m), 
            m_lt(m), m_arith(m), m_interval(nullptr), m_kind(NOT_APPLICABLE) {
            expr* l, *r, *r1, *r2, *c2;
            rational n1;
            if ((m_arith.is_lt(cond, l, r) || m_arith.is_gt(cond, r, l)) && 
                is_var(l) && is_var(r)) {
                mk_lt(l, r);
            }
            else if (m.is_not(cond, c2) && 
                     (m_arith.is_ge(c2, l, r) || m_arith.is_le(c2, r, l)) && 
                is_var(l) && is_var(r)) {
                mk_lt(l, r);
            }
            else if ((m_arith.is_le(cond, l, r) || m_arith.is_ge(cond, r, l)) && 
                is_var(l) && is_var(r)) {
                mk_le(l, r);
            }
            else if (m.is_not(cond, c2) && 
                     (m_arith.is_gt(c2, l, r) || m_arith.is_lt(c2, r, l)) && 
                is_var(l) && is_var(r)) {
                mk_le(l, r);
            }
            else if (m.is_false(cond)) {
                m_kind = K_FALSE;
            }
            else if (m.is_eq(cond, l, r) && is_var(l) && is_var(r)) {
                mk_eq(l, r);
            }            
            else if (m.is_eq(cond, l, r) && 
                     m_arith.is_sub(r, r1, r2) && 
                     is_var(l) && is_var(r1) && is_var(r2)) {
                mk_sub_eq(l, r1, r2);
            }
            else if (m.is_eq(cond, l, r) && 
                     m_arith.is_sub(l, r1, r2) && 
                     is_var(r) && is_var(r1) && is_var(r2)) {
                mk_sub_eq(r, r1, r2);
            }
            else if (m.is_eq(cond, l, r) && 
                     m_arith.is_add(r, r1, r2) &&
                     m_arith.is_numeral(r1, n1) &&
                     n1.is_pos() && is_var(l) && is_var(r2)) {
                mk_lt(r2, l);
            }
            else if (m.is_eq(cond, l, r) && 
                     m_arith.is_add(r, r1, r2) &&
                     m_arith.is_numeral(r2, n1) &&
                     n1.is_pos() && is_var(l) && is_var(r1)) {
                mk_lt(r1, l);
            }
            else {
                
            }            
        }
     
        //
        // x = z - y
        // x = y
        // x < y
        // x <= y
        // x < y + z
        //  

        void operator()(relation_base& t) override {
            TRACE("dl", tout << mk_pp(m_cond, m_cond.get_manager()) << "\n"; t.display(tout););
            bound_relation& r = get(t);
            switch(m_kind) {
            case K_FALSE:
                r.set_empty();
                break;
            case NOT_APPLICABLE: 
                break;
            case EQ_VAR:
                r.equate(m_vars[0], m_vars[1]);
                break;
            case EQ_SUB:
                // TBD
                break;            
            case LT_VAR:
                r.mk_lt(m_vars[0], m_vars[1]);
                break;
            case LE_VAR:
                r.mk_le(m_vars[0], m_vars[1]);
                break;
            default:
                UNREACHABLE();
                break;
            }    
            TRACE("dl", t.display(tout << "result\n"););   
        }

        bool supports_attachment(relation_base& t) override {
            return is_interval_relation(t);
        }

        void attach(relation_base& t) override {
            SASSERT(is_interval_relation(t));
            interval_relation& r = get_interval_relation(t);
            m_interval = &r;
        } 
    };

    relation_mutator_fn * bound_relation_plugin::mk_filter_interpreted_fn(const relation_base & t, app * condition) {
        return alloc(filter_interpreted_fn, t.get_plugin().get_ast_manager(), condition);
    }      

    // -----------------------------
    // bound_relation

    void bound_relation_helper::mk_project_t(uint_set2& t, unsigned_vector const& renaming) {
        if (t.lt.empty() && t.le.empty()) {
            return;
        }
        uint_set::iterator it = t.lt.begin(), end = t.lt.end();
        unsigned_vector ltv, lev;
        for (; it != end; ++it) {
            ltv.push_back(renaming[*it]);
        }
        it = t.le.begin(), end = t.le.end();
        for (; it != end; ++it) {
            lev.push_back(renaming[*it]);
        }
        TRACE("dl", 
              tout << "project: ";
              for (unsigned i = 0; i < renaming.size(); ++i) 
                  if (renaming[i] == UINT_MAX) tout << i << " ";
              tout << ": ";
              it = t.lt.begin(); end = t.lt.end();
              for (; it != end; ++it) tout << *it << " ";
              tout << " le ";
              it = t.le.begin(); end = t.le.end();
              for (; it != end; ++it) tout << *it << " ";
              tout << " => ";
              for (unsigned i = 0; i < ltv.size(); ++i) tout << ltv[i] << " ";
              tout << " le ";
              for (unsigned i = 0; i < lev.size(); ++i) tout << lev[i] << " ";
              tout << "\n";);
        t.lt.reset();
        for (unsigned i = 0; i < ltv.size(); ++i) {
            t.lt.insert(ltv[i]);
        }
        t.le.reset();
        for (unsigned i = 0; i < lev.size(); ++i) {
            t.le.insert(lev[i]);
        }
    }

    bound_relation::bound_relation(bound_relation_plugin& p, relation_signature const& s, bool is_empty):
        vector_relation<uint_set2, bound_relation_helper>(p, s, is_empty, uint_set2())
    {
    }


    uint_set2 bound_relation::mk_intersect(uint_set2 const& t1, uint_set2 const& t2, bool& is_empty) const {
        is_empty = false;
        uint_set2 r(t1);
        r.lt |= t2.lt;
        r.le |= t2.le;
        return r;
    }

    uint_set2 bound_relation::mk_widen(uint_set2 const& t1, uint_set2 const& t2) const {
        return mk_unite(t1, t2);  
    }

    uint_set2 bound_relation::mk_unite(uint_set2 const& t1, uint_set2 const& t2) const {
        uint_set2 s1(t1);
        s1.lt &= t2.lt;
        s1.le &= t2.le;
        return s1;
    }

    uint_set2 bound_relation::mk_eq(union_find<> const& old_eqs, union_find<> const& new_eqs, uint_set2 const& t) const {
        unsigned sz = old_eqs.get_num_vars();
        SASSERT(sz == new_eqs.get_num_vars());
        uint_set2 result;
        for (unsigned i = 0; i < sz; ++i) {
            if (t.lt.contains(i)) {
                unsigned j = i;         
                do {
                    result.lt.insert(new_eqs.find(j));
                    j = old_eqs.next(j);
                }
                while (j != i);
            }
            if (t.le.contains(i)) {
                unsigned j = i;         
                do {
                    result.le.insert(new_eqs.find(j));
                    j = old_eqs.next(j);
                }
                while (j != i);
            }
        }
        return result;
    }

    bool bound_relation::is_subset_of(uint_set2 const& t1, uint_set2 const& t2) const {
        uint_set2 s1, s2;
        normalize(t1, s1);
        normalize(t2, s2);
        return s1.lt.subset_of(s2.lt) && s1.le.subset_of(s2.le);
    }

    void bound_relation::mk_rename_elem(uint_set2& t, unsigned col_cnt, unsigned const* cycle) {
        // [ 0 -> 2 -> 3 -> 0]
        if (col_cnt == 0) return;
        unsigned col1, col2;
        col1 = find(cycle[0]);
        col2 = find(cycle[col_cnt-1]);
        bool has_col2_lt = t.lt.contains(col2);
        t.lt.remove(col2);
        bool has_col2_le = t.le.contains(col2);
        t.le.remove(col2);
        for (unsigned i = 0; i + 1 < col_cnt; ++i) {
            col1 = find(cycle[i]);
            col2 = find(cycle[i+1]);
            if (t.lt.contains(col1)) {
                t.lt.remove(col1);
                t.lt.insert(col2);
            }
            if (t.le.contains(col1)) {
                t.le.remove(col1);
                t.le.insert(col2);
            }
        }
        if (has_col2_lt) {
            col1 = find(cycle[0]);
            t.lt.insert(col1);
        }
        if (has_col2_le) {
            col1 = find(cycle[0]);
            t.le.insert(col1);
        }
    }


    bool bound_relation::is_full(uint_set2 const& t) const {
        return t.lt.empty() && t.le.empty();
    }

    bool bound_relation::is_empty(unsigned index, uint_set2 const& t) const {
        return t.lt.contains(find(index)) || t.le.contains(find(index));
    }

    void bound_relation::normalize(uint_set const& src, uint_set& dst) const {
        uint_set::iterator it = src.begin(), end = src.end();
        for (; it != end; ++it) {
            dst.insert(find(*it));
        }
    }
    void bound_relation::normalize(uint_set2 const& src, uint_set2& dst) const {
        normalize(src.lt, dst.lt);
        normalize(src.le, dst.le);
    }


    void bound_relation::mk_lt(unsigned i) {
        uint_set2& dst = (*this)[i];        
        while (!m_todo.empty()) {
            unsigned j = m_todo.back().first;
            bool strict = m_todo.back().second;
            if (i == j && strict) {
                m_todo.reset();
                m_empty = true;
                return;
            }
            m_todo.pop_back();
            if (i == j) {
                continue;
            }
            uint_set2& src = (*m_elems)[j];
            uint_set::iterator it = src.lt.begin(), end = src.lt.end();
            for(; it != end; ++it) {
                m_todo.push_back(std::make_pair(*it, true));
            }
            it = src.le.begin(), end = src.le.end();
            for(; it != end; ++it) {
                m_todo.push_back(std::make_pair(*it, strict));
            }
            if (strict) {
                dst.lt.insert(j);
            }
            else {
                dst.le.insert(j);
            }
        }
    }

    void bound_relation::mk_lt(unsigned i, unsigned j) {
        m_todo.reset();
        i = find(i);
        m_todo.push_back(std::make_pair(find(j), true));
        mk_lt(i);
    }

    void bound_relation::mk_le(unsigned i, unsigned j) {
        m_todo.reset();
        i = find(i);
        m_todo.push_back(std::make_pair(find(j), false));
        mk_lt(i);
    }

    bool bound_relation::is_lt(unsigned i, unsigned j) const {
        return (*this)[i].lt.contains(find(j));
    }

    void bound_relation::add_fact(const relation_fact & f) {        
        bound_relation r(get_plugin(), get_signature(), false);
        for (unsigned i = 0; i < f.size(); ++i) {
            scoped_ptr<relation_mutator_fn> fe = get_plugin().mk_filter_equal_fn(r, f[i], i);
            (*fe)(r);
        }
        mk_union(r, nullptr, false);
    }

    bool bound_relation::contains_fact(const relation_fact & f) const {
        if (empty()) {
            return false;
        }
        // this is a very rough approximation.
        return true;
    }

    bound_relation * bound_relation::clone() const {
        bound_relation* result = nullptr;
        if (empty()) {
            result = bound_relation_plugin::get(get_plugin().mk_empty(get_signature()));
        }
        else {
            result = bound_relation_plugin::get(get_plugin().mk_full(nullptr, get_signature()));
            result->copy(*this);
        }        
        return result;
    }

    void bound_relation::mk_union_i(interval_relation const& src, bound_relation* delta, bool is_widen) {
        unsigned size = get_signature().size();
        for (unsigned i = 0; i < size; ++i) {
            if (find(i) != i) {
                continue;
            }
            uint_set2& s = (*this)[i];
            ext_numeral const& lo = src[i].sup();
            if (lo.is_infinite()) {
                s.lt.reset();
                s.le.reset();
                continue;
            }
            uint_set::iterator it = s.lt.begin(), end = s.lt.end();
            for(; it != end; ++it) {
                ext_numeral const& hi = src[*it].inf();
                if (hi.is_infinite() || lo.to_rational() >= hi.to_rational()) {
                    s.lt.remove(*it);
                }
            }            
            it = s.le.begin(), end = s.le.end();
            for(; it != end; ++it) {
                ext_numeral const& hi = src[*it].inf();
                if (hi.is_infinite() || lo.to_rational() > hi.to_rational()) {
                    s.le.remove(*it);
                }
            }            
        }
    }

    bound_relation * bound_relation::complement(func_decl* p) const {
        UNREACHABLE();
        return nullptr;
    }

    void bound_relation::to_formula(expr_ref& fml) const {
        ast_manager& m = get_plugin().get_ast_manager();
        arith_util& arith = get_plugin().m_arith;
        bool_rewriter& bsimp = get_plugin().m_bsimp;
        expr_ref_vector conjs(m);
        relation_signature const& sig = get_signature();
        for (unsigned i = 0; i < sig.size(); ++i) {
            if (i != find(i)) {
                conjs.push_back(m.mk_eq(m.mk_var(i, sig[i]), m.mk_var(find(i), sig[find(i)])));
                continue;
            }
            uint_set2 const& upper = (*this)[i];
            uint_set::iterator it = upper.lt.begin(), end = upper.lt.end();
            for (; it != end; ++it) {
                conjs.push_back(arith.mk_lt(m.mk_var(i, sig[i]), m.mk_var(*it, sig[*it])));
            }
            it = upper.le.begin(), end = upper.le.end();
            for (; it != end; ++it) {
                conjs.push_back(arith.mk_le(m.mk_var(i, sig[i]), m.mk_var(*it, sig[*it])));
            }
        }
        bsimp.mk_and(conjs.size(), conjs.c_ptr(), fml);
    }


    void bound_relation::display_index(unsigned i, uint_set2 const& src, std::ostream & out) const {
        uint_set::iterator it = src.lt.begin(), end = src.lt.end();
        out << "#" << i;
        if (!src.lt.empty()) {
            out << " < ";
            for(; it != end; ++it) {
                out << *it << " ";
            }
        }
        if (!src.le.empty()) {
            it = src.le.begin(), end = src.le.end();
            out << " <= ";
            for(; it != end; ++it) {
                out << *it << " ";
            }
        }
        if (src.lt.empty() && src.le.empty()) {
            out << " < oo";
        }
        out << "\n";
    }

    bound_relation_plugin& bound_relation::get_plugin() const {
        return dynamic_cast<bound_relation_plugin&>(relation_base::get_plugin());
    }


};


