/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_base.cpp

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-09-14.

Revision History:

--*/


#include "ast/ast_pp.h"
#include "util/union_find.h"
#include "util/vector.h"
#include "muz/base/dl_context.h"
#include "muz/rel/dl_base.h"
#include "ast/rewriter/bool_rewriter.h"
#include "muz/rel/dl_relation_manager.h"
#include<sstream>


namespace datalog {

    void universal_delete(relation_base* ptr) {
        ptr->deallocate();
    }

    void universal_delete(table_base* ptr) {
        ptr->deallocate();
    }

    void dealloc_ptr_vector_content(ptr_vector<relation_base> & v) {
        for (auto& r : v) {
            r->deallocate();
        }
    }

    void get_renaming_args(const unsigned_vector & map, const relation_signature & orig_sig, 
                           expr_ref_vector & renaming_arg) {
        ast_manager & m = renaming_arg.get_manager();
        unsigned sz = map.size();
        unsigned ofs = sz-1;
        renaming_arg.resize(sz, static_cast<expr *>(nullptr));
        for (unsigned i = 0; i < sz; i++) {
            if (map[i] != UINT_MAX) {
                renaming_arg.set(ofs-i, m.mk_var(map[i], orig_sig[i]));
            }
        }
    }


    context & get_context_from_rel_manager(const relation_manager & rm) {
        return rm.get_context();
    }

    ast_manager & get_ast_manager_from_rel_manager(const relation_manager & rm) {
        return rm.get_context().get_manager();
    }

#if DL_LEAK_HUNTING
    void leak_guard_check(const symbol & s) {
    }
#endif

    void relation_signature::output(ast_manager & m, std::ostream & out) const {
        unsigned sz = size();
        out << "(";
        for (unsigned i = 0; i < sz; i++) {
            if (i != 0) out << ","; 
            out << mk_pp((*this)[i], m);
        }
        out << ")";
    }


    relation_fact::relation_fact(context & ctx) : app_ref_vector(ctx.get_manager()) {}

    void relation_base::reset() {
        ast_manager & m = get_plugin().get_ast_manager();
        app_ref bottom_ref(m.mk_false(), m);
        scoped_ptr<relation_mutator_fn> reset_fn = get_manager().mk_filter_interpreted_fn(*this, bottom_ref);
        if (!reset_fn) {
            throw default_exception("filter function does not exist");
        }
        (*reset_fn)(*this);
    }



    void table_signature::from_join(const table_signature & s1, const table_signature & s2, unsigned col_cnt, 
            const unsigned * cols1, const unsigned * cols2, table_signature & result) {
        result.reset();

        unsigned s1sz=s1.size();
        unsigned s2sz=s2.size();
        unsigned s1first_func=s1sz-s1.functional_columns();
        unsigned s2first_func=s2sz-s2.functional_columns();
        for (unsigned i=0; i<s1first_func; i++) {
            result.push_back(s1[i]);
        }
        for (unsigned i=0; i<s2first_func; i++) {
            result.push_back(s2[i]);
        }
        for (unsigned i=s1first_func; i<s1sz; i++) {
            result.push_back(s1[i]);
        }
        for (unsigned i=s2first_func; i<s2sz; i++) {
            result.push_back(s2[i]);
        }
        result.set_functional_columns(s1.functional_columns()+s2.functional_columns());
    }

    void table_signature::from_project(const table_signature & src, unsigned col_cnt, 
            const unsigned * removed_cols, table_signature & result) {
        signature_base::from_project(src, col_cnt, removed_cols, result);

        unsigned func_cnt = src.functional_columns();

        if (removed_cols==nullptr) {
            result.set_functional_columns(func_cnt);
            return;
        }

        unsigned first_src_fun = src.first_functional();
        if (removed_cols[0]<first_src_fun) {
            //if we remove at least one non-functional column, all the columns in the result are non-functional
            result.set_functional_columns(0);
        }
        else {
            //all columns we are removing are functional
            SASSERT(func_cnt>=col_cnt);
            result.set_functional_columns(func_cnt-col_cnt);
        }
    }

    void table_signature::from_project_with_reduce(const table_signature & src, unsigned col_cnt, 
            const unsigned * removed_cols, table_signature & result) {
        signature_base::from_project(src, col_cnt, removed_cols, result);

        unsigned remaining_fun = src.functional_columns();
        unsigned first_src_fun = src.first_functional();
        for (int i=col_cnt-1; i>=0; i--) {
            if (removed_cols[i]<first_src_fun) {
                break;
            }
            remaining_fun--;
        }
        result.set_functional_columns(remaining_fun);
    }

    void table_signature::from_join_project(const table_signature & s1, const table_signature & s2, 
            unsigned joined_col_cnt, const unsigned * cols1, const unsigned * cols2, unsigned removed_col_cnt, 
            const unsigned * removed_cols, table_signature & result) {
        table_signature aux;
        from_join(s1, s2, joined_col_cnt, cols1, cols2, aux);

        //after the join the column order is
        //(non-functional of s1)(non-functional of s2)(functional of s1)(functional of s2)

        if (s1.functional_columns()==0 && s2.functional_columns()==0) {
            from_project(aux, removed_col_cnt, removed_cols, result);
            SASSERT(result.functional_columns()==0);
            return;
        }

        unsigned join_sig_sz = s1.size()+s2.size();
        unsigned s1_first_func = s1.first_functional();
        unsigned s2_first_func = s2.first_functional();
        unsigned second_ofs = s1_first_func;
        unsigned first_func_ofs = second_ofs + s2_first_func;
        unsigned second_func_ofs = second_ofs + s1.functional_columns();

        svector<unsigned> remaining_in_equivalence_class;
        remaining_in_equivalence_class.resize(join_sig_sz, 0);
        bool merging_rows_can_happen = false;

        union_find_default_ctx uf_ctx;
        union_find<> uf(uf_ctx); //the numbers in uf correspond to column indexes after the join
        for (unsigned i=0; i<join_sig_sz; i++) {
            VERIFY(uf.mk_var() == i);
        }

        for (unsigned i=0; i<joined_col_cnt; i++) {
            unsigned idx1 = (s1_first_func>cols1[i]) ? cols1[i] : (first_func_ofs+cols1[i]-s1_first_func);
            unsigned idx2 = (s2_first_func>cols2[i]) ? (second_ofs+cols2[i]) : (second_func_ofs+cols2[i]-s2_first_func);
            uf.merge(idx1, idx2);
        }
        for (unsigned i=0; i<first_func_ofs; i++) { //we only count the non-functional columns
            remaining_in_equivalence_class[uf.find(i)]++;
        }

        for (unsigned i=0; i<removed_col_cnt; i++) {
            unsigned rc = removed_cols[i];
            if (rc>=first_func_ofs) {
                //removing functional columns won't make us merge rows
                continue;
            }
            unsigned eq_class_idx = uf.find(rc);
            if (remaining_in_equivalence_class[eq_class_idx]>1) {
                remaining_in_equivalence_class[eq_class_idx]--;
            }
            else {
                merging_rows_can_happen = true;
                break;
            }
        }

        if (merging_rows_can_happen) {
            //this one marks all columns as non-functional
            from_project(aux, removed_col_cnt, removed_cols, result);
            SASSERT(result.functional_columns()==0);
        }
        else {
            //this one preserves columns to be functional
            from_project_with_reduce(aux, removed_col_cnt, removed_cols, result);
        }
    }

    // -----------------------------------
    //
    // table_base
    //
    // -----------------------------------

    //here we give generic implementation of table operations using iterators

    bool table_base::empty() const {
        return begin() == end();
    }
    
    void table_base::remove_facts(unsigned fact_cnt, const table_fact * facts) {
        for (unsigned i = 0; i < fact_cnt; i++) {
            remove_fact(facts[i]);
        }
    }

    void table_base::remove_facts(unsigned fact_cnt, const table_element * facts) {
        for (unsigned i = 0; i < fact_cnt; i++) {
            remove_fact(facts + i*get_signature().size());
        }
    }


    void table_base::reset() {
        vector<table_fact> to_remove;
        table_fact row;
        for (auto& k : *this) {
            k.get_fact(row);
            to_remove.push_back(row);
        }
        remove_facts(to_remove.size(), to_remove.data());
    }

    bool table_base::contains_fact(const table_fact & f) const {
        table_fact row;
        for (auto const& k : *this) {
            k.get_fact(row);
            if (vectors_equal(row, f)) {
                return true;
            }
        }
        return false;
    }

    bool table_base::fetch_fact(table_fact & f) const {
        if (get_signature().functional_columns() == 0) {
            return contains_fact(f);
        }
        else {
            unsigned sig_sz = get_signature().size();
            unsigned non_func_cnt = sig_sz-get_signature().functional_columns();
            table_fact row;
            for (auto& k : *this) {
                k.get_fact(row);
                bool differs = false;
                for (unsigned i=0; i<non_func_cnt; i++) {
                    if (row[i]!=f[i]) {
                        differs = true;
                    }
                }
                if (differs) {
                    continue;
                }
                for (unsigned i=non_func_cnt; i<sig_sz; i++) {
                    f[i]=row[i];
                }
                return true;
            }
            return false;
        }
    }

    bool table_base::suggest_fact(table_fact & f) {
        if (get_signature().functional_columns()==0) {
            if (contains_fact(f)) {
                return false;
            }
            add_new_fact(f);
            return true;
        }
        else {
            if (fetch_fact(f)) {
                return false;
            }
            add_new_fact(f);
            return true;
        }
    }

    void table_base::ensure_fact(const table_fact & f) {
        if (get_signature().functional_columns() == 0) {
            add_fact(f);
        }
        else {
            remove_fact(f);
            add_fact(f);
        }
    }

    table_base * table_base::clone() const {
        table_base * res = get_plugin().mk_empty(get_signature());
        table_fact row;
        for (auto& k : *this) {
            k.get_fact(row);
            res->add_new_fact(row);
        }
        return res;
    }

    /**
       \brief Default method for complementation.

       It assumes that the compiler creates only tables with
       at most one column (0 or 1 columns).       
       Complementation of tables with more than one columns
       is transformed into a cross product of complements and/or
       difference. 

     */
    table_base * table_base::complement(func_decl* p, const table_element * func_columns) const {
        const table_signature & sig = get_signature();
        SASSERT(sig.functional_columns() == 0 || func_columns != 0);
        SASSERT(sig.first_functional() <= 1);

        table_base * res = get_plugin().mk_empty(sig);

        table_fact fact;
        fact.resize(sig.first_functional());
        fact.append(sig.functional_columns(), func_columns);

        if (sig.first_functional() == 0) {
            if (empty()) {
                res->add_fact(fact);
            }
            return res;
        }

        VERIFY(sig.first_functional() == 1);

        uint64_t upper_bound = get_signature()[0];
        bool empty_table = empty();

        if (upper_bound > (1 << 18)) {
            std::ostringstream buffer;
            buffer << "creating large table of size " << upper_bound;
            if (p) buffer << " for relation " << p->get_name();
            auto str = buffer.str();
            warning_msg("%s", str.c_str());
        }

        for (table_element i = 0; i < upper_bound; i++) {
            fact[0] = i;
            if (empty_table || !contains_fact(fact)) {
                res->add_fact(fact);
            }
        }
        return res;
    }
    
    void table_base::display(std::ostream & out) const {
        out << "table with signature ";
        print_container(get_signature(), out);
        out << ":\n";
        
        for (auto& k : *this) {
            k.display(out);
        }

        out << "\n";
    }


    class table_base::row_interface::fact_row_iterator : public table_base::row_iterator_core {
        const row_interface & m_parent;
        unsigned m_index;
    protected:
        bool is_finished() const override { return m_index==m_parent.size(); }
    public:
        fact_row_iterator(const row_interface & row, bool finished) 
            : m_parent(row), m_index(finished ? row.size() : 0) {}

        table_element operator*() override {
            SASSERT(!is_finished());
            return m_parent[m_index];
        }

        void operator++() override {
            m_index++;
            SASSERT(m_index<=m_parent.size());
        }
    };

    table_base::row_iterator table_base::row_interface::begin() const {
        return row_iterator(alloc(fact_row_iterator, *this, false));
    }
    table_base::row_iterator table_base::row_interface::end() const {
        return row_iterator(alloc(fact_row_iterator, *this, true));
    }

    void table_base::row_interface::get_fact(table_fact & result) const {
        result.reset();
        unsigned n = size();
        for (unsigned i = 0; i < n; i++) {
            result.push_back((*this)[i]);
        }
    }


    void table_base::row_interface::display(std::ostream & out) const {
        table_fact fact;
        get_fact(fact);
        print_container(fact, out);
        out << "\n";
    }

    void table_base::to_formula(relation_signature const& sig, expr_ref& fml) const {
        // iterate over rows and build disjunction
        ast_manager & m = fml.get_manager();
        expr_ref_vector disjs(m);
        expr_ref_vector conjs(m);
        dl_decl_util util(m);
        bool_rewriter brw(m);
        table_fact fact;
        for (row_interface const& r : *this) {
            r.get_fact(fact);
            conjs.reset();
            for (unsigned i = 0; i < fact.size(); ++i) {
                conjs.push_back(m.mk_eq(m.mk_var(i, sig[i]), util.mk_numeral(fact[i], sig[i])));
            }
            brw.mk_and(conjs.size(), conjs.data(), fml);
            disjs.push_back(fml);
        }
        brw.mk_or(disjs.size(), disjs.data(), fml);        
    }
}
