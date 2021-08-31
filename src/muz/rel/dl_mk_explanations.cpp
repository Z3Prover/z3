/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_mk_explanations.cpp

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-11-08.

Revision History:

--*/


#include <sstream>
#include "ast/ast_pp.h"
#include "ast/ast_smt_pp.h"
#include "muz/rel/dl_finite_product_relation.h"
#include "muz/rel/dl_product_relation.h"
#include "muz/rel/dl_sieve_relation.h"
#include "muz/rel/dl_mk_explanations.h"

namespace datalog {

    // -----------------------------------
    //
    // explanation_relation_plugin declaration
    //
    // -----------------------------------

    class explanation_relation;

    class explanation_relation_plugin : public relation_plugin {
        friend class explanation_relation;

        class join_fn;
        class project_fn;
        class rename_fn;
        class union_fn;
        class foreign_union_fn;
        class assignment_filter_fn;
        class negation_filter_fn;
        class intersection_filter_fn;

        bool m_relation_level_explanations;

        func_decl_ref m_union_decl;

        vector<ptr_vector<explanation_relation> > m_pool;


        app * mk_union(app * a1, app * a2) {
            return get_ast_manager().mk_app(m_union_decl, a1, a2);
        }

    public:
        static symbol get_name(bool relation_level) {
            return symbol(relation_level ? "relation_explanation" : "fact_explanation");
        }

        explanation_relation_plugin(bool relation_level, relation_manager & manager) 
            : relation_plugin(get_name(relation_level), manager),
            m_relation_level_explanations(relation_level),
            m_union_decl(mk_explanations::get_union_decl(get_context()), get_ast_manager()) {}

        ~explanation_relation_plugin() override {
            for (unsigned i = 0; i < m_pool.size(); ++i) {
                for (unsigned j = 0; j < m_pool[i].size(); ++j) {
                    dealloc(m_pool[i][j]);
                }
            }
        }

        bool can_handle_signature(const relation_signature & s) override {
            unsigned n=s.size();
            for (unsigned i=0; i<n; i++) {
                if (!get_context().get_decl_util().is_rule_sort(s[i])) {
                    return false;
                }
            }
            return true;
        }
        
        relation_base * mk_empty(const relation_signature & s) override;

        void recycle(explanation_relation* r);

    protected:

        relation_join_fn * mk_join_fn(const relation_base & t1, const relation_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) override;
        relation_transformer_fn * mk_project_fn(const relation_base & t, unsigned col_cnt,
            const unsigned * removed_cols) override;
        relation_transformer_fn * mk_rename_fn(const relation_base & t, unsigned permutation_cycle_len,
            const unsigned * permutation_cycle) override;
        relation_union_fn * mk_union_fn(const relation_base & tgt, const relation_base & src,
            const relation_base * delta) override;
        relation_mutator_fn * mk_filter_interpreted_fn(const relation_base & t, app * condition) override;
        relation_intersection_filter_fn * mk_filter_by_negation_fn(const relation_base & t,
            const relation_base & negated_obj, unsigned joined_col_cnt,
            const unsigned * t_cols, const unsigned * negated_cols) override;
        relation_intersection_filter_fn * mk_filter_by_intersection_fn(const relation_base & t,
                const relation_base & src, unsigned joined_col_cnt,
                const unsigned * t_cols, const unsigned * src_cols) override;

    };


    // -----------------------------------
    //
    // explanation_relation
    //
    // -----------------------------------

    class explanation_relation : public relation_base {
        friend class explanation_relation_plugin;
        friend class explanation_relation_plugin::join_fn;
        friend class explanation_relation_plugin::project_fn;
        friend class explanation_relation_plugin::rename_fn;
        friend class explanation_relation_plugin::union_fn;
        friend class explanation_relation_plugin::foreign_union_fn;
        friend class explanation_relation_plugin::assignment_filter_fn;
        friend class explanation_relation_plugin::intersection_filter_fn;

        bool m_empty;
        /**
           Valid only if \c !m_empty.

           Zero elements mean undefined.
        */
        relation_fact m_data;

        explanation_relation(explanation_relation_plugin & p, const relation_signature & s) 
                : relation_base(p, s), m_empty(true), m_data(p.get_ast_manager()) {
                    
            DEBUG_CODE(
                unsigned sz = s.size();
                for (unsigned i=0;i<sz; i++) {
                    SASSERT( p.get_context().get_decl_util().is_rule_sort(s[i]) );
                }
                );
        }

        void assign_data(const relation_fact & f) {
            m_empty = false;

            unsigned n=get_signature().size();
            SASSERT(f.size()==n);
            m_data.reset();
            m_data.append(n, f.data());
        }
        void set_undefined() {
            m_empty = false;
            m_data.reset();
            m_data.resize(get_signature().size());
        }
        void unite_with_data(const relation_fact & f) {
            if (empty()) {
                assign_data(f);
                return;
            }
            unsigned n=get_signature().size();
            SASSERT(f.size()==n);
            for (unsigned i=0; i<n; i++) {
                SASSERT(!is_undefined(i));
                m_data[i] = get_plugin().mk_union(m_data[i], f[i]);
            }
        }

        void deallocate() override {
            get_plugin().recycle(this);
        }

    public:

        explanation_relation_plugin & get_plugin() const { 
            return static_cast<explanation_relation_plugin &>(relation_base::get_plugin());
        }

        void to_formula(expr_ref& fml) const override {
            ast_manager& m = fml.get_manager();
            fml = m.mk_eq(m.mk_var(0, m_data[0]->get_sort()), m_data[0]);
        }

        bool is_undefined(unsigned col_idx) const {
            return m_data[col_idx]==nullptr;
        }
        bool no_undefined() const {
            if (empty()) {
                return true;
            }
            unsigned n = get_signature().size();
            for (unsigned i=0; i<n; i++) {
                if (is_undefined(i)) {
                    return false;
                }
            }
            return true;
        }

        bool empty() const override { return m_empty; }

        void reset() override {
            m_empty = true;
        }

        void add_fact(const relation_fact & f) override {
            SASSERT(empty());
            assign_data(f);
        }

        bool contains_fact(const relation_fact & f) const override {
            UNREACHABLE();
            throw 0;
        }

        explanation_relation * clone() const override {
            explanation_relation * res = static_cast<explanation_relation *>(get_plugin().mk_empty(get_signature()));
            res->m_empty = m_empty;
            SASSERT(res->m_data.empty());
            res->m_data.append(m_data);
            return res;
        }

        relation_base * complement(func_decl* pred) const override {
            explanation_relation * res = static_cast<explanation_relation *>(get_plugin().mk_empty(get_signature()));
            if (empty()) {
                res->set_undefined();
            }
            return res;
        }

        void display_explanation(app * expl, std::ostream & out) const {
            if (expl) {
                //TODO: some nice explanation output
                ast_smt_pp pp(get_plugin().get_ast_manager());
                pp.display_expr_smt2(out, expl);
            }
            else {
                out << "<undefined>";
            }
        }

        void display(std::ostream & out) const override {
            if (empty()) {
                out << "<empty explanation relation>\n";
                return;
            }
            unsigned sz = get_signature().size();
            for (unsigned i=0; i<sz; i++) {
                if (i!=0) {
                    out << ", ";
                }
                display_explanation(m_data[0], out);
            }
            out << "\n";
        }

        virtual unsigned get_size_estimate() const { return empty() ? 0 : 1; }
    };


    // -----------------------------------
    //
    // explanation_relation_plugin
    //
    // -----------------------------------


    relation_base * explanation_relation_plugin::mk_empty(const relation_signature & s) {
        if (m_pool.size() > s.size() && !m_pool[s.size()].empty()) {
            explanation_relation* r = m_pool[s.size()].back();
            m_pool[s.size()].pop_back();
            r->m_empty = true;
            r->m_data.reset();
            return r;
        }
        return alloc(explanation_relation, *this, s);
    }

    void explanation_relation_plugin::recycle(explanation_relation* r) {
        relation_signature const& sig = r->get_signature();
        if (m_pool.size() <= sig.size()) {
            m_pool.resize(sig.size()+1);
        }
        m_pool[sig.size()].push_back(r);
    }


    class explanation_relation_plugin::join_fn : public convenient_relation_join_fn {
    public:
        join_fn(const relation_signature & sig1, const relation_signature & sig2)
            : convenient_relation_join_fn(sig1, sig2, 0, nullptr, nullptr) {}

        relation_base * operator()(const relation_base & r1_0, const relation_base & r2_0) override {
            const explanation_relation & r1 = static_cast<const explanation_relation &>(r1_0);
            const explanation_relation & r2 = static_cast<const explanation_relation &>(r2_0);
            explanation_relation_plugin & plugin = r1.get_plugin();

            explanation_relation * res = static_cast<explanation_relation *>(plugin.mk_empty(get_result_signature()));
            if (!r1.empty() && !r2.empty()) {
                res->m_empty = false;
                SASSERT(res->m_data.empty());
                res->m_data.append(r1.m_data);
                res->m_data.append(r2.m_data);
            }
            return res;
        }
    };

    relation_join_fn * explanation_relation_plugin::mk_join_fn(const relation_base & r1, const relation_base & r2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
        if (&r1.get_plugin()!=this || &r2.get_plugin()!=this) {
            return nullptr;
        }
        if (col_cnt!=0) {
            return nullptr;
        }
        return alloc(join_fn, r1.get_signature(), r2.get_signature());
    }


    class explanation_relation_plugin::project_fn : public convenient_relation_project_fn {
    public:
        project_fn(const relation_signature & sig, unsigned col_cnt, const unsigned * removed_cols)
            : convenient_relation_project_fn(sig, col_cnt, removed_cols) {}

        relation_base * operator()(const relation_base & r0) override {
            const explanation_relation & r = static_cast<const explanation_relation &>(r0);
            explanation_relation_plugin & plugin = r.get_plugin();

            explanation_relation * res = static_cast<explanation_relation *>(plugin.mk_empty(get_result_signature()));
            if (!r.empty()) {
                relation_fact proj_data = r.m_data;
                project_out_vector_columns(proj_data, m_removed_cols);
                res->assign_data(proj_data);
            }
            return res;
        }
    };

    relation_transformer_fn * explanation_relation_plugin::mk_project_fn(const relation_base & r, unsigned col_cnt, 
            const unsigned * removed_cols) {
        if (&r.get_plugin()!=this) {
            return nullptr;
        }
        return alloc(project_fn, r.get_signature(), col_cnt, removed_cols);
    }


    class explanation_relation_plugin::rename_fn : public convenient_relation_rename_fn {
    public:
        rename_fn(const relation_signature & sig, unsigned permutation_cycle_len, const unsigned * permutation_cycle)
            : convenient_relation_rename_fn(sig, permutation_cycle_len, permutation_cycle) {}

        relation_base * operator()(const relation_base & r0) override {
            const explanation_relation & r = static_cast<const explanation_relation &>(r0);
            explanation_relation_plugin & plugin = r.get_plugin();

            explanation_relation * res = static_cast<explanation_relation *>(plugin.mk_empty(get_result_signature()));
            if (!r.empty()) {
                relation_fact permutated_data = r.m_data;
                permutate_by_cycle(permutated_data, m_cycle);
                res->assign_data(permutated_data);
            }
            return res;
        }
    };

    relation_transformer_fn * explanation_relation_plugin::mk_rename_fn(const relation_base & r, 
            unsigned permutation_cycle_len, const unsigned * permutation_cycle) {
        return alloc(rename_fn, r.get_signature(), permutation_cycle_len, permutation_cycle);
    }


    class explanation_relation_plugin::union_fn : public relation_union_fn {
        scoped_ptr<relation_union_fn> m_delta_union_fun;
    public:
        void operator()(relation_base & tgt0, const relation_base & src0, relation_base * delta0) override {
            explanation_relation & tgt = static_cast<explanation_relation &>(tgt0);
            const explanation_relation & src = static_cast<const explanation_relation &>(src0);
            explanation_relation * delta = delta0 ? static_cast<explanation_relation *>(delta0) : nullptr;
            explanation_relation_plugin & plugin = tgt.get_plugin();

            if (!src.no_undefined() || !tgt.no_undefined() || (delta && !delta->no_undefined())) {
                throw default_exception("explanations are not supported with undefined predicates");
            }
            if (src.empty()) {
                return;
            }
            if (plugin.m_relation_level_explanations) {
                tgt.unite_with_data(src.m_data);
                if (delta) {
                    if (!m_delta_union_fun) {
                        m_delta_union_fun = plugin.get_manager().mk_union_fn(*delta, src);
                        SASSERT(m_delta_union_fun);
                    }
                    (*m_delta_union_fun)(*delta, src);
                }
            }
            else {
                if (tgt.empty()) {
                    tgt.assign_data(src.m_data);
                    if (delta && delta->empty()) {
                        delta->assign_data(src.m_data);
                    }
                }
            }
        }
    };

    class explanation_relation_plugin::foreign_union_fn : public relation_union_fn {
        scoped_ptr<relation_union_fn> m_delta_union_fun;
    public:
        void operator()(relation_base & tgt0, const relation_base & src, relation_base * delta0) override {
            explanation_relation & tgt = static_cast<explanation_relation &>(tgt0);
            explanation_relation * delta = delta0 ? static_cast<explanation_relation *>(delta0) : nullptr;

            if (src.empty()) {
                return;
            }
            tgt.set_undefined();
            if (delta) {
                delta->set_undefined();
            }
        }
    };

    relation_union_fn * explanation_relation_plugin::mk_union_fn(const relation_base & tgt, const relation_base & src, 
            const relation_base * delta) {
        if (!check_kind(tgt) || (delta && !check_kind(*delta))) {
            return nullptr;
        }
        if (!check_kind(src)) {
            //this is to handle the product relation
            return alloc(foreign_union_fn);
        }
        return alloc(union_fn);
    }

    class explanation_relation_plugin::assignment_filter_fn : public relation_mutator_fn {
        ast_manager & m_manager;
        var_subst & m_subst;
        unsigned m_col_idx;
        app_ref m_new_rule;
    public:
        assignment_filter_fn(context & ctx, unsigned col_idx, app_ref new_rule) 
            : m_manager(ctx.get_manager()), 
              m_subst(ctx.get_var_subst()), 
              m_col_idx(col_idx), 
              m_new_rule(std::move(new_rule)) {}

        void not_handled() {
            throw default_exception("explanations are not supported with undefined predicates");
        }

        void operator()(relation_base & r0) override {
            explanation_relation & r = static_cast<explanation_relation &>(r0);

            if (!r.is_undefined(m_col_idx)) {
                not_handled();
            }

            unsigned sz = r.get_signature().size();
            ptr_vector<expr> subst_arg;
            subst_arg.resize(sz);
            unsigned ofs = sz-1;
            for (unsigned i=0; i<sz; i++) {
                if (r.is_undefined(i) && contains_var(m_new_rule, i))
                    not_handled();
                subst_arg[ofs-i] = r.m_data.get(i);
            }
            expr_ref res = m_subst(m_new_rule, subst_arg.size(), subst_arg.data());
            r.m_data[m_col_idx] = to_app(res);
        }
    };

    relation_mutator_fn * explanation_relation_plugin::mk_filter_interpreted_fn(const relation_base & r, 
            app * cond) {
        if (&r.get_plugin() != this) {
            TRACE("dl", tout << "not same plugin\n";);
            return nullptr;
        }
        ast_manager & m = get_ast_manager();
        if (!m.is_eq(cond)) {
            TRACE("dl", tout << "not equality " << mk_pp(cond, m) << "\n";);
            return nullptr;
        }
        expr * arg1 = cond->get_arg(0);
        expr * arg2 = cond->get_arg(1);

        if (is_var(arg2)) {
            std::swap(arg1, arg2);
        }

        if (!is_var(arg1) || !is_app(arg2)) {
            TRACE("dl", tout << "not variable assignemnt\n";);
            return nullptr;
        }
        var * col_var = to_var(arg1);
        app * new_rule = to_app(arg2);
        if (!get_context().get_decl_util().is_rule_sort(col_var->get_sort())) {
            TRACE("dl", tout << "not rule sort\n";);
            return nullptr;
        }
        unsigned col_idx = col_var->get_idx();

        return alloc(assignment_filter_fn, get_context(), col_idx, app_ref(new_rule, get_ast_manager()));
    }


    class explanation_relation_plugin::negation_filter_fn : public relation_intersection_filter_fn {
    public:
        void operator()(relation_base & r, const relation_base & neg) override {
            if (!neg.empty()) {
                r.reset();
            }
        }
    };

    relation_intersection_filter_fn * explanation_relation_plugin::mk_filter_by_negation_fn(const relation_base & r, 
            const relation_base & neg, unsigned joined_col_cnt, const unsigned * t_cols, 
            const unsigned * negated_cols) {
        if (&r.get_plugin()!=this || &neg.get_plugin()!=this) {
            return nullptr;
        }
        return alloc(negation_filter_fn);
    }

    class explanation_relation_plugin::intersection_filter_fn : public relation_intersection_filter_fn {
        func_decl_ref m_union_decl;
    public:
        intersection_filter_fn(explanation_relation_plugin & plugin)
            : m_union_decl(plugin.m_union_decl) {}

        void operator()(relation_base & tgt0, const relation_base & src0) override {
            explanation_relation & tgt = static_cast<explanation_relation &>(tgt0);
            const explanation_relation & src = static_cast<const explanation_relation &>(src0);

            if (src.empty()) {
                tgt.reset();
                return;
            }
            if (tgt.empty()) {
                return;
            }
            unsigned sz = tgt.get_signature().size();
            for (unsigned i=0; i<sz; i++) {
                if (src.is_undefined(i)) {
                    continue;
                }
                app * curr_src = src.m_data.get(i);
                if (tgt.is_undefined(i)) {
                    tgt.m_data.set(i, curr_src);
                    continue;
                }
                app * curr_tgt = tgt.m_data.get(i);
                if (curr_tgt->get_decl()==m_union_decl.get()) {
                    if (curr_tgt->get_arg(0)==curr_src || curr_tgt->get_arg(1)==curr_src) {
                        tgt.m_data.set(i, curr_src);
                        continue;
                    }
                }
                //the intersection is imprecise because we do nothing here, but it is good enough for
                //the purpose of explanations
            }
        }
    };

    relation_intersection_filter_fn * explanation_relation_plugin::mk_filter_by_intersection_fn(
            const relation_base & tgt, const relation_base & src, unsigned joined_col_cnt, 
            const unsigned * tgt_cols, const unsigned * src_cols) {
        if (&tgt.get_plugin()!=this || &src.get_plugin()!=this) {
            return nullptr;
        }
        //this checks the join is one to one on all columns
        if (tgt.get_signature()!=src.get_signature()
            || joined_col_cnt!=tgt.get_signature().size()
            || !containers_equal(tgt_cols, tgt_cols+joined_col_cnt, src_cols, src_cols+joined_col_cnt)) {
            return nullptr;
        }
        counter ctr;
        ctr.count(joined_col_cnt, tgt_cols);
        if (ctr.get_max_counter_value()>1 || (joined_col_cnt && ctr.get_max_positive()!=joined_col_cnt-1)) {
            return nullptr;
        }
        return alloc(intersection_filter_fn, *this);
    }


    // -----------------------------------
    //
    // mk_explanations
    //
    // -----------------------------------


    mk_explanations::mk_explanations(context & ctx) 
        : plugin(50000),
          m_manager(ctx.get_manager()),
          m_context(ctx),
          m_decl_util(ctx.get_decl_util()),
          m_relation_level(ctx.explanations_on_relation_level()),
          m_pinned(m_manager) {
        m_e_sort = m_decl_util.mk_rule_sort();
        m_pinned.push_back(m_e_sort);

        relation_manager & rmgr = ctx.get_rel_context()->get_rmanager();
        symbol er_symbol = explanation_relation_plugin::get_name(m_relation_level);
        m_er_plugin = static_cast<explanation_relation_plugin *>(rmgr.get_relation_plugin(er_symbol));
        if (!m_er_plugin) {
            m_er_plugin = alloc(explanation_relation_plugin, m_relation_level, rmgr);
            rmgr.register_plugin(m_er_plugin);
            if (!m_relation_level) {
                DEBUG_CODE(
                    finite_product_relation_plugin * dummy;
                    SASSERT(!rmgr.try_get_finite_product_relation_plugin(*m_er_plugin, dummy));
                    );
                rmgr.register_plugin(alloc(finite_product_relation_plugin, *m_er_plugin, rmgr));
            }
        }
        DEBUG_CODE(
            if (!m_relation_level) {
                finite_product_relation_plugin * dummy;
                SASSERT(rmgr.try_get_finite_product_relation_plugin(*m_er_plugin, dummy));
            }
        );
    }

    mk_explanations::~mk_explanations() {
    }

    func_decl * mk_explanations::get_union_decl(context & ctx) {
        ast_manager & m = ctx.get_manager();
        sort_ref s(ctx.get_decl_util().mk_rule_sort(), m);
        //can it happen that the function name would collide with some other symbol?
        //if functions can be overloaded by their ranges, it should be fine.
        return m.mk_func_decl(symbol("e_union"), s, s, s);
    }

    void mk_explanations::assign_rel_level_kind(func_decl * e_decl, func_decl * orig) {
        SASSERT(m_relation_level);

        relation_manager & rmgr = m_context.get_rel_context()->get_rmanager();
        unsigned sz = e_decl->get_arity();
        relation_signature sig;
        rmgr.from_predicate(e_decl, sig);

        bool_vector inner_sieve(sz-1, true);
        inner_sieve.push_back(false);

        bool_vector expl_sieve(sz-1, false);
        expl_sieve.push_back(true);

        sieve_relation_plugin & sieve_plugin = sieve_relation_plugin::get_plugin(rmgr);

        family_id inner_kind = rmgr.get_requested_predicate_kind(orig); //may be null_family_id
        family_id inner_sieve_kind = sieve_plugin.get_relation_kind(sig, inner_sieve, inner_kind);
        family_id expl_kind = m_er_plugin->get_kind();
        family_id expl_sieve_kind = sieve_plugin.get_relation_kind(sig, expl_sieve, expl_kind);

        rel_spec product_spec;
        product_spec.push_back(inner_sieve_kind);
        product_spec.push_back(expl_sieve_kind);

        family_id pred_kind = 
            product_relation_plugin::get_plugin(rmgr).get_relation_kind(sig, product_spec);

        rmgr.set_predicate_kind(e_decl, pred_kind);
    }

    func_decl * mk_explanations::get_e_decl(func_decl * orig_decl) {
        auto& value = m_e_decl_map.insert_if_not_there(orig_decl, 0);
        if (value == nullptr) {
            relation_signature e_domain;
            e_domain.append(orig_decl->get_arity(), orig_decl->get_domain());
            e_domain.push_back(m_e_sort);
            func_decl * new_decl = m_context.mk_fresh_head_predicate(orig_decl->get_name(), symbol("expl"), 
                e_domain.size(), e_domain.data(), orig_decl);
            m_pinned.push_back(new_decl);
            value = new_decl;

            if (m_relation_level) {
                assign_rel_level_kind(new_decl, orig_decl);
            }
        }
        return value;
    }

    app * mk_explanations::get_e_lit(app * lit, unsigned e_var_idx) {
        expr_ref_vector args(m_manager);
        func_decl * e_decl = get_e_decl(lit->get_decl());
        args.append(lit->get_num_args(), lit->get_args());
        args.push_back(m_manager.mk_var(e_var_idx, m_e_sort));
        return m_manager.mk_app(e_decl, args.data());
    }

    symbol mk_explanations::get_rule_symbol(rule * r) {
        if (r->name() == symbol::null) {
            std::stringstream sstm;
            r->display(m_context, sstm);
            std::string res = sstm.str();
            res = res.substr(0, res.find_last_not_of('\n')+1);
            return symbol(res.c_str());
        }
        else {
            return r->name();
        }
    }

    rule * mk_explanations::get_e_rule(rule * r) {
        rule_counter ctr;
        ctr.count_rule_vars(r);
        unsigned max_var;
        unsigned next_var = ctr.get_max_positive(max_var) ? (max_var+1) : 0;
        unsigned head_var = next_var++;
        app_ref e_head(get_e_lit(r->get_head(), head_var), m_manager);

        app_ref_vector e_tail(m_manager);
        bool_vector neg_flags;
        unsigned pos_tail_sz = r->get_positive_tail_size();
        for (unsigned i=0; i<pos_tail_sz; i++) {
            unsigned e_var = next_var++;
            e_tail.push_back(get_e_lit(r->get_tail(i), e_var));
            neg_flags.push_back(false);
        }
        unsigned tail_sz = r->get_tail_size();
        for (unsigned i=pos_tail_sz; i<tail_sz; i++) {
            e_tail.push_back(r->get_tail(i));
            neg_flags.push_back(r->is_neg_tail(i));
        }

        symbol rule_repr = get_rule_symbol(r);

        expr_ref_vector rule_expr_args(m_manager);
        for (unsigned tail_idx=0; tail_idx<pos_tail_sz; tail_idx++) {
            app * tail = e_tail.get(tail_idx);
            if (true || m_relation_level) {
                //this adds the explanation term of the tail
                rule_expr_args.push_back(tail->get_arg(tail->get_num_args()-1));
            }
            else {
                //this adds argument values and the explanation term
                //(values will be substituted for variables at runtime by the finite_product_relation)
                rule_expr_args.append(tail->get_num_args(), tail->get_args());
            }
        }
        //rule_expr contains rule function with string representation of the rule as symbol and
        //for each positive uninterpreted tail it contains its argument values and its explanation term
        expr * rule_expr = m_decl_util.mk_rule(rule_repr, rule_expr_args.size(), rule_expr_args.data());

        app_ref e_record(m_manager.mk_eq(m_manager.mk_var(head_var, m_e_sort), rule_expr), m_manager);
        e_tail.push_back(e_record);
        neg_flags.push_back(false);
        SASSERT(e_tail.size()==neg_flags.size());

        return m_context.get_rule_manager().mk(e_head, e_tail.size(), e_tail.data(), neg_flags.data());
    }

    void mk_explanations::transform_rules(const rule_set & src, rule_set & dst) {
        rule_set::iterator rit = src.begin();
        rule_set::iterator rend = src.end();
        for (; rit!=rend; ++rit) {
            rule * e_rule = get_e_rule(*rit);
            dst.add_rule(e_rule);
        }

        //add rules that will (for output predicates) copy facts from explained relations back to
        //the original ones
        expr_ref_vector lit_args(m_manager);
        decl_set::iterator pit = src.get_output_predicates().begin();
        decl_set::iterator pend = src.get_output_predicates().end();
        for (; pit != pend; ++pit) {
            func_decl * orig_decl = *pit;

            lit_args.reset();
            unsigned arity = orig_decl->get_arity();
            for (unsigned i=0; i<arity; i++) {
                lit_args.push_back(m_manager.mk_var(i, orig_decl->get_domain(i)));
            }
            app_ref orig_lit(m_manager.mk_app(orig_decl, lit_args.data()), m_manager);
            app_ref e_lit(get_e_lit(orig_lit, arity), m_manager);
            app * tail[] = { e_lit.get() };
            dst.add_rule(m_context.get_rule_manager().mk(orig_lit, 1, tail, nullptr));
        }
    }

    void mk_explanations::translate_rel_level_relation(relation_manager & rmgr, relation_base & orig, 
            relation_base & e_rel) {
        SASSERT(m_e_fact_relation);
        SASSERT(e_rel.get_plugin().is_product_relation());

        product_relation & prod_rel = static_cast<product_relation &>(e_rel);
        SASSERT(prod_rel.size()==2);
       
        if (!prod_rel[0].get_plugin().is_sieve_relation())
            throw default_exception("explanations are not supported with undefined predicates");
        if (!prod_rel[1].get_plugin().is_sieve_relation())
            throw default_exception("explanations are not supported with undefined predicates");
        sieve_relation * srels[] = { 
            static_cast<sieve_relation *>(&prod_rel[0]),
            static_cast<sieve_relation *>(&prod_rel[1]) };
        if (&srels[0]->get_inner().get_plugin()==m_er_plugin) {
            std::swap(srels[0], srels[1]);
        }
        SASSERT(&srels[0]->get_inner().get_plugin()==&orig.get_plugin());
        SASSERT(&srels[1]->get_inner().get_plugin()==m_er_plugin);

        relation_base & new_orig = srels[0]->get_inner();
        explanation_relation & expl_rel = static_cast<explanation_relation &>(srels[1]->get_inner());

        {
            scoped_ptr<relation_union_fn> orig_union_fun = rmgr.mk_union_fn(new_orig, orig);
            SASSERT(orig_union_fun);
            (*orig_union_fun)(new_orig, orig);
        }

        {
            scoped_ptr<relation_union_fn> expl_union_fun = rmgr.mk_union_fn(expl_rel, *m_e_fact_relation);
            SASSERT(expl_union_fun);
            (*expl_union_fun)(expl_rel, *m_e_fact_relation);
        }
    }

    void mk_explanations::transform_facts(relation_manager & rmgr, rule_set const& src, rule_set& dst) {

        if (!m_e_fact_relation) {
            relation_signature expl_singleton_sig;
            expl_singleton_sig.push_back(m_e_sort);

            relation_base * expl_singleton = rmgr.mk_empty_relation(expl_singleton_sig, m_er_plugin->get_kind());
            relation_fact es_fact(m_manager);
            es_fact.push_back(m_decl_util.mk_fact(symbol("fact")));
            expl_singleton->add_fact(es_fact);

            SASSERT(&expl_singleton->get_plugin()==m_er_plugin);
            m_e_fact_relation = static_cast<explanation_relation *>(expl_singleton);
        }
        func_decl_set predicates(m_context.get_predicates());
        for (func_decl* orig_decl : predicates) {
            TRACE("dl", tout << mk_pp(orig_decl, m_manager) << "\n";);
            func_decl * e_decl = get_e_decl(orig_decl);

            if (!rmgr.try_get_relation(orig_decl) &&
                !src.contains(orig_decl)) {
                // there are no facts or rules for this predicate
                continue;
            }

            dst.inherit_predicate(src, orig_decl, e_decl);

            relation_base & orig_rel = rmgr.get_relation(orig_decl);
            relation_base & e_rel = rmgr.get_relation(e_decl);
            SASSERT(e_rel.empty()); //the e_rel should be a new relation
            
            if (m_relation_level) {
                translate_rel_level_relation(rmgr, orig_rel, e_rel);
            }
            else {
                scoped_ptr<relation_join_fn> product_fun = rmgr.mk_join_fn(orig_rel, *m_e_fact_relation, 0, nullptr, nullptr);
                SASSERT(product_fun);
                scoped_rel<relation_base> aux_extended_rel = (*product_fun)(orig_rel, *m_e_fact_relation);
                TRACE("dl", tout << aux_extended_rel << " " << aux_extended_rel->get_plugin().get_name() << "\n";
                      tout << e_rel.get_plugin().get_name() << "\n";);
                scoped_ptr<relation_union_fn> union_fun = rmgr.mk_union_fn(e_rel, *aux_extended_rel);
                TRACE("dl", tout << union_fun << "\n";);
                SASSERT(union_fun);
                (*union_fun)(e_rel, *aux_extended_rel);
            }
        }
    }

    rule_set * mk_explanations::operator()(rule_set const & source) {

        if (source.empty()) {
            return nullptr;
        }
        if (!m_context.generate_explanations()) {
            return nullptr;
        }
        scoped_ptr<rule_set> res = alloc(rule_set, m_context);
        transform_facts(m_context.get_rel_context()->get_rmanager(), source, *res);
        transform_rules(source, *res);
        return res.detach();
    }
    
};

