/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_context.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-18.

Revision History:

--*/

#include<sstream>
#include<limits>
#include"arith_simplifier_plugin.h"
#include"basic_simplifier_plugin.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"dl_table.h"
#include"dl_table_relation.h"
#include"dl_rule_transformer.h"
#include"dl_mk_coi_filter.h"
#include"dl_mk_explanations.h"
#include"dl_mk_filter_rules.h"
#include"dl_mk_interp_tail_simplifier.h"
#include"dl_mk_rule_inliner.h"
#include"dl_mk_simple_joins.h"
#include"dl_mk_similarity_compressor.h"
#include"dl_mk_unbound_compressor.h"
#include"dl_mk_subsumption_checker.h"
#include"dl_compiler.h"
#include"dl_instruction.h"
#include"dl_context.h"
#include"for_each_expr.h"
#include"ast_smt_pp.h"
#include"ast_smt2_pp.h"
#include"expr_functors.h"
#include"dl_mk_partial_equiv.h"
#include"dl_mk_bit_blast.h"
#include"dl_mk_array_blast.h"
#include"datatype_decl_plugin.h"
#include"expr_abstract.h"


namespace datalog {

    // -----------------------------------
    //
    // context::sort_domain
    //
    // -----------------------------------

    class context::sort_domain {
    private:
        sort_kind m_kind;
    protected:
        sort_ref m_sort;
        bool m_limited_size;
        uint64 m_size;

        sort_domain(sort_kind k, context & ctx, sort * s)
            : m_kind(k), m_sort(s, ctx.get_manager()) {
                m_limited_size = ctx.get_decl_util().try_get_size(s, m_size);
        }
    public:
        virtual ~sort_domain() {}

        sort_kind get_kind() const { return m_kind; }
        virtual unsigned get_constant_count() const = 0;
        virtual void print_element(finite_element el_num, std::ostream & out) = 0;
    };

    class context::symbol_sort_domain : public sort_domain {
        typedef map<symbol,       finite_element,   symbol_hash_proc, symbol_eq_proc> sym2num;
        typedef svector<symbol> num2sym;

        sym2num m_el_numbers;
        num2sym m_el_names;
    public:
        symbol_sort_domain(context & ctx, sort * s) : sort_domain(SK_SYMBOL, ctx, s) {}

        finite_element get_number(symbol sym) {
            //we number symbols starting from zero, so table->size() is equal to the
            //index of the symbol to be added next

            unsigned newIdx = m_el_numbers.size();

            sym2num::entry* sym_e = m_el_numbers.insert_if_not_there2(sym, newIdx);
            unsigned idx=sym_e->get_data().m_value;

            if (idx==newIdx) {
                m_el_names.push_back(sym);
                SASSERT(m_el_names.size()==m_el_numbers.size());
            }

            if (m_limited_size && idx>=m_size) {
                std::stringstream sstm;
                sstm << "sort " << m_sort->get_name() << " contains more constants than its declared size " << m_size;
                throw default_exception(sstm.str());
            }
            return idx;
        }

        virtual unsigned get_constant_count() const {
            return m_el_names.size();
        }
        virtual void print_element(finite_element el_num, std::ostream & out) {
            if (el_num>=m_el_names.size()) {
                out << el_num;
                return;
            }
            out << m_el_names[el_num];
        }
    };

    class context::uint64_sort_domain : public sort_domain {
        typedef map<uint64,       finite_element,   uint64_hash, default_eq<uint64> > el2num;
        typedef svector<uint64> num2el;

        el2num m_el_numbers;
        num2el m_el_names;
    public:
        uint64_sort_domain(context & ctx, sort * s) : sort_domain(SK_UINT64, ctx, s) {}

        finite_element get_number(uint64 el) {
            //we number symbols starting from zero, so table->size() is equal to the
            //index of the symbol to be added next

            unsigned newIdx = m_el_numbers.size();

            el2num::entry* sym_e = m_el_numbers.insert_if_not_there2(el, newIdx);
            unsigned idx=sym_e->get_data().m_value;

            if (idx==newIdx) {
                m_el_names.push_back(el);
                SASSERT(m_el_names.size()==m_el_numbers.size());
            }

            if (m_limited_size && idx>=m_size) {
                std::stringstream sstm;
                sstm << "sort " << m_sort->get_name() << " contains more constants than its declared size " << m_size;
                throw default_exception(sstm.str());
            }
            return idx;
        }
        virtual unsigned get_constant_count() const {
            return m_el_names.size();
        }
        virtual void print_element(finite_element el_num, std::ostream & out) {
            if (el_num >= m_el_names.size()) {
                out << "<unk " << m_sort->get_name() << ":" << el_num << '>';
                return;
            }
            out << m_el_names[el_num];
        }
    };

    // -----------------------------------
    //
    // trail stack for restoring rules
    //
    // -----------------------------------

    class context::restore_rules : public trail<context> {
        rule_set* m_old_rules;
        void reset() { 
            dealloc(m_old_rules); 
            m_old_rules = 0; 
        }
    public:
        restore_rules(rule_set& r): m_old_rules(alloc(rule_set, r)) {}

        virtual ~restore_rules() {}
        
        virtual void undo(context& ctx) {
            ctx.replace_rules(*m_old_rules);
            reset();
        }
    };

    template<typename Ctx, typename Vec>
    class restore_vec_size_trail : public trail<Ctx> {
        Vec& m_vector;
        unsigned m_old_size;
    public:
        restore_vec_size_trail(Vec& v): m_vector(v), m_old_size(v.size()) {}
        virtual ~restore_vec_size_trail() {}
        virtual void undo(Ctx& ctx) { m_vector.shrink(m_old_size); }
    };

    void context::push() {
        m_trail.push_scope();
        m_trail.push(restore_rules(m_rule_set));
        m_trail.push(restore_vec_size_trail<context,expr_ref_vector>(m_background));
    }

    void context::pop() {
        if (m_trail.get_num_scopes() == 0) {
            throw default_exception("there are no backtracking points to pop to");
        }
        m_trail.pop_scope(1); 
    }

    // -----------------------------------
    //
    // context
    //
    // -----------------------------------

    context::context(ast_manager & m, smt_params& fp, params_ref const& pa):
        m(m),
        m_fparams(fp),
        m_params_ref(pa),
        m_params(m_params_ref),
        m_decl_util(m),
        m_rewriter(m),
        m_var_subst(m),
        m_rule_manager(*this),
        m_trail(*this),
        m_pinned(m),
        m_vars(m),
        m_rule_set(*this),
        m_rule_fmls(m),
        m_background(m),
        m_closed(false),
        m_saturation_was_run(false),
        m_last_answer(m),
        m_engine(LAST_ENGINE),
        m_cancel(false) {
        
        //register plugins for builtin tables
    }

    context::~context() {
        reset();
    }

    void context::reset() {
        m_trail.reset();
        m_rule_set.reset();
        m_argument_var_names.reset();
        m_preds.reset();
        m_preds_by_name.reset();
        reset_dealloc_values(m_sorts);
        m_pdr = 0;
        m_bmc = 0;
        m_rel = 0;
    }

    bool context::is_fact(app * head) const {
        return m_rule_manager.is_fact(head);
    }

    bool context::has_sort_domain(relation_sort s) const {
        return m_sorts.contains(s);
    }

    context::sort_domain & context::get_sort_domain(relation_sort s) {
        sort_domain * dom;
        TRUSTME( m_sorts.find(s, dom) );
        return *dom;
    }

    const context::sort_domain & context::get_sort_domain(relation_sort s) const {
        sort_domain * dom;
        TRUSTME( m_sorts.find(s, dom) );
        return *dom;
    }

    void context::register_finite_sort(sort * s, sort_kind k) {
        m_pinned.push_back(s);
        SASSERT(!m_sorts.contains(s));
        sort_domain * dom;
        switch (k) {
        case SK_SYMBOL:
            dom = alloc(symbol_sort_domain, *this, s);
            break;
        case SK_UINT64:
            dom = alloc(uint64_sort_domain, *this, s);
            break;
        default:
            UNREACHABLE();
        }
        m_sorts.insert(s, dom);
    }

    bool context::is_predicate(func_decl * pred) const {
        return m_preds.contains(pred);
    }

    func_decl * context::try_get_predicate_decl(symbol pred_name) const {
        func_decl * res;
        if (!m_preds_by_name.find(pred_name, res)) {
            return 0;
        }
        return res;
    }

    void context::register_variable(func_decl* var) {
        m_vars.push_back(m.mk_const(var));
    }

    expr_ref context::bind_variables(expr* fml, bool is_forall) {
        expr_ref result(m);
        app_ref_vector const & vars = m_vars;
        if (vars.empty()) {
            result = fml;
        }
        else {
            ptr_vector<sort> sorts;
            expr_abstract(m, 0, vars.size(), reinterpret_cast<expr*const*>(vars.c_ptr()), fml, result);
            get_free_vars(result, sorts);
            if (sorts.empty()) {
                result = fml;
            }
            else {
                svector<symbol> names;
                for (unsigned i = 0; i < sorts.size(); ++i) {
                    if (!sorts[i]) {
                        if (i < vars.size()) { 
                            sorts[i] = vars[i]->get_decl()->get_range();
                        }
                        else {
                            sorts[i] = m.mk_bool_sort();
                        }
                    }
                    if (i < vars.size()) {
                        names.push_back(vars[i]->get_decl()->get_name());
                    }
                    else {
                        names.push_back(symbol(i));
                    }
                }
                quantifier_ref q(m);
                sorts.reverse();
                q = m.mk_quantifier(is_forall, sorts.size(), sorts.c_ptr(), names.c_ptr(), result); 
                elim_unused_vars(m, q, result);
            }
        }
        return result;
    }

    void context::register_predicate(func_decl * decl, bool named) {
        if (m_preds.contains(decl)) {
            return;
        }
        m_pinned.push_back(decl);
        m_preds.insert(decl);
        if (named) {
            SASSERT(!m_preds_by_name.contains(decl->get_name()));
            m_preds_by_name.insert(decl->get_name(), decl);
        }
    }

    context::finite_element context::get_constant_number(relation_sort srt, symbol sym) {
        sort_domain & dom0 = get_sort_domain(srt);
        SASSERT(dom0.get_kind() == SK_SYMBOL);
        symbol_sort_domain & dom = static_cast<symbol_sort_domain &>(dom0);
        return dom.get_number(sym);
    }

    context::finite_element context::get_constant_number(relation_sort srt, uint64 el) {
        sort_domain & dom0 = get_sort_domain(srt);
        SASSERT(dom0.get_kind()==SK_UINT64);
        uint64_sort_domain & dom = static_cast<uint64_sort_domain &>(dom0);
        return dom.get_number(el);
    }

    void context::print_constant_name(relation_sort srt, uint64 num, std::ostream & out)
    {
        if (has_sort_domain(srt)) {
            SASSERT(num<=UINT_MAX);
            get_sort_domain(srt).print_element(static_cast<unsigned>(num), out);
        }
        else {
            out << num;
        }
    }

    bool context::try_get_sort_constant_count(relation_sort srt, uint64 & constant_count) {
        if (!has_sort_domain(srt)) {
            return false;
        }
        constant_count = get_sort_domain(srt).get_constant_count();
        return true;
    }

    uint64 context::get_sort_size_estimate(relation_sort srt) {
        if (get_decl_util().is_rule_sort(srt)) {
            return 1;
        }
        uint64 res;
        if (!try_get_sort_constant_count(srt, res)) {
            sort_size sz = srt->get_num_elements();
            if (sz.is_finite()) {
                res = sz.size();
            }
            else {
                res = std::numeric_limits<uint64>::max();
            }
        }
        return res;
    }

    void context::set_argument_names(const func_decl * pred, svector<symbol> var_names)
    {
        SASSERT(!m_argument_var_names.contains(pred));
        m_argument_var_names.insert(pred, var_names);
    }

    symbol context::get_argument_name(const func_decl * pred, unsigned arg_index)
    {
        pred2syms::obj_map_entry * e = m_argument_var_names.find_core(pred);
        if (!e) {
            std::stringstream name_stm;
            name_stm << '#' << arg_index;
            return symbol(name_stm.str().c_str());
        }
        SASSERT(arg_index < e->get_data().m_value.size());
        return e->get_data().m_value[arg_index];
    }


    void context::set_predicate_representation(func_decl * pred, unsigned relation_name_cnt, 
            symbol const * relation_names) {
        if (relation_name_cnt > 0) {
            ensure_rel();
            m_rel->set_predicate_representation(pred, relation_name_cnt, relation_names);
        }
    }

    func_decl * context::mk_fresh_head_predicate(symbol const & prefix, symbol const & suffix, 
            unsigned arity, sort * const * domain, func_decl* orig_pred) {
        func_decl* new_pred = 
            m.mk_fresh_func_decl(prefix, suffix, arity, domain, m.mk_bool_sort());

        register_predicate(new_pred);

        if (m_rel.get()) {
            m_rel->inherit_predicate_kind(new_pred, orig_pred);
        }
        return new_pred;
    }

    void context::set_output_predicate(func_decl * pred) { 
        ensure_rel();
        m_rel->set_output_predicate(pred);
    }

    bool context::is_output_predicate(func_decl * pred) {
        ensure_rel();
        return m_rel->is_output_predicate(pred); 
    }

    const decl_set & context::get_output_predicates() { 
        ensure_rel();
        return m_rel->get_output_predicates();
    }

    void context::add_rule(expr* rl, symbol const& name) {
        m_rule_fmls.push_back(rl);
        m_rule_names.push_back(name);
    }

    void context::flush_add_rules() {
        datalog::rule_manager& rm = get_rule_manager();
        datalog::rule_ref_vector rules(rm);
        for (unsigned i = 0; i < m_rule_fmls.size(); ++i) {
            rm.mk_rule(m_rule_fmls[i].get(), rules, m_rule_names[i]);
        }
        add_rules(rules);
        m_rule_fmls.reset();
        m_rule_names.reset();
    }

    //
    // Update a rule with a new.
    // It requires basic subsumption.
    // 
    void context::update_rule(expr* rl, symbol const& name) {
        datalog::rule_manager& rm = get_rule_manager();
        datalog::rule_ref_vector rules(rm);
        rm.mk_rule(rl, rules, name);
        if (rules.size() != 1) {
            std::stringstream strm;
            strm << "Rule " << name << " has a non-trivial body. It cannot be modified";
            throw default_exception(strm.str());
        }
        rule_ref r(rules[0].get(), rm);
        rule_ref_vector const& rls = m_rule_set.get_rules();
        rule* old_rule = 0;
        for (unsigned i = 0; i < rls.size(); ++i) {
            if (rls[i]->name() == name) {
                if (old_rule) {                    
                    std::stringstream strm;
                    strm << "Rule " << name << " occurs twice. It cannot be modified";
                    throw default_exception(strm.str());
                }
                old_rule = rls[i];                
            }
        }
        if (old_rule) {
            if (!check_subsumes(*old_rule, *r)) {
                std::stringstream strm;
                strm << "Old rule ";
                old_rule->display(*this, strm);
                strm << "does not subsume new rule ";
                r->display(*this, strm);
                throw default_exception(strm.str());
            }
            m_rule_set.del_rule(old_rule);
        }
        m_rule_set.add_rule(r);
    }

    bool context::check_subsumes(rule const& stronger_rule, rule const& weaker_rule) {
        if (stronger_rule.get_head() != weaker_rule.get_head()) {
            return false;
        }
        for (unsigned i = 0; i < stronger_rule.get_tail_size(); ++i) {
            app* t = stronger_rule.get_tail(i);
            bool found = false;
            for (unsigned j = 0; j < weaker_rule.get_tail_size(); ++j) {
                app* s = weaker_rule.get_tail(j);
                if (s == t) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                return false;
            }
        }
        return true;
    }

    unsigned context::get_num_levels(func_decl* pred) {
        switch(get_engine()) {
        case DATALOG_ENGINE:
            throw default_exception("get_num_levels is not supported for datalog engine");
        case PDR_ENGINE:
        case QPDR_ENGINE:
            ensure_pdr();
            return m_pdr->get_num_levels(pred);
        case BMC_ENGINE:
        case QBMC_ENGINE:
            throw default_exception("get_num_levels is not supported for bmc");
        case TAB_ENGINE:
            throw default_exception("get_num_levels is not supported for tab");
        default:
            throw default_exception("unknown engine");
        } 
    }

    expr_ref context::get_cover_delta(int level, func_decl* pred) {
        switch(get_engine()) {
        case DATALOG_ENGINE:
            throw default_exception("operation is not supported for datalog engine");
        case PDR_ENGINE:
        case QPDR_ENGINE:
            ensure_pdr();
            return m_pdr->get_cover_delta(level, pred);
        case BMC_ENGINE:
        case QBMC_ENGINE:
            throw default_exception("operation is not supported for BMC engine");
        case TAB_ENGINE:
            throw default_exception("operation is not supported for TAB engine");
        default:
            throw default_exception("unknown engine");
        } 
    }

    void context::add_cover(int level, func_decl* pred, expr* property) {
        switch(get_engine()) {
        case DATALOG_ENGINE:
            throw default_exception("operation is not supported for datalog engine");
        case PDR_ENGINE:
        case QPDR_ENGINE:
            ensure_pdr();
            m_pdr->add_cover(level, pred, property);
            break;
        case BMC_ENGINE:
        case QBMC_ENGINE:
            throw default_exception("operation is not supported for BMC engine");
        case TAB_ENGINE:
            throw default_exception("operation is not supported for TAB engine");
        default:
            throw default_exception("unknown engine");
        } 
    }

    void context::check_uninterpreted_free(rule_ref& r) {
        func_decl* f = 0;
        if (r->has_uninterpreted_non_predicates(f)) {
            std::stringstream stm;
            stm << "Uninterpreted '" 
                << f->get_name() 
                << "' in ";
            r->display(*this, stm);
            throw default_exception(stm.str());
        }
    }

    void context::check_quantifier_free(rule_ref& r) {
        if (r->has_quantifiers()) {
            std::stringstream stm;
            stm << "cannot process quantifiers in rule ";
            r->display(*this, stm);
            throw default_exception(stm.str());
        }
    }

    class context::contains_pred : public i_expr_pred {
        rule_manager const& m;
    public:
        contains_pred(rule_manager const& m): m(m) {}
        virtual ~contains_pred() {}

        virtual bool operator()(expr* e) {
            return is_app(e) && m.is_predicate(to_app(e));
        }
    };

    void context::check_existential_tail(rule_ref& r) {
        unsigned ut_size = r->get_uninterpreted_tail_size();
        unsigned t_size  = r->get_tail_size();   
        contains_pred contains_p(get_rule_manager());
        check_pred check_pred(contains_p, get_manager());
        
        TRACE("dl", r->display_smt2(get_manager(), tout); tout << "\n";);
        for (unsigned i = ut_size; i < t_size; ++i) {
            app* t = r->get_tail(i);
            TRACE("dl", tout << "checking: " << mk_ismt2_pp(t, get_manager()) << "\n";);
            if (check_pred(t)) {
                std::ostringstream out;
                out << "interpreted body " << mk_ismt2_pp(t, get_manager()) << " contains recursive predicate";
                throw default_exception(out.str());
            }
        }
    }

    void context::check_positive_predicates(rule_ref& r) {
        ast_mark visited;
        ptr_vector<expr> todo, tocheck;
        unsigned ut_size = r->get_uninterpreted_tail_size();
        unsigned t_size  = r->get_tail_size();   
        for (unsigned i = 0; i < ut_size; ++i) {
            if (r->is_neg_tail(i)) {
                tocheck.push_back(r->get_tail(i));
            }
        }
        ast_manager& m = get_manager();
        datalog::rule_manager& rm = get_rule_manager();
        contains_pred contains_p(rm);
        check_pred check_pred(contains_p, get_manager());

        for (unsigned i = ut_size; i < t_size; ++i) {
            todo.push_back(r->get_tail(i));
        }
        while (!todo.empty()) {
            expr* e = todo.back(), *e1, *e2;
            todo.pop_back();
            if (visited.is_marked(e)) {
                continue;
            }
            visited.mark(e, true);
            if (rm.is_predicate(e)) {
            }
            else if (m.is_and(e) || m.is_or(e)) {
                todo.append(to_app(e)->get_num_args(), to_app(e)->get_args());
            }
            else if (m.is_implies(e, e1, e2)) {
                tocheck.push_back(e1);
                todo.push_back(e2);
            }
            else if (is_quantifier(e)) {
                todo.append(to_quantifier(e)->get_expr());
            }
            else if ((m.is_eq(e, e1, e2) || m.is_iff(e, e1, e2)) && 
                     m.is_true(e1)) {
                todo.push_back(e2);
            }
            else if ((m.is_eq(e, e1, e2) || m.is_iff(e, e1, e2)) &&
                     m.is_true(e2)) {
                todo.push_back(e1);
            }
            else {
                tocheck.push_back(e);
            }
        }
        for (unsigned i = 0; i < tocheck.size(); ++i) {
            expr* e = tocheck[i];
            if (check_pred(e)) {
                std::ostringstream out;
                out << "recursive predicate " << mk_ismt2_pp(e, get_manager()) << " occurs nested in body";
                throw default_exception(out.str());

            }
        }
    }

    void context::check_rule(rule_ref& r) {
        switch(get_engine()) {
        case DATALOG_ENGINE:
            check_quantifier_free(r);
            check_uninterpreted_free(r);
            check_existential_tail(r); 
            break;
        case PDR_ENGINE:
            check_existential_tail(r);
            check_positive_predicates(r);
            break;
        case QPDR_ENGINE:
            check_positive_predicates(r);
            break;
        case BMC_ENGINE:
            check_positive_predicates(r);
            break;            
        case QBMC_ENGINE:
            check_existential_tail(r);
            check_positive_predicates(r);
            break;         
        case TAB_ENGINE:
            check_existential_tail(r);
            check_positive_predicates(r);
            break;
        default:
            UNREACHABLE();
            break;
        }
    }

    void context::add_rule(rule_ref& r) {
        m_rule_set.add_rule(r);
    }

    void context::add_rules(rule_ref_vector& rules) {
        for (unsigned i = 0; i < rules.size(); ++i) {
            rule_ref rule(rules[i].get(), rules.get_manager());
            add_rule(rule);
        }
    }


    void context::add_fact(func_decl * pred, const relation_fact & fact) {
        if (get_engine() == DATALOG_ENGINE) {
            ensure_rel();
            m_rel->add_fact(pred, fact);
        }
        else {
            expr_ref rule(m.mk_app(pred, fact.size(), (expr*const*)fact.c_ptr()), m);
            add_rule(rule, symbol::null);
        }
    }


    void context::add_fact(app * head) {
        SASSERT(is_fact(head));

        relation_fact fact(get_manager());
        unsigned n=head->get_num_args();
        for (unsigned i=0; i<n; i++) {
            fact.push_back(to_app(head->get_arg(i)));
        }
        add_fact(head->get_decl(), fact);
    }

    void context::add_table_fact(func_decl * pred, const table_fact & fact) {
        if (get_engine() == DATALOG_ENGINE) {
            ensure_rel();
            m_rel->add_fact(pred, fact);
        }
        else {
            relation_fact rfact(m);
            for (unsigned i = 0; i < fact.size(); ++i) {
                rfact.push_back(m_decl_util.mk_numeral(fact[i], pred->get_domain()[i]));
            }
            add_fact(pred, rfact);
        }
    }
    
    void context::add_table_fact(func_decl * pred, unsigned num_args, unsigned args[]) {
        if (pred->get_arity() != num_args) {
            std::ostringstream out;
            out << "miss-matched number of arguments passed to " << mk_ismt2_pp(pred, m) << " " << num_args << " passed";
            throw default_exception(out.str());
        }
        table_fact fact;
        for (unsigned i = 0; i < num_args; ++i) {
            fact.push_back(args[i]);
        }
        add_table_fact(pred, fact);
    }

    void context::close() {
        SASSERT(!m_closed);
        if (!m_rule_set.close()) {
            throw default_exception("Negation is not stratified!");
        }
        m_closed = true;
    }

    void context::ensure_closed() {
        if (!m_closed) {
            close();
        }
    }
    void context::ensure_opened() {
        if (m_closed) {
            reopen();
        }
    }
    
    void context::reopen() {
        SASSERT(m_closed);
        m_rule_set.reopen();
        m_closed = false;
    }

    void context::transform_rules(model_converter_ref& mc, proof_converter_ref& pc) {
        rule_transformer transf(*this);
        transf.register_plugin(alloc(mk_filter_rules,*this));
        transf.register_plugin(alloc(mk_simple_joins,*this));

        if (unbound_compressor()) {
            transf.register_plugin(alloc(mk_unbound_compressor,*this));
        }

        if (similarity_compressor()) {
            transf.register_plugin(alloc(mk_similarity_compressor, *this, 
                                         similarity_compressor_threshold()));
        }
        transf.register_plugin(alloc(datalog::mk_partial_equivalence_transformer, *this));

        transform_rules(transf, mc, pc);
    }

    void context::transform_rules(rule_transformer& transf, model_converter_ref& mc, proof_converter_ref& pc) {
        SASSERT(m_closed); //we must finish adding rules before we start transforming them
        TRACE("dl", display_rules(tout););
        if (transf(m_rule_set, mc, pc)) {
            //we have already ensured the negation is stratified and transformations
            //should not break the stratification
            m_rule_set.ensure_closed();
            TRACE("dl", display_rules(tout););
            TRACE("dl_verbose", display(tout););
        }
    }

    void context::replace_rules(rule_set & rs) {
        SASSERT(!m_closed);
        m_rule_set.reset();
        m_rule_set.add_rules(rs);
    }

    void context::apply_default_transformation(model_converter_ref& mc, proof_converter_ref& pc) {
        ensure_closed();
        datalog::rule_transformer transf(*this);
        transf.register_plugin(alloc(datalog::mk_coi_filter, *this));
        transf.register_plugin(alloc(datalog::mk_interp_tail_simplifier, *this));

        transf.register_plugin(alloc(datalog::mk_subsumption_checker, *this, 35005));
        transf.register_plugin(alloc(datalog::mk_rule_inliner, *this, 35000));
        transf.register_plugin(alloc(datalog::mk_coi_filter, *this, 34990));
        transf.register_plugin(alloc(datalog::mk_interp_tail_simplifier, *this, 34980));

        //and another round of inlining
        transf.register_plugin(alloc(datalog::mk_subsumption_checker, *this, 34975));
        transf.register_plugin(alloc(datalog::mk_rule_inliner, *this, 34970));
        transf.register_plugin(alloc(datalog::mk_coi_filter, *this, 34960));
        transf.register_plugin(alloc(datalog::mk_interp_tail_simplifier, *this, 34950));

        transf.register_plugin(alloc(datalog::mk_subsumption_checker, *this, 34940));
        transf.register_plugin(alloc(datalog::mk_rule_inliner, *this, 34930));
        transf.register_plugin(alloc(datalog::mk_subsumption_checker, *this, 34920));
        transf.register_plugin(alloc(datalog::mk_rule_inliner, *this, 34910));
        transf.register_plugin(alloc(datalog::mk_subsumption_checker, *this, 34900));
        transf.register_plugin(alloc(datalog::mk_rule_inliner, *this, 34890));
        transf.register_plugin(alloc(datalog::mk_subsumption_checker, *this, 34880));

        transf.register_plugin(alloc(datalog::mk_bit_blast, *this, 35000));
        transf.register_plugin(alloc(datalog::mk_array_blast, *this, 36000));
        transform_rules(transf, mc, pc);
    }

    void context::collect_params(param_descrs& p) {
        fixedpoint_params::collect_param_descrs(p);
        insert_timeout(p);
    }

    void context::updt_params(params_ref const& p) {
        m_params_ref.copy(p);
        if (m_pdr.get()) m_pdr->updt_params();        
    }

    void context::collect_predicates(decl_set& res) {
        ensure_rel();
        m_rel->collect_predicates(res);
    }

    void context::restrict_predicates(decl_set const& res) {
        ensure_rel();
        m_rel->restrict_predicates(res);
    }

    expr_ref context::get_background_assertion() {
        expr_ref result(m);
        switch (m_background.size()) {
        case 0: result = m.mk_true(); break;
        case 1: result = m_background[0].get(); break;
        default: result = m.mk_and(m_background.size(), m_background.c_ptr()); break;
        }
        return result;
    }

    void context::assert_expr(expr* e) {
        TRACE("dl", tout << mk_ismt2_pp(e, m) << "\n";);
        m_background.push_back(e); 
    }


    void context::cancel() {
        m_cancel = true;
        if (m_pdr.get()) m_pdr->cancel();
        if (m_bmc.get()) m_bmc->cancel();
        if (m_rel.get()) m_rel->cancel();
        if (m_tab.get()) m_tab->cancel();
    }

    void context::cleanup() {
        m_cancel = false;
        if (m_pdr.get()) m_pdr->cleanup();
        if (m_bmc.get()) m_bmc->cleanup();
        if (m_rel.get()) m_rel->cleanup();
        if (m_tab.get()) m_tab->cleanup();
    }

    class context::engine_type_proc {
        ast_manager&  m;
        arith_util    a;
        datatype_util dt;
        DL_ENGINE     m_engine;

    public:
        engine_type_proc(ast_manager& m): m(m), a(m), dt(m), m_engine(DATALOG_ENGINE) {}

        DL_ENGINE get_engine() const { return m_engine; }
        void operator()(expr* e) {
            if (is_quantifier(e)) {
                m_engine = QPDR_ENGINE;
            }
            else if (a.is_int_real(e) && m_engine != QPDR_ENGINE) {
                m_engine = PDR_ENGINE;
            }
            else if (is_var(e) && m.is_bool(e)) {
                m_engine = PDR_ENGINE;
            }
            else if (dt.is_datatype(m.get_sort(e))) {
                m_engine = PDR_ENGINE;
            }
        }
    };

    void context::configure_engine() {
        symbol e = m_params.engine();
        
        if (e == symbol("datalog")) {
            m_engine = DATALOG_ENGINE;
        }
        else if (e == symbol("pdr")) {
            m_engine = PDR_ENGINE;
        }
        else if (e == symbol("qpdr")) {
            m_engine = QPDR_ENGINE;
        }
        else if (e == symbol("bmc")) {
            m_engine = BMC_ENGINE;
        }
        else if (e == symbol("qbmc")) {
            m_engine = QBMC_ENGINE;
        }
        else if (e == symbol("tab")) {
            m_engine = TAB_ENGINE;
        }

        if (m_engine == LAST_ENGINE) {
            expr_fast_mark1 mark;
            engine_type_proc proc(m);
            m_engine = DATALOG_ENGINE;
            for (unsigned i = 0; m_engine == DATALOG_ENGINE && i < m_rule_set.get_num_rules(); ++i) {
                rule * r = m_rule_set.get_rule(i);
                quick_for_each_expr(proc, mark, r->get_head());
                for (unsigned j = 0; j < r->get_tail_size(); ++j) {
                    quick_for_each_expr(proc, mark, r->get_tail(j));
                }
                m_engine = proc.get_engine();
            }
        }
    }

    lbool context::query(expr* query) {
        new_query();
        rule_set::iterator it = m_rule_set.begin(), end = m_rule_set.end();
        rule_ref r(m_rule_manager);
        for (; it != end; ++it) {
            r = *it;
            check_rule(r);
        }
        
        switch(get_engine()) {
        case DATALOG_ENGINE:
            return rel_query(query);
        case PDR_ENGINE:
        case QPDR_ENGINE:
            return pdr_query(query);
        case BMC_ENGINE:
        case QBMC_ENGINE:
            return bmc_query(query);
        case TAB_ENGINE:
            return tab_query(query);
        default:
            UNREACHABLE();
            return rel_query(query);
        }
    }

    void context::new_query() {
        flush_add_rules();
        m_last_status = OK;
        m_last_answer = 0;
    }

    model_ref context::get_model() {
        switch(get_engine()) {
        case PDR_ENGINE:
        case QPDR_ENGINE:
            ensure_pdr();
            return m_pdr->get_model();
        default:
            return model_ref(alloc(model, m));
        }        
    }

    proof_ref context::get_proof() {
        switch(get_engine()) {
        case PDR_ENGINE:
        case QPDR_ENGINE:
            ensure_pdr();
            return m_pdr->get_proof();
        default:
            return proof_ref(m.mk_asserted(m.mk_true()), m);
        }                
    }

    void context::ensure_pdr() {
        if (!m_pdr.get()) {
            m_pdr = alloc(pdr::dl_interface, *this);
        }
    }

    lbool context::pdr_query(expr* query) {
        ensure_pdr();
        return m_pdr->query(query);
    }

    void context::ensure_bmc() {
        if (!m_bmc.get()) {
            m_bmc = alloc(bmc, *this);
        }
    }

    lbool context::bmc_query(expr* query) {
        ensure_bmc();
        return m_bmc->query(query);
    }

    void context::ensure_tab() {
        if (!m_tab.get()) {
            m_tab = alloc(tab, *this);
        }
    }

    lbool context::tab_query(expr* query) {
        ensure_tab();
        return m_tab->query(query);
    }

    void context::ensure_rel() {
        if (!m_rel.get()) {
            m_rel = alloc(rel_context, *this);
        }
    }

    lbool context::rel_query(unsigned num_rels, func_decl * const* rels) {
        ensure_rel();
        return m_rel->query(num_rels, rels);
    }
    
    lbool context::rel_query(expr* query) {
        ensure_rel();
        return m_rel->query(query);
    }

    
    expr* context::get_answer_as_formula() {
        if (m_last_answer) {
            return m_last_answer.get();
        }
        switch(get_engine()) {
        case PDR_ENGINE: 
        case QPDR_ENGINE:
            ensure_pdr();
            m_last_answer = m_pdr->get_answer();
            return m_last_answer.get();
        case BMC_ENGINE:
        case QBMC_ENGINE:
            ensure_bmc();
            m_last_answer = m_bmc->get_answer();
            return m_last_answer.get();
        case DATALOG_ENGINE:
            ensure_rel();
            m_last_answer = m_rel->get_last_answer();
            return m_last_answer.get();
        case TAB_ENGINE:
            ensure_tab();
            m_last_answer = m_tab->get_answer();
            return m_last_answer.get();
        default:
            UNREACHABLE();
        }
        m_last_answer = m.mk_false();
        return m_last_answer.get();
    }

    bool context::display_certificate(std::ostream& out) {
        switch(get_engine()) {
        case DATALOG_ENGINE:            
            return false;
        case QPDR_ENGINE: 
            ensure_pdr();
            m_pdr->display_certificate(out);
            return true;
        case BMC_ENGINE:
        case QBMC_ENGINE:
            ensure_bmc();
            m_bmc->display_certificate(out);
            return true;
        case TAB_ENGINE:
            ensure_tab();
            m_tab->display_certificate(out);
            return true;
        default: 
            return false;
        }        
    }

    void context::reset_statistics() {
        if (m_pdr) {
            m_pdr->reset_statistics();
        }
        if (m_bmc) {
            m_bmc->reset_statistics();
        }
    }

    void context::collect_statistics(statistics& st) const {

        switch(m_engine) {
        case DATALOG_ENGINE: 
            break;
        case PDR_ENGINE: 
        case QPDR_ENGINE:
            if (m_pdr) {
                m_pdr->collect_statistics(st);
            }
            break;
        case BMC_ENGINE:
        case QBMC_ENGINE:
            if (m_bmc) {
                m_bmc->collect_statistics(st);
            }
            break;
        case TAB_ENGINE:
            if (m_tab) {
                m_tab->collect_statistics(st);
            }
            break;
        default: 
            break;
        }
    }


    execution_result context::get_status() { return m_last_status; }

    bool context::result_contains_fact(relation_fact const& f) {
        ensure_rel();
        return m_rel->result_contains_fact(f);
    }
    
    // TBD: algebraic data-types declarations will not be printed.
    class free_func_visitor {
        ast_manager& m;
        func_decl_set m_funcs;
        obj_hashtable<sort> m_sorts;
    public:        
        free_func_visitor(ast_manager& m): m(m) {}
        void operator()(var * n)        { }
        void operator()(app * n)        { 
            m_funcs.insert(n->get_decl()); 
            sort* s = m.get_sort(n);
            if (s->get_family_id() == null_family_id) {
                m_sorts.insert(s);
            }
        }
        void operator()(quantifier * n) { }
        func_decl_set& funcs() { return m_funcs; }
        obj_hashtable<sort>& sorts() { return m_sorts; }
    };

    static void collect_free_funcs(unsigned sz, expr* const* exprs, 
                                   expr_mark& visited, free_func_visitor& v,
                                   mk_fresh_name& fresh_names) {
        for (unsigned i = 0; i < sz; ++i) {
            expr* e = exprs[i];
            for_each_expr(v, visited, e);
            while (is_quantifier(e)) {
                e = to_quantifier(e)->get_expr();
            }
            fresh_names.add(e);
        }
    }
   
    void context::get_rules_as_formulas(expr_ref_vector& rules, svector<symbol>& names) {
        expr_ref fml(m);
        datalog::rule_manager& rm = get_rule_manager();
        datalog::rule_ref_vector rule_refs(rm);
        
        // ensure that rules are all using bound variables.
        for (unsigned i = 0; i < m_rule_fmls.size(); ++i) {
            ptr_vector<sort> sorts;
            get_free_vars(m_rule_fmls[i].get(), sorts);
            if (!sorts.empty()) {
                rm.mk_rule(m_rule_fmls[i].get(), rule_refs, m_rule_names[i]);
                m_rule_fmls[i] = m_rule_fmls.back();
                m_rule_names[i] = m_rule_names.back();
                m_rule_fmls.pop_back();
                m_rule_names.pop_back();
                --i;
            }
        }
        add_rules(rule_refs);
        rule_set::iterator it = m_rule_set.begin(), end = m_rule_set.end();
        for (; it != end; ++it) {
            (*it)->to_formula(fml);
            rules.push_back(fml);
            names.push_back((*it)->name());
        }
        for (unsigned i = 0; i < m_rule_fmls.size(); ++i) {
            rules.push_back(m_rule_fmls[i].get());
            names.push_back(m_rule_names[i]);
        }
    }
 
    void context::display_smt2(
        unsigned num_queries, 
        expr* const* queries, 
        std::ostream& out) {
        ast_manager& m = get_manager();
        free_func_visitor visitor(m);
        expr_mark visited;
        func_decl_set rels;
        unsigned num_axioms = m_background.size();
        expr* const* axioms = m_background.c_ptr();
        expr_ref fml(m);
        expr_ref_vector rules(m);
        svector<symbol> names;
        bool use_fixedpoint_extensions = m_params.print_with_fixedpoint_extensions();
        bool print_low_level = m_params.print_low_level_smt2();
        bool do_declare_vars = m_params.print_with_variable_declarations();

#define PP(_e_) if (print_low_level) out << mk_smt_pp(_e_, m); else ast_smt2_pp(out, _e_, env);

        get_rules_as_formulas(rules, names);

        smt2_pp_environment_dbg env(m);
        mk_fresh_name fresh_names;
        collect_free_funcs(num_axioms,  axioms,  visited, visitor, fresh_names);
        collect_free_funcs(rules.size(), rules.c_ptr(),   visited, visitor, fresh_names);
        collect_free_funcs(num_queries, queries, visited, visitor, fresh_names);
        func_decl_set funcs;
        func_decl_set::iterator it  = visitor.funcs().begin();
        func_decl_set::iterator end = visitor.funcs().end();
        for (; it != end; ++it) {
            func_decl* f = *it;
            if (f->get_family_id() != null_family_id) {
                // 
            }
            else if (is_predicate(f) && use_fixedpoint_extensions) {
                rels.insert(f);
            }
            else {
                funcs.insert(f);
            }
        }

        if (!use_fixedpoint_extensions) {
            out << "(set-logic HORN)\n";
        }
        
        it = funcs.begin(), end = funcs.end();
        
        obj_hashtable<sort>& sorts = visitor.sorts();
        obj_hashtable<sort>::iterator sit = sorts.begin(), send = sorts.end();
        for (; sit != send; ++sit) {
            PP(*sit);
        }
        for (; it != end; ++it) {
            func_decl* f = *it;
            PP(f);
            out << "\n";
        }
        it = rels.begin(); end = rels.end();
        for (; it != end; ++it) {
            func_decl* f = *it;
            out << "(declare-rel " << f->get_name() << " (";
            for (unsigned i = 0; i < f->get_arity(); ++i) {                
                ast_smt2_pp(out, f->get_domain(i), env);
                if (i + 1 < f->get_arity()) {
                    out << " ";
                }
            }
            out << "))\n";
        }

        if (use_fixedpoint_extensions && do_declare_vars) {
            declare_vars(rules, fresh_names, out);
        }

        if (num_axioms > 0 && !use_fixedpoint_extensions) {
            throw default_exception("Background axioms cannot be used with SMT-LIB2 HORN format");
        }

        for (unsigned i = 0; i < num_axioms; ++i) {
            out << "(assert ";
            PP(axioms[i]);
            out << ")\n";
        }
        for (unsigned i = 0; i < rules.size(); ++i) {            
            out << (use_fixedpoint_extensions?"(rule ":"(assert ");
            expr* r = rules[i].get();
            symbol nm = names[i];
            if (symbol::null != nm) {
                out << "(! ";
            }
            PP(r);
            if (symbol::null != nm) {
                out << " :named ";
                while (fresh_names.contains(nm)) {
                    std::ostringstream s;
                    s << nm << "!";
                    nm = symbol(s.str().c_str());                    
                }
                fresh_names.add(nm);
                if (is_smt2_quoted_symbol(nm)) {
                    out << mk_smt2_quoted_symbol(nm);
                }
                else {
                    out << nm;
                }
                out << ")";
            }
            out << ")\n";
        }
        if (use_fixedpoint_extensions) {
            for (unsigned i = 0; i < num_queries; ++i) {
                out << "(query ";
                PP(queries[i]);                
                out << ")\n";
            }
        }
        else {
            for (unsigned i = 0; i < num_queries; ++i) {
                if (num_queries > 1) out << "(push)\n";
                out << "(assert ";
                expr_ref q(m);
                q = m.mk_not(queries[i]);
                PP(q);
                out << ")\n";
                out << "(check-sat)\n";
                if (num_queries > 1) out << "(pop)\n";
            }
        }
    }


    void context::declare_vars(expr_ref_vector& rules, mk_fresh_name& fresh_names, std::ostream& out) {
        //
        // replace bound variables in rules by 'var declarations'
        // First remove quantifers, then replace bound variables 
        // by fresh constants.
        // 
        smt2_pp_environment_dbg env(m);
        var_subst vsubst(m, false);
        
        expr_ref_vector fresh_vars(m), subst(m);
        expr_ref res(m);
        obj_map<sort, unsigned_vector> var_idxs;
        obj_map<sort, unsigned> max_vars;
        for (unsigned i = 0; i < rules.size(); ++i) {
            expr* r = rules[i].get();
            if (!is_quantifier(r)) {
                continue;
            }
            quantifier* q = to_quantifier(r);
            if (!q->is_forall()) {
                continue;
            }            
            if (has_quantifiers(q->get_expr())) {
                continue;
            }
            max_vars.reset();
            subst.reset();
            unsigned max_var = 0;
            unsigned num_vars = q->get_num_decls();
            for (unsigned j = 0; j < num_vars; ++j) {
                sort* s = q->get_decl_sort(num_vars-1-j);
                // maximal var for the given sort.
                if (!max_vars.find(s, max_var)) {
                    max_var = 0;
                }
                else {
                    ++max_var;
                }
                max_vars.insert(s, max_var);

                // index into fresh variable array.
                // unsigned fresh_var_idx = 0;
                obj_map<sort, unsigned_vector>::obj_map_entry* e = var_idxs.insert_if_not_there2(s, unsigned_vector());
                unsigned_vector& vars = e->get_data().m_value;
                if (max_var >= vars.size()) {
                    SASSERT(vars.size() == max_var);
                    vars.push_back(fresh_vars.size());
                    symbol name = fresh_names.next();
                    fresh_vars.push_back(m.mk_const(name, s));
                    out << "(declare-var " << name << " ";
                    ast_smt2_pp(out, s, env);
                    out << ")\n"; 
                }
                subst.push_back(fresh_vars[vars[max_var]].get());
            }

            vsubst(q->get_expr(), subst.size(), subst.c_ptr(), res);
            rules[i] = res.get();
        }
    }


};

