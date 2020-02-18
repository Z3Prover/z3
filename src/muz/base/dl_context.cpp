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
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "muz/base/dl_context.h"
#include "ast/for_each_expr.h"
#include "ast/ast_smt_pp.h"
#include "ast/ast_smt2_pp.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/scoped_proof.h"
#include "muz/base/fp_params.hpp"
#include "ast/ast_pp_util.h"


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
        uint64_t m_size;

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

        unsigned get_constant_count() const override {
            return m_el_names.size();
        }
        void print_element(finite_element el_num, std::ostream & out) override {
            if (el_num>=m_el_names.size()) {
                out << el_num;
                return;
            }
            out << m_el_names[el_num];
        }
    };

    class context::uint64_sort_domain : public sort_domain {
        typedef map<uint64_t,     finite_element,   uint64_hash, default_eq<uint64_t> > el2num;
        typedef svector<uint64_t> num2el;

        el2num m_el_numbers;
        num2el m_el_names;
    public:
        uint64_sort_domain(context & ctx, sort * s) : sort_domain(SK_UINT64, ctx, s) {}

        finite_element get_number(uint64_t el) {
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
        unsigned get_constant_count() const override {
            return m_el_names.size();
        }
        void print_element(finite_element el_num, std::ostream & out) override {
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
            m_old_rules = nullptr;
        }
    public:
        restore_rules(rule_set& r): m_old_rules(alloc(rule_set, r)) {}

        ~restore_rules() override {}

        void undo(context& ctx) override {
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
        ~restore_vec_size_trail() override {}
        void undo(Ctx& ctx) override { m_vector.shrink(m_old_size); }
    };

    void context::push() {
        m_trail.push_scope();
        m_trail.push(restore_rules(m_rule_set));
        m_trail.push(restore_vec_size_trail<context,expr_ref_vector>(m_rule_fmls));
        m_trail.push(restore_vec_size_trail<context,expr_ref_vector>(m_background));
    }

    void context::pop() {
        if (m_trail.get_num_scopes() == 0) {
            throw default_exception("there are no backtracking points to pop to");
        }
        throw default_exception("pop operation is not supported");
        m_trail.pop_scope(1);
    }

    // -----------------------------------
    //
    // context
    //
    // -----------------------------------

    context::context(ast_manager & m, register_engine_base& re, smt_params& fp, params_ref const& pa):
        m(m),
        m_register_engine(re),
        m_fparams(fp),
        m_params_ref(pa),
        m_params(alloc(fp_params, m_params_ref)),
        m_decl_util(m),
        m_rewriter(m),
        m_var_subst(m),
        m_rule_manager(*this),
        m_contains_p(*this),
        m_rule_properties(m, m_rule_manager, *this, m_contains_p),
        m_transf(*this),
        m_trail(*this),
        m_pinned(m),
        m_bind_variables(m),
        m_rule_set(*this),
        m_transformed_rule_set(*this),
        m_rule_fmls_head(0),
        m_rule_fmls(m),
        m_background(m),
        m_mc(nullptr),
        m_rel(nullptr),
        m_engine(nullptr),
        m_closed(false),
        m_saturation_was_run(false),
        m_enable_bind_variables(true),
        m_last_status(OK),
        m_last_answer(m),
        m_last_ground_answer(m),
        m_engine_type(LAST_ENGINE) {
        re.set_context(this);
        updt_params(pa);
    }

    context::~context() {
        reset();
        dealloc(m_params);
    }

    void context::reset() {
        m_trail.reset();
        m_rule_set.reset();
        m_rule_fmls_head = 0;
        m_rule_fmls.reset();
        m_rule_names.reset();
        m_rule_bounds.reset();
        m_argument_var_names.reset();
        m_preds.reset();
        m_preds_by_name.reset();
        reset_dealloc_values(m_sorts);
        m_engine = nullptr;
        m_rel = nullptr;
    }

    bool context::is_fact(app * head) const {
        return m_rule_manager.is_fact(head);
    }

    bool context::has_sort_domain(relation_sort s) const {
        return m_sorts.contains(s);
    }

    context::sort_domain & context::get_sort_domain(relation_sort s) {
        return *m_sorts.find(s);
    }

    const context::sort_domain & context::get_sort_domain(relation_sort s) const {
        return *m_sorts.find(s);
    }


    bool context::generate_proof_trace() const { return m_generate_proof_trace; }
    bool context::output_profile() const { return m_params->datalog_output_profile(); }
    bool context::output_tuples() const { return m_params->datalog_print_tuples(); }
    bool context::use_map_names() const { return m_params->datalog_use_map_names(); }
    bool context::fix_unbound_vars() const { return m_params->xform_fix_unbound_vars(); }
    symbol context::default_table() const { return m_params->datalog_default_table(); }
    symbol context::default_relation() const { return m_default_relation; }
    void context::set_default_relation(symbol const& s) { m_default_relation = s; }
    symbol context::print_aig() const { return m_params->print_aig(); }
    symbol context::check_relation() const { return m_params->datalog_check_relation(); }
    symbol context::default_table_checker() const { return m_params->datalog_default_table_checker(); }
    bool context::default_table_checked() const { return m_params->datalog_default_table_checked(); }
    bool context::dbg_fpr_nonempty_relation_signature() const { return m_params->datalog_dbg_fpr_nonempty_relation_signature(); }
    unsigned context::dl_profile_milliseconds_threshold() const { return m_params->datalog_profile_timeout_milliseconds(); }
    bool context::all_or_nothing_deltas() const { return m_params->datalog_all_or_nothing_deltas(); }
    bool context::compile_with_widening() const { return m_params->datalog_compile_with_widening(); }
    bool context::unbound_compressor() const { return m_unbound_compressor; }
    void context::set_unbound_compressor(bool f) { m_unbound_compressor = f; }
    unsigned context::soft_timeout() const { return m_params->datalog_timeout(); }
    bool context::similarity_compressor() const { return m_params->datalog_similarity_compressor(); }
    unsigned context::similarity_compressor_threshold() const { return m_params->datalog_similarity_compressor_threshold(); }
    unsigned context::initial_restart_timeout() const { return m_params->datalog_initial_restart_timeout(); }
    bool context::generate_explanations() const { return m_params->datalog_generate_explanations(); }
    bool context::explanations_on_relation_level() const { return m_params->datalog_explanations_on_relation_level(); }
    bool context::magic_sets_for_queries() const { return m_params->datalog_magic_sets_for_queries();  }
    symbol context::tab_selection() const { return m_params->tab_selection(); }
    bool context::xform_coi() const { return m_params->xform_coi(); }
    bool context::xform_slice() const { return m_params->xform_slice(); }
    bool context::xform_bit_blast() const { return m_params->xform_bit_blast(); }
    bool context::karr() const { return m_params->xform_karr(); }
    bool context::scale() const { return m_params->xform_scale(); }
    bool context::magic() const { return m_params->xform_magic(); }
    bool context::compress_unbound() const { return m_params->xform_compress_unbound(); }
    bool context::quantify_arrays() const { return m_params->xform_quantify_arrays(); }
    bool context::instantiate_quantifiers() const { return m_params->xform_instantiate_quantifiers(); }
    bool context::array_blast() const { return m_params->xform_array_blast(); }
    bool context::array_blast_full() const { return m_params->xform_array_blast_full(); }
    bool context::elim_term_ite() const {return m_params->xform_elim_term_ite();}
    unsigned context::blast_term_ite_inflation() const {
        return m_params->xform_elim_term_ite_inflation();
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

    void context::register_variable(func_decl* var) {
        m_bind_variables.add_var(m.mk_const(var));
    }

    expr_ref context::bind_vars(expr* fml, bool is_forall) {
        if (m_enable_bind_variables) {
            return m_bind_variables(fml, is_forall);
        }
        else {
            return expr_ref(fml, m);
        }
    }

    void context::register_predicate(func_decl * decl, bool named) {
        if (!is_predicate(decl)) {
            m_pinned.push_back(decl);
            m_preds.insert(decl);
            TRACE("dl", tout << mk_pp(decl, m) << "\n";);
            if (named) {
                m_preds_by_name.insert(decl->get_name(), decl);
            }
        }
    }

    void context::restrict_predicates(func_decl_set const& preds) {
        m_preds.reset();
        func_decl_set::iterator it = preds.begin(), end = preds.end();
        for (; it != end; ++it) {
            TRACE("dl", tout << mk_pp(*it, m) << "\n";);
            m_preds.insert(*it);
        }
    }

    context::finite_element context::get_constant_number(relation_sort srt, symbol sym) {
        sort_domain & dom0 = get_sort_domain(srt);
        SASSERT(dom0.get_kind() == SK_SYMBOL);
        symbol_sort_domain & dom = static_cast<symbol_sort_domain &>(dom0);
        return dom.get_number(sym);
    }

    context::finite_element context::get_constant_number(relation_sort srt, uint64_t el) {
        sort_domain & dom0 = get_sort_domain(srt);
        SASSERT(dom0.get_kind()==SK_UINT64);
        uint64_sort_domain & dom = static_cast<uint64_sort_domain &>(dom0);
        return dom.get_number(el);
    }

    void context::print_constant_name(relation_sort srt, uint64_t num, std::ostream & out)
    {
        if (has_sort_domain(srt)) {
            SASSERT(num<=UINT_MAX);
            get_sort_domain(srt).print_element(static_cast<unsigned>(num), out);
        }
        else {
            out << num;
        }
    }

    bool context::try_get_sort_constant_count(relation_sort srt, uint64_t & constant_count) {
        if (!has_sort_domain(srt)) {
            return false;
        }
        constant_count = get_sort_domain(srt).get_constant_count();
        return true;
    }

    uint64_t context::get_sort_size_estimate(relation_sort srt) {
        if (get_decl_util().is_rule_sort(srt)) {
            return 1;
        }
        uint64_t res;
        if (!try_get_sort_constant_count(srt, res)) {
            const sort_size & sz = srt->get_num_elements();
            if (sz.is_finite()) {
                res = sz.size();
            }
            else {
                res = std::numeric_limits<uint64_t>::max();
            }
        }
        return res;
    }

    void context::set_argument_names(const func_decl * pred, const svector<symbol> & var_names)
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
            ensure_engine();
        }
        if (relation_name_cnt > 0 && m_rel) {
            m_rel->set_predicate_representation(pred, relation_name_cnt, relation_names);
        }
    }

    func_decl * context::mk_fresh_head_predicate(symbol const & prefix, symbol const & suffix,
            unsigned arity, sort * const * domain, func_decl* orig_pred) {
        func_decl* new_pred =
            m.mk_fresh_func_decl(prefix, suffix, arity, domain, m.mk_bool_sort());

        register_predicate(new_pred, true);

        if (m_rel) {
            m_rel->inherit_predicate_kind(new_pred, orig_pred);
        }
        return new_pred;
    }

    void context::add_rule(expr* rl, symbol const& name, unsigned bound) {
        SASSERT(rl);
        m_rule_fmls.push_back(rl);
        m_rule_names.push_back(name);
        m_rule_bounds.push_back(bound);
    }

    void context::flush_add_rules() {
        datalog::rule_manager& rm = get_rule_manager();
        scoped_proof_mode _scp(m, generate_proof_trace()?PGM_ENABLED:PGM_DISABLED);
        while (m_rule_fmls_head < m_rule_fmls.size()) {
            expr* fml = m_rule_fmls[m_rule_fmls_head].get();
            proof* p = generate_proof_trace()?m.mk_asserted(fml):nullptr;
            rm.mk_rule(fml, p, m_rule_set, m_rule_names[m_rule_fmls_head]);
            ++m_rule_fmls_head;
        }
        check_rules(m_rule_set);
    }

    //
    // Update a rule with a new.
    // It requires basic subsumption.
    //
    void context::update_rule(expr* rl, symbol const& name) {
        datalog::rule_manager& rm = get_rule_manager();
        proof* p = nullptr;
        if (generate_proof_trace()) {
            p = m.mk_asserted(rl);
        }
        unsigned size_before = m_rule_set.get_num_rules();
        rm.mk_rule(rl, p, m_rule_set, name);
        unsigned size_after = m_rule_set.get_num_rules();
        if (size_before + 1 != size_after) {
            std::stringstream strm;
            strm << "Rule " << name << " has a non-trivial body. It cannot be modified";
            throw default_exception(strm.str());
        }
        // The new rule is inserted last:
        rule_ref r(m_rule_set.get_rule(size_before), rm);
        rule_ref_vector const& rls = m_rule_set.get_rules();
        rule* old_rule = nullptr;
        for (unsigned i = 0; i < size_before; ++i) {
            if (rls[i]->name() == name) {
                if (old_rule) {
                    std::stringstream strm;
                    strm << "Rule " << name << " occurs twice. It cannot be modified";
                    m_rule_set.del_rule(r);
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
                m_rule_set.del_rule(r);
                throw default_exception(strm.str());
            }
            m_rule_set.del_rule(old_rule);
        }
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
        ensure_engine();
        return m_engine->get_num_levels(pred);
    }

    expr_ref context::get_cover_delta(int level, func_decl* pred) {
        ensure_engine();
        return m_engine->get_cover_delta(level, pred);
    }

    expr_ref context::get_reachable(func_decl *pred) {
        ensure_engine();
        return m_engine->get_reachable(pred);
    }
    void context::add_cover(int level, func_decl* pred, expr* property) {
        ensure_engine();
        m_engine->add_cover(level, pred, property);
    }

    void context::add_invariant(func_decl* pred, expr *property)
    {
        ensure_engine();
        m_engine->add_invariant(pred, property);
    }

    void context::check_rules(rule_set& r) {
        m_rule_properties.set_generate_proof(generate_proof_trace());
        switch(get_engine()) {
        case DATALOG_ENGINE:
            m_rule_properties.collect(r);
            m_rule_properties.check_quantifier_free();
            m_rule_properties.check_uninterpreted_free();
            m_rule_properties.check_nested_free();
            m_rule_properties.check_infinite_sorts();
            break;
        case SPACER_ENGINE:
            m_rule_properties.collect(r);
            m_rule_properties.check_existential_tail();
            m_rule_properties.check_for_negated_predicates();
            m_rule_properties.check_uninterpreted_free();
            break;
        case BMC_ENGINE:
            m_rule_properties.collect(r);
            m_rule_properties.check_for_negated_predicates();
            break;
        case QBMC_ENGINE:
            m_rule_properties.collect(r);
            m_rule_properties.check_existential_tail();
            m_rule_properties.check_for_negated_predicates();
            break;
        case TAB_ENGINE:
            m_rule_properties.collect(r);
            m_rule_properties.check_existential_tail();
            m_rule_properties.check_for_negated_predicates();
            break;
        case CLP_ENGINE:
            m_rule_properties.collect(r);
            m_rule_properties.check_existential_tail();
            m_rule_properties.check_for_negated_predicates();
            break;
        case DDNF_ENGINE:
            break;
        case LAST_ENGINE:
        default:
            UNREACHABLE();
            break;
        }
    }

    void context::add_rule(rule_ref& r) {
        m_rule_set.add_rule(r);
    }

    void context::add_fact(func_decl * pred, const relation_fact & fact) {
        if (get_engine() == DATALOG_ENGINE) {
            ensure_engine();
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
        unsigned n = head->get_num_args();
        for (unsigned i = 0; i < n; i++) {
            fact.push_back(to_app(head->get_arg(i)));
        }
        add_fact(head->get_decl(), fact);
    }

    bool context::has_facts(func_decl * pred) const {
        return m_rel && m_rel->has_facts(pred);
    }

    void context::add_table_fact(func_decl * pred, const table_fact & fact) {
        if (get_engine() == DATALOG_ENGINE) {
            ensure_engine();
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
            out << "mismatched number of arguments passed to " << mk_ismt2_pp(pred, m) << " " << num_args << " passed";
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

    void context::transform_rules(rule_transformer::plugin* plugin) {
        flet<bool> _enable_bv(m_enable_bind_variables, false);
        rule_transformer transformer(*this);
        transformer.register_plugin(plugin);
        transform_rules(transformer);
    }

    void context::transform_rules(rule_transformer& transf) {
        SASSERT(m_closed); //we must finish adding rules before we start transforming them
        TRACE("dl", display_rules(tout););
        if (transf(m_rule_set)) {
            //we have already ensured the negation is stratified and transformations
            //should not break the stratification
            m_rule_set.ensure_closed();
            TRACE("dl", display_rules(tout););
            TRACE("dl_verbose", display(tout););
        }
    }

    void context::replace_rules(rule_set const & rs) {
        SASSERT(!m_closed);
        m_rule_set.replace_rules(rs);
        if (m_rel) {
            m_rel->restrict_predicates(get_predicates());
        }
    }

    void context::record_transformed_rules() {
        m_transformed_rule_set.replace_rules(m_rule_set);
    }

    void context::apply_default_transformation() {
    }

    void context::collect_params(param_descrs& p) {
        fp_params::collect_param_descrs(p);
        insert_timeout(p);
        insert_ctrl_c(p);
    }

    void context::updt_params(params_ref const& p) {
        m_params_ref.copy(p);
        if (m_engine.get()) m_engine->updt_params();
        m_generate_proof_trace = m_params->generate_proof_trace();
        m_unbound_compressor = m_params->datalog_unbound_compressor();
        m_default_relation = m_params->datalog_default_relation();
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

    void context::cleanup() {
        m_last_status = OK;
        if (m_engine) m_engine->cleanup();
    }

    class context::engine_type_proc {
        ast_manager&  m;
        arith_util    a;        
        datatype_util dt;
        bv_util       bv;
        DL_ENGINE     m_engine_type;

        bool is_large_bv(sort* s) {
            return false;
        }

    public:
        engine_type_proc(ast_manager& m): m(m), a(m), dt(m), bv(m), m_engine_type(DATALOG_ENGINE) {}

        DL_ENGINE get_engine() const { return m_engine_type; }

        void operator()(expr* e) {
            if (a.is_int_real(e)) {
                m_engine_type = SPACER_ENGINE;
            }
            else if (is_var(e) && m.is_bool(e)) {
                m_engine_type = SPACER_ENGINE;
            }
            else if (dt.is_datatype(m.get_sort(e))) {
                m_engine_type = SPACER_ENGINE;
            }
            else if (is_large_bv(m.get_sort(e))) {
                m_engine_type = SPACER_ENGINE;
            }
            else if (!m.get_sort(e)->get_num_elements().is_finite()) {
                m_engine_type = SPACER_ENGINE;
            }
        }
    };

    void context::configure_engine(expr* q) {
        TRACE("dl", tout << mk_pp(q, m) << " " << m_engine_type << "\n";);
        if (m_engine_type != LAST_ENGINE) {
            return;
        }
        symbol e = m_params->engine();

        if (e == symbol("datalog")) {
            m_engine_type = DATALOG_ENGINE;
        }
        else if (e == symbol("spacer")) {
            m_engine_type = SPACER_ENGINE;
        }
        else if (e == symbol("bmc")) {
            m_engine_type = BMC_ENGINE;
        }
        else if (e == symbol("qbmc")) {
            m_engine_type = QBMC_ENGINE;
        }
        else if (e == symbol("tab")) {
            m_engine_type = TAB_ENGINE;
        }
        else if (e == symbol("clp")) {
            m_engine_type = CLP_ENGINE;
        }
        else if (e == symbol("ddnf")) {
            m_engine_type = DDNF_ENGINE;
        }

        if (m_engine_type == LAST_ENGINE) {
            expr_fast_mark1 mark;
            engine_type_proc proc(m);
            m_engine_type = DATALOG_ENGINE;
            if (q) {
                quick_for_each_expr(proc, mark, q);
                m_engine_type = proc.get_engine();
            }

            for (unsigned i = 0; m_engine_type == DATALOG_ENGINE && i < m_rule_set.get_num_rules(); ++i) {
                rule * r = m_rule_set.get_rule(i);
                quick_for_each_expr(proc, mark, r->get_head());
                for (unsigned j = 0; j < r->get_tail_size(); ++j) {
                    quick_for_each_expr(proc, mark, r->get_tail(j));
                }
                m_engine_type = proc.get_engine();
            }
            for (unsigned i = m_rule_fmls_head; m_engine_type == DATALOG_ENGINE && i < m_rule_fmls.size(); ++i) {
                expr* fml = m_rule_fmls[i].get();
                while (is_quantifier(fml)) {
                    fml = to_quantifier(fml)->get_expr();
                }
                quick_for_each_expr(proc, mark, fml);
                m_engine_type = proc.get_engine();
            }
        }
    }

    lbool context::query(expr* query) {
        expr_ref _query(query, m);
        m_mc = mk_skip_model_converter();
        m_last_status = OK;
        m_last_answer = nullptr;
        m_last_ground_answer = nullptr;
        switch (get_engine(query)) {
        case DATALOG_ENGINE:
        case SPACER_ENGINE:
        case BMC_ENGINE:
        case QBMC_ENGINE:
        case TAB_ENGINE:
        case CLP_ENGINE:
        case DDNF_ENGINE:
            flush_add_rules();
            break;
        default:
            UNREACHABLE();
        }
        ensure_engine(query);
        lbool r = m_engine->query(query);
        if (r != l_undef && get_params().print_certificate()) {
            display_certificate(std::cout) << "\n";
        }
        return r;
    }

    lbool context::query_from_lvl (expr* query, unsigned lvl) {
        m_mc = mk_skip_model_converter();
        m_last_status = OK;
        m_last_answer = nullptr;
        m_last_ground_answer = nullptr;
        switch (get_engine()) {
        case DATALOG_ENGINE:
        case SPACER_ENGINE:
        case BMC_ENGINE:
        case QBMC_ENGINE:
        case TAB_ENGINE:
        case CLP_ENGINE:
            flush_add_rules();
            break;
        default:
            UNREACHABLE();
        }
        ensure_engine();
        return m_engine->query_from_lvl (query, lvl);
    }
    model_ref context::get_model() {
        ensure_engine();
        return m_engine->get_model();
    }

    proof_ref context::get_proof() {
        ensure_engine();
        return m_engine->get_proof();
    }

    void context::ensure_engine(expr* e) {
        if (!m_engine.get()) {
            m_engine = m_register_engine.mk_engine(get_engine(e));
            m_engine->updt_params();

            // break abstraction.
            if (get_engine() == DATALOG_ENGINE) {
                m_rel = dynamic_cast<rel_context_base*>(m_engine.get());
            }

        }
    }

    lbool context::rel_query(unsigned num_rels, func_decl * const* rels) {
        m_last_answer = nullptr;
        ensure_engine();
        return m_engine->query(num_rels, rels);
    }

    expr* context::get_answer_as_formula() {
        if (m_last_answer) {
            return m_last_answer.get();
        }
        ensure_engine();
        m_last_answer = m_engine->get_answer();
        return m_last_answer.get();
    }

    expr* context::get_ground_sat_answer () {
        if (m_last_ground_answer) {
            return m_last_ground_answer;
        }
        ensure_engine ();
        m_last_ground_answer = m_engine->get_ground_sat_answer ();
        return m_last_ground_answer;
    }

    void context::get_rules_along_trace (rule_ref_vector& rules) {
        ensure_engine ();
        m_engine->get_rules_along_trace (rules);
    }

    void context::get_rules_along_trace_as_formulas (expr_ref_vector& rules, svector<symbol>& names) {
        rule_manager& rm = get_rule_manager ();
        rule_ref_vector rv (rm);
        get_rules_along_trace (rv);
        expr_ref fml (m);
        rule_ref_vector::iterator it = rv.begin (), end = rv.end ();
        for (; it != end; it++) {
            m_rule_manager.to_formula (**it, fml);
            rules.push_back (fml);
            // The concatenated names are already stored last-first, so do not need to be reversed here
            const symbol& rule_name = (*it)->name();
            names.push_back (rule_name);

            TRACE ("dl",
                   if (rule_name == symbol::null) {
                       tout << "Encountered unnamed rule: ";
                       (*it)->display(*this, tout);
                       tout << "\n";
                   });
        }
    }

    std::ostream& context::display_certificate(std::ostream& out) {
        ensure_engine();
        m_engine->display_certificate(out);
        return out;
    }

    void context::display(std::ostream & out) const {
        display_rules(out);
        if (m_rel) m_rel->display_facts(out);
    }

    void context::display_profile(std::ostream& out) const {
        out << "\n---------------\n";
        out << "Original rules\n";
        display_rules(out);
        out << "\n---------------\n";
        out << "Transformed rules\n";
        m_transformed_rule_set.display(out);

        if (m_rel) {
            m_rel->display_profile(out);
        }
    }

    void context::reset_statistics() {
        if (m_engine) {
            m_engine->reset_statistics();
        }
    }

    void context::collect_statistics(statistics& st) const {
        if (m_engine) {
            m_engine->collect_statistics(st);
        }
        get_memory_statistics(st);
        get_rlimit_statistics(m.limit(), st);
    }


    execution_result context::get_status() { return m_last_status; }

    bool context::result_contains_fact(relation_fact const& f) {
        return m_rel && m_rel->result_contains_fact(f);
    }

    // NB: algebraic data-types declarations will not be printed.

    static void collect_free_funcs(unsigned sz, expr* const* exprs,
                                   ast_pp_util& v,
                                   mk_fresh_name& fresh_names) {
        v.collect(sz, exprs);
        for (unsigned i = 0; i < sz; ++i) {
            expr* e = exprs[i];
            while (is_quantifier(e)) {
                e = to_quantifier(e)->get_expr();
            }
            fresh_names.add(e);
        }
    }

    void context::get_raw_rule_formulas(expr_ref_vector& rules, svector<symbol>& names, unsigned_vector &bounds) {
        for (unsigned i = 0; i < m_rule_fmls.size(); ++i) {
            expr_ref r = bind_vars(m_rule_fmls[i].get(), true);
            rules.push_back(r.get());
            names.push_back(m_rule_names[i]);
            bounds.push_back(m_rule_bounds[i]);
        }
    }

    void context::get_rules_as_formulas(expr_ref_vector& rules, expr_ref_vector& queries, svector<symbol>& names) {
        expr_ref fml(m);
        rule_manager& rm = get_rule_manager();

        // ensure that rules are all using bound variables.
        for (unsigned i = m_rule_fmls_head; i < m_rule_fmls.size(); ++i) {
            m_free_vars(m_rule_fmls[i].get());
            if (!m_free_vars.empty()) {
                rm.mk_rule(m_rule_fmls[i].get(), nullptr, m_rule_set, m_rule_names[i]);
                m_rule_fmls[i] = m_rule_fmls.back();
                m_rule_names[i] = m_rule_names.back();
                m_rule_fmls.pop_back();
                m_rule_names.pop_back();
                m_rule_bounds.pop_back();
                --i;
            }
        }
        rule_set::iterator it = m_rule_set.begin(), end = m_rule_set.end();
        for (; it != end; ++it) {
            rule* r = *it;
            rm.to_formula(*r, fml);
            func_decl* h = r->get_decl();
            if (m_rule_set.is_output_predicate(h)) {
                expr* body = fml;
                expr* e2;
                if (is_quantifier(body)) {
                    quantifier* q = to_quantifier(body);
                    expr* e = q->get_expr();
                    if (m.is_implies(e, body, e2)) {
                        fml = m.mk_quantifier(exists_k, q->get_num_decls(),
                                              q->get_decl_sorts(), q->get_decl_names(),
                                              body);
                    }
                    else {
                        fml = body;
                    }
                }
                else {
                    fml = body;
                    if (m.is_implies(body, body, e2)) {
                        fml = body;
                    }
                }
                queries.push_back(fml);
            }
            else {
                rules.push_back(fml);
                names.push_back(r->name());
            }
        }
        for (unsigned i = m_rule_fmls_head; i < m_rule_fmls.size(); ++i) {
            rules.push_back(m_rule_fmls[i].get());
            names.push_back(m_rule_names[i]);
        }
    }

    static std::ostream& display_symbol(std::ostream& out, symbol const& nm) {
        if (is_smt2_quoted_symbol(nm)) {
            out << mk_smt2_quoted_symbol(nm);
        }
        else {
            out << nm;
        }
        return out;
    }

    void context::display_smt2(unsigned num_queries, expr* const* qs, std::ostream& out) {
        ast_manager& m = get_manager();
        ast_pp_util visitor(m);
        func_decl_set rels;
        unsigned num_axioms = m_background.size();
        expr* const* axioms = m_background.c_ptr();
        expr_ref fml(m);
        expr_ref_vector rules(m), queries(m);
        svector<symbol> names;
        bool use_fixedpoint_extensions = m_params->print_fixedpoint_extensions();
        bool print_low_level = m_params->print_low_level_smt2();
        bool do_declare_vars = m_params->print_with_variable_declarations();

#define PP(_e_) if (print_low_level) out << mk_smt_pp(_e_, m); else ast_smt2_pp(out, _e_, env);

        get_rules_as_formulas(rules, queries, names);
        queries.append(num_queries, qs);

        smt2_pp_environment_dbg env(m);
        mk_fresh_name fresh_names;
        collect_free_funcs(num_axioms,  axioms,  visitor, fresh_names);
        collect_free_funcs(rules.size(), rules.c_ptr(),   visitor, fresh_names);
        collect_free_funcs(queries.size(), queries.c_ptr(), visitor, fresh_names);
        func_decl_set funcs;
        unsigned sz = visitor.coll.get_num_decls();
        for (unsigned i = 0; i < sz; ++i) {
            func_decl* f = visitor.coll.get_func_decls()[i];
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
        for (func_decl * f : rels)
            visitor.remove_decl(f);

        visitor.display_decls(out);

        for (func_decl * f : rels)
            display_rel_decl(out, f);

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
                display_symbol(out, nm) << ")";
            }
            out << ")\n";
        }
        if (use_fixedpoint_extensions) {
            for (unsigned i = 0; i < queries.size(); ++i) {
                expr* q = queries[i].get();
                func_decl_ref fn(m);
                if (is_query(q)) {
                    fn = to_app(q)->get_decl();
                }
                else {
                    m_free_vars(q);
                    m_free_vars.set_default_sort(m.mk_bool_sort());
                    sort* const* domain = m_free_vars.c_ptr();
                    expr_ref qfn(m);
                    expr_ref_vector args(m);
                    fn = m.mk_fresh_func_decl(symbol("q"), symbol(""), m_free_vars.size(), domain, m.mk_bool_sort());
                    display_rel_decl(out, fn);
                    for (unsigned j = 0; j < m_free_vars.size(); ++j) {
                        args.push_back(m.mk_var(j, m_free_vars[j]));
                    }
                    qfn = m.mk_implies(q, m.mk_app(fn, args.size(), args.c_ptr()));

                    out << "(assert ";
                    PP(qfn);
                    out << ")\n";
                }
                out << "(query ";
                display_symbol(out, fn->get_name()) << ")\n";
            }
        }
        else {
            for (unsigned i = 0; i < queries.size(); ++i) {
                if (queries.size() > 1) out << "(push)\n";
                out << "(assert ";
                expr_ref q(m);
                q = m.mk_not(queries[i].get());
                PP(q);
                out << ")\n";
                out << "(check-sat)\n";
                if (queries.size() > 1) out << "(pop)\n";
            }
        }
    }

    void context::display_rel_decl(std::ostream& out, func_decl* f) {
        smt2_pp_environment_dbg env(m);
        out << "(declare-rel ";
        display_symbol(out, f->get_name()) << " (";
        for (unsigned i = 0; i < f->get_arity(); ++i) {
            ast_smt2_pp(out, f->get_domain(i), env);
            if (i + 1 < f->get_arity()) {
                out << " ";
            }
        }
        out << "))\n";
    }

    bool context::is_query(expr* q) {
        if (!is_app(q) || !is_predicate(to_app(q)->get_decl())) {
            return false;
        }
        app* a = to_app(q);
        for (unsigned i = 0; i < a->get_num_args(); ++i) {
            if (!is_var(a->get_arg(i))) {
                return false;
            }
            var* v = to_var(a->get_arg(i));
            if (v->get_idx() != i) {
                return false;
            }
        }
        return true;
    }


    void context::declare_vars(expr_ref_vector& rules, mk_fresh_name& fresh_names, std::ostream& out) {
        //
        // replace bound variables in rules by 'var declarations'
        // First remove quantifiers, then replace bound variables
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
            if (!is_forall(r)) {
                continue;
            }
            quantifier* q = to_quantifier(r);
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

            res = vsubst(q->get_expr(), subst.size(), subst.c_ptr());
            rules[i] = res.get();
        }
    }


};
