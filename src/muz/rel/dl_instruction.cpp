/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_instruction.cpp

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-09-14.

Revision History:

--*/

#include"ast_pp.h"
#include"stopwatch.h"
#include"dl_context.h"
#include"dl_util.h"
#include"dl_instruction.h"
#include"rel_context.h"
#include"debug.h"
#include"warning.h"

namespace datalog {

    // -----------------------------------
    //
    // execution_context
    //
    // -----------------------------------
    
    execution_context::execution_context(context & context) 
        : m_context(context),
        m_stopwatch(0),
        m_timelimit_ms(0) {}

    execution_context::~execution_context() {
        reset();
        dealloc(m_stopwatch);
    }

    void execution_context::reset() {
        reg_vector::iterator it=m_registers.begin();
        reg_vector::iterator end=m_registers.end();
        for(; it != end; ++it) {
            relation_base * rel = *it;
            if (rel) {
                rel->deallocate();
            }
        }
        m_registers.reset();
        m_reg_annotation.reset();
        reset_timelimit();
    }

    rel_context& execution_context::get_rel_context() { 
        return dynamic_cast<rel_context&>(*m_context.get_rel_context()); 
    }

    rel_context const& execution_context::get_rel_context() const { 
        return dynamic_cast<rel_context const&>(*m_context.get_rel_context()); 
    }

    struct compare_size_proc {
        typedef std::pair<unsigned, unsigned> pr;
        bool operator()(pr const& a, pr const& b) const {
            return a.second > b.second;
        }
    };

    void execution_context::report_big_relations(unsigned threshold, std::ostream & out) const {
        unsigned n = register_count();
        svector<std::pair<unsigned, unsigned> > sizes;
        size_t total_bytes = 0;
        for(unsigned i = 0; i < n; i++) {
            unsigned sz = reg(i) ? reg(i)->get_size_estimate_bytes() : 0;
            total_bytes += sz;
            sizes.push_back(std::make_pair(i, sz));
        }
        std::sort(sizes.begin(), sizes.end(), compare_size_proc());        

        out << "bytes " << total_bytes << "\n";
        out << "bytes\trows\tannotation\n";
        for(unsigned i = 0; i < n; i++) {
            unsigned sz = sizes[i].second;
            unsigned rg = sizes[i].first;
            unsigned rows = reg(rg) ? reg(rg)->get_size_estimate_rows() : 0;
            if (sz < threshold) {
                continue;
            }
            std::string annotation;
            get_register_annotation(i, annotation);
            out << sz << "\t" << rows << "\t" << annotation << "\n";
        }
    }

    void execution_context::set_timelimit(unsigned time_in_ms) {
        SASSERT(time_in_ms > 0);
        m_timelimit_ms = time_in_ms;
        if (!m_stopwatch) {
            m_stopwatch = alloc(stopwatch);
        }
        m_stopwatch->stop();
        m_stopwatch->reset();
        m_stopwatch->start();
    }
    void execution_context::reset_timelimit() {
        if (m_stopwatch) {
            m_stopwatch->stop();
        }
        m_timelimit_ms = 0;
    }

    bool execution_context::should_terminate() {
        return 
            m_context.canceled() ||
            memory::above_high_watermark() ||
            (m_stopwatch && 
             m_timelimit_ms != 0 &&
             m_timelimit_ms < static_cast<unsigned>(1000*m_stopwatch->get_current_seconds()));
    }

    void execution_context::collect_statistics(statistics& st) const {
        st.update("dl.joins",   m_stats.m_join);
        st.update("dl.project", m_stats.m_project);
        st.update("dl.filter",  m_stats.m_filter);
        st.update("dl.total", m_stats.m_total);
        st.update("dl.unary_singleton", m_stats.m_unary_singleton);
        st.update("dl.filter_by_negation", m_stats.m_filter_by_negation);
        st.update("dl.select_equal_project", m_stats.m_select_equal_project);
        st.update("dl.join_project", m_stats.m_join_project);
        st.update("dl.project_rename", m_stats.m_project_rename);
        st.update("dl.union", m_stats.m_union);
        st.update("dl.filter_interpreted_project", m_stats.m_filter_interp_project);
        st.update("dl.filter_id", m_stats.m_filter_id);
        st.update("dl.filter_eq", m_stats.m_filter_eq);
    }


    // -----------------------------------
    //
    // instruction
    //
    // -----------------------------------

    instruction::~instruction() {
        fn_cache::iterator it = m_fn_cache.begin();
        fn_cache::iterator end = m_fn_cache.end();
        for(; it != end; ++it) {
            dealloc(it->m_value);
        }
    }

    void instruction::process_all_costs() {
        process_costs();
    }

    void instruction::collect_statistics(statistics& st) const {
        costs c;
        get_total_cost(c);
        st.update("instruction", c.instructions);
        st.update("instruction-time", c.milliseconds);
    }


    void instruction::display_indented(execution_context const & _ctx, std::ostream & out, std::string indentation) const {
        out << indentation;
        rel_context const& ctx = _ctx.get_rel_context();
        display_head_impl(_ctx, out);
        if (ctx.output_profile()) {
            out << " {";
            output_profile(out);
            out << '}';
        }
        out << "\n";
        display_body_impl(_ctx, out, indentation);
    }

    void instruction::log_verbose(execution_context& ctx) {
        IF_VERBOSE(2, display(ctx, verbose_stream()););
    }

    class instr_io : public instruction {
        bool m_store;
        func_decl_ref m_pred;
        reg_idx m_reg;
    public:
        instr_io(bool store, func_decl_ref pred, reg_idx reg)
            : m_store(store), m_pred(pred), m_reg(reg) {}
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            if (m_store) {
                if (ctx.reg(m_reg)) {
                    ctx.get_rel_context().store_relation(m_pred, ctx.release_reg(m_reg));
                }
                else {
                    rel_context & dctx = ctx.get_rel_context();
                    relation_base * empty_rel;
                    //the object referenced by sig is valid only until we call dctx.store_relation()
                    const relation_signature & sig = dctx.get_relation(m_pred).get_signature();
                    empty_rel = dctx.get_rmanager().mk_empty_relation(sig, m_pred.get());
                    dctx.store_relation(m_pred, empty_rel);
                }
            }
            else {
                relation_base& rel = ctx.get_rel_context().get_relation(m_pred);
                if (!rel.fast_empty()) {
                    ctx.set_reg(m_reg, rel.clone());
                }
                else {
                    ctx.make_empty(m_reg);
                }
            }
            return true;
        }
        virtual void make_annotations(execution_context & ctx) {
            ctx.set_register_annotation(m_reg, m_pred->get_name().bare_str());
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            const char * rel_name = m_pred->get_name().bare_str();
            if (m_store) {
                out << "store " << m_reg << " into " << rel_name;
            }
            else {
                out << "load " << rel_name << " into " << m_reg;
            }
        }
    };

    instruction * instruction::mk_load(ast_manager & m, func_decl * pred, reg_idx tgt) {
        return alloc(instr_io, false, func_decl_ref(pred, m), tgt);
    }

    instruction * instruction::mk_store(ast_manager & m, func_decl * pred, reg_idx src) {
        return alloc(instr_io, true, func_decl_ref(pred, m), src);
    }


    class instr_dealloc : public instruction {
        reg_idx m_reg;
    public:
        instr_dealloc(reg_idx reg) : m_reg(reg) {}
        virtual bool perform(execution_context & ctx) {
            ctx.make_empty(m_reg);
            return true;
        }
        virtual void make_annotations(execution_context & ctx) {
            ctx.set_register_annotation(m_reg, "alloc");
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "dealloc " << m_reg;
        }
    };

    instruction * instruction::mk_dealloc(reg_idx reg) {
        return alloc(instr_dealloc, reg);
    }

    class instr_clone_move : public instruction {
        bool m_clone;
        reg_idx m_src;
        reg_idx m_tgt;
    public:
        instr_clone_move(bool clone, reg_idx src, reg_idx tgt)
            : m_clone(clone), m_src(src), m_tgt(tgt) {}
        virtual bool perform(execution_context & ctx) {
            if (ctx.reg(m_src)) log_verbose(ctx);            
            if (m_clone) {
                ctx.set_reg(m_tgt, ctx.reg(m_src) ? ctx.reg(m_src)->clone() : 0);
            }
            else {
                ctx.set_reg(m_tgt, ctx.reg(m_src) ? ctx.release_reg(m_src) : 0);
            }
            return true;
        }
        virtual void make_annotations(execution_context & ctx) {
            std::string str;
            if (ctx.get_register_annotation(m_src, str)) {
                ctx.set_register_annotation(m_tgt, str);
            }
            else if (ctx.get_register_annotation(m_tgt, str)) {
                ctx.set_register_annotation(m_src, str);
            }
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << (m_clone ? "clone " : "move ") << m_src << " into " << m_tgt;
        }
    };

    instruction * instruction::mk_clone(reg_idx from, reg_idx to) {
        return alloc(instr_clone_move, true, from, to);
    }
    instruction * instruction::mk_move(reg_idx from, reg_idx to) {
        return alloc(instr_clone_move, false, from, to);
    }


    class instr_while_loop : public instruction {
        typedef const vector<reg_idx> idx_vector;
        idx_vector m_controls;
        instruction_block * m_body;

        bool control_is_empty(execution_context & ctx) {
            idx_vector::const_iterator it=m_controls.begin();
            idx_vector::const_iterator end=m_controls.end();
            for(; it != end; ++it) {
                reg_idx r = *it;
                if (ctx.reg(r) && !ctx.reg(r)->fast_empty()) {
                    return false;
                }
            }
            return true;
        }
    protected:
        virtual void process_all_costs() {
            instruction::process_all_costs();
            m_body->process_all_costs();
        }
    public:
        instr_while_loop(unsigned control_reg_cnt, const reg_idx * control_regs, instruction_block * body)
            : m_controls(control_reg_cnt, control_regs), m_body(body) {}
        virtual ~instr_while_loop() {
            dealloc(m_body);
        }
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            TRACE("dl", tout << "loop entered\n";);
            unsigned count = 0;
            while (!control_is_empty(ctx)) {
                IF_VERBOSE(10, verbose_stream() << "looping ... " << count++ << "\n";);
                if (!m_body->perform(ctx)) {
                    TRACE("dl", tout << "while loop terminated before completion\n";);
                    return false;
                }
            }
            TRACE("dl", tout << "while loop exited\n";);
            return true;
        }
        virtual void make_annotations(execution_context & ctx) {
            m_body->make_annotations(ctx);
        }
        virtual void display_head_impl(execution_context const & ctx, std::ostream & out) const {
            out << "while";
            print_container(m_controls, out);
        }
        virtual void display_body_impl(execution_context const & ctx, std::ostream & out, std::string indentation) const {
            m_body->display_indented(ctx, out, indentation+"    ");
        }
    };

    instruction * instruction::mk_while_loop(unsigned control_reg_cnt, const reg_idx * control_regs, 
            instruction_block * body) {
        return alloc(instr_while_loop, control_reg_cnt, control_regs, body);
    }


    class instr_join : public instruction {
        typedef unsigned_vector column_vector;
        reg_idx m_rel1;
        reg_idx m_rel2;
        column_vector m_cols1;
        column_vector m_cols2;
        reg_idx m_res;
    public:
        instr_join(reg_idx rel1, reg_idx rel2, unsigned col_cnt, const unsigned * cols1, 
            const unsigned * cols2, reg_idx result)
            : m_rel1(rel1), m_rel2(rel2), m_cols1(col_cnt, cols1), 
            m_cols2(col_cnt, cols2), m_res(result) {}
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            ++ctx.m_stats.m_join;
            if (!ctx.reg(m_rel1) || !ctx.reg(m_rel2)) {
                ctx.make_empty(m_res);
                return true;
            }
            relation_join_fn * fn;
            const relation_base & r1 = *ctx.reg(m_rel1);
            const relation_base & r2 = *ctx.reg(m_rel2);
            if (!find_fn(r1, r2, fn)) {
                fn = r1.get_manager().mk_join_fn(r1, r2, m_cols1, m_cols2);
                if (!fn) {
                    throw default_exception("trying to perform unsupported join operation on relations of kinds %s and %s",
                        r1.get_plugin().get_name().bare_str(), r2.get_plugin().get_name().bare_str());
                }
                store_fn(r1, r2, fn);
            }

            TRACE("dl",
                r1.get_signature().output(ctx.get_rel_context().get_manager(), tout);
                tout<<":"<<r1.get_size_estimate_rows()<<" x ";
                r2.get_signature().output(ctx.get_rel_context().get_manager(), tout);
                tout<<":"<<r2.get_size_estimate_rows()<<" ->\n";);

            ctx.set_reg(m_res, (*fn)(r1, r2));

            TRACE("dl", 
                ctx.reg(m_res)->get_signature().output(ctx.get_rel_context().get_manager(), tout);
                tout<<":"<<ctx.reg(m_res)->get_size_estimate_rows()<<"\n";);

            if (ctx.reg(m_res)->fast_empty()) {
                ctx.make_empty(m_res);
            }
            return true;
        }
        virtual void make_annotations(execution_context & ctx) {
            std::string a1 = "rel1", a2 = "rel2";
            ctx.get_register_annotation(m_rel1, a1);
            ctx.get_register_annotation(m_rel1, a1);
            ctx.set_register_annotation(m_res, "join " + a1 + " " + a2);
        }
        virtual void display_head_impl(execution_context const & ctx, std::ostream & out) const {
            out << "join " << m_rel1;
            print_container(m_cols1, out);
            out << " and " << m_rel2;
            print_container(m_cols2, out);
            out << " into " << m_res;
        }
    };

    instruction * instruction::mk_join(reg_idx rel1, reg_idx rel2, unsigned col_cnt,
            const unsigned * cols1, const unsigned * cols2, reg_idx result) {
        return alloc(instr_join, rel1, rel2, col_cnt, cols1, cols2, result);
    }

    class instr_filter_equal : public instruction {
        reg_idx m_reg;
        app_ref m_value;
        unsigned m_col;
    public:
        instr_filter_equal(ast_manager & m, reg_idx reg, const relation_element & value, unsigned col)
            : m_reg(reg), m_value(value, m), m_col(col) {}
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            ++ctx.m_stats.m_filter_eq;
            if (!ctx.reg(m_reg)) {
                return true;
            }

            relation_mutator_fn * fn;
            relation_base & r = *ctx.reg(m_reg);
            if (!find_fn(r, fn)) {
                fn = r.get_manager().mk_filter_equal_fn(r, m_value, m_col);
                if (!fn) {
                    throw default_exception(
                        "trying to perform unsupported filter_equal operation on a relation of kind %s",
                        r.get_plugin().get_name().bare_str());
                }
                store_fn(r, fn);
            }
            (*fn)(r);

            if (r.fast_empty()) {
                ctx.make_empty(m_reg);
            }
            return true;
        }
        virtual void make_annotations(execution_context & ctx) {
            std::stringstream a;
            a << "filter_equal " << m_col << " val: " << ctx.get_rel_context().get_rmanager().to_nice_string(m_value);
            ctx.set_register_annotation(m_reg, a.str());
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "filter_equal " << m_reg << " col: " << m_col << " val: "
                << ctx.get_rel_context().get_rmanager().to_nice_string(m_value);
        }
    };

    instruction * instruction::mk_filter_equal(ast_manager & m, reg_idx reg, const relation_element & value, 
            unsigned col) {
        return alloc(instr_filter_equal, m, reg, value, col);
    }


    class instr_filter_identical : public instruction {
        typedef unsigned_vector column_vector;
        reg_idx m_reg;
        column_vector m_cols;
    public:
        instr_filter_identical(reg_idx reg, unsigned col_cnt, const unsigned * identical_cols)
            : m_reg(reg), m_cols(col_cnt, identical_cols) {}
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            ++ctx.m_stats.m_filter_id;
            if (!ctx.reg(m_reg)) {
                return true;
            }

            relation_mutator_fn * fn;
            relation_base & r = *ctx.reg(m_reg);
            if (!find_fn(r, fn)) {
                fn = r.get_manager().mk_filter_identical_fn(r, m_cols.size(), m_cols.c_ptr());
                if (!fn) {
                    throw default_exception(
                        "trying to perform unsupported filter_identical operation on a relation of kind %s",
                        r.get_plugin().get_name().bare_str());
                }
                store_fn(r, fn);
            }
            (*fn)(r);

            if (r.fast_empty()) {
                ctx.make_empty(m_reg);
            }
            return true;
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "filter_identical " << m_reg << " ";
            print_container(m_cols, out);
        }
        virtual void make_annotations(execution_context & ctx) {
            ctx.set_register_annotation(m_reg, "filter_identical");
        }
    };

    instruction * instruction::mk_filter_identical(reg_idx reg, unsigned col_cnt, const unsigned * identical_cols) {
        return alloc(instr_filter_identical, reg, col_cnt, identical_cols);
    }


    class instr_filter_interpreted : public instruction {
        reg_idx m_reg;
        app_ref m_cond;
    public:
        instr_filter_interpreted(reg_idx reg, app_ref & condition)
            : m_reg(reg), m_cond(condition) {}
        virtual bool perform(execution_context & ctx) {
            if (!ctx.reg(m_reg)) {
                return true;
            }
            log_verbose(ctx);            
            ++ctx.m_stats.m_filter;

            relation_mutator_fn * fn;
            relation_base & r = *ctx.reg(m_reg);
            TRACE("dl_verbose", r.display(tout <<"pre-filter-interpreted:\n"););
            if (!find_fn(r, fn)) {
                fn = r.get_manager().mk_filter_interpreted_fn(r, m_cond);
                if (!fn) {
                    throw default_exception(
                        "trying to perform unsupported filter_interpreted operation on a relation of kind %s",
                        r.get_plugin().get_name().bare_str());
                }
                store_fn(r, fn);
            }
            (*fn)(r);

            if (r.fast_empty()) {
                ctx.make_empty(m_reg);
            }            
            TRACE("dl_verbose", r.display(tout <<"post-filter-interpreted:\n"););

            return true;
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "filter_interpreted " << m_reg << " using "
                << mk_pp(m_cond, m_cond.get_manager());
        }
        virtual void make_annotations(execution_context & ctx) {
            std::stringstream a;
            a << "filter_interpreted " << mk_pp(m_cond, m_cond.get_manager());
            ctx.set_register_annotation(m_reg, a.str());
        }

    };

    instruction * instruction::mk_filter_interpreted(reg_idx reg, app_ref & condition) {
        return alloc(instr_filter_interpreted, reg, condition);
    }

    class instr_filter_interpreted_and_project : public instruction {
        reg_idx m_src;
        app_ref m_cond;
        unsigned_vector m_cols;
        reg_idx m_res;
    public:
        instr_filter_interpreted_and_project(reg_idx src, app_ref & condition,
            unsigned col_cnt, const unsigned * removed_cols, reg_idx result)
            : m_src(src), m_cond(condition), m_cols(col_cnt, removed_cols),
              m_res(result) {}

        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            if (!ctx.reg(m_src)) {
                ctx.make_empty(m_res);
                return true;
            }
            ++ctx.m_stats.m_filter_interp_project;

            relation_transformer_fn * fn;
            relation_base & reg = *ctx.reg(m_src);
            TRACE("dl_verbose", reg.display(tout <<"pre-filter-interpreted-and-project:\n"););
            if (!find_fn(reg, fn)) {
                fn = reg.get_manager().mk_filter_interpreted_and_project_fn(reg, m_cond, m_cols.size(), m_cols.c_ptr());
                if (!fn) {
                    throw default_exception(
                        "trying to perform unsupported filter_interpreted_and_project operation on a relation of kind %s",
                        reg.get_plugin().get_name().bare_str());
                }
                store_fn(reg, fn);
            }

            ctx.set_reg(m_res, (*fn)(reg));

            if (ctx.reg(m_res)->fast_empty()) {
                ctx.make_empty(m_res);
            }
            TRACE("dl_verbose", reg.display(tout << "post-filter-interpreted-and-project:\n"););
            return true;
        }

        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "filter_interpreted_and_project " << m_src << " into " << m_res;
            out << " using " << mk_pp(m_cond, m_cond.get_manager());
            out << " deleting columns ";
            print_container(m_cols, out);
        }

        virtual void make_annotations(execution_context & ctx) {
            std::stringstream s;
            std::string a = "rel_src";
            ctx.get_register_annotation(m_src, a);
            s << "filter_interpreted_and_project " << mk_pp(m_cond, m_cond.get_manager());
            ctx.set_register_annotation(m_res, s.str());
        }
    };

    instruction * instruction::mk_filter_interpreted_and_project(reg_idx reg, app_ref & condition,
        unsigned col_cnt, const unsigned * removed_cols, reg_idx result) {
        return alloc(instr_filter_interpreted_and_project, reg, condition, col_cnt, removed_cols, result);
    }


    class instr_union : public instruction {
        reg_idx m_src;
        reg_idx m_tgt;
        reg_idx m_delta;
        bool m_widen; //if true, widening is performed intead of an union
    public:
        instr_union(reg_idx src, reg_idx tgt, reg_idx delta, bool widen)
            : m_src(src), m_tgt(tgt), m_delta(delta), m_widen(widen) {}
        virtual bool perform(execution_context & ctx) {
            TRACE("dl", tout << "union " << m_src << " into " << m_tgt 
                  << " " << ctx.reg(m_src) << " " << ctx.reg(m_tgt) << "\n";);
            if (!ctx.reg(m_src)) {
                return true;
            }
            log_verbose(ctx);            
            ++ctx.m_stats.m_union;
            relation_base & r_src = *ctx.reg(m_src);
            if (!ctx.reg(m_tgt)) {
                relation_base * new_tgt = r_src.get_plugin().mk_empty(r_src);
                ctx.set_reg(m_tgt, new_tgt);
            }
            relation_base & r_tgt = *ctx.reg(m_tgt);
            if (m_delta!=execution_context::void_register && !ctx.reg(m_delta)) {
                relation_base * new_delta = r_tgt.get_plugin().mk_empty(r_tgt);
                ctx.set_reg(m_delta, new_delta);
            }
            relation_base * r_delta = (m_delta!=execution_context::void_register) ? ctx.reg(m_delta) : 0;

            relation_union_fn * fn;

            if (r_delta) {
                if (!find_fn(r_tgt, r_src, *r_delta, fn)) {
                    if (m_widen) {
                        fn = r_src.get_manager().mk_widen_fn(r_tgt, r_src, r_delta);
                    }
                    else {
                        fn = r_src.get_manager().mk_union_fn(r_tgt, r_src, r_delta);
                    }
                    if (!fn) {
                        std::stringstream sstm;
                        sstm << "trying to perform unsupported union operation on relations of kinds ";
                        sstm << r_tgt.get_plugin().get_name() << ", " << r_src.get_plugin().get_name() << " and ";
                        sstm << r_delta->get_plugin().get_name();
                        throw default_exception(sstm.str());
                    }
                    store_fn(r_tgt, r_src, *r_delta, fn);
                }
            }
            else {
                if (!find_fn(r_tgt, r_src, fn)) {
                    if (m_widen) {
                        fn = r_src.get_manager().mk_widen_fn(r_tgt, r_src, 0);
                    }
                    else {
                        fn = r_src.get_manager().mk_union_fn(r_tgt, r_src, 0);
                    }
                    if (!fn) {
                        std::stringstream sstm;
                        sstm << "trying to perform unsupported union operation on relations of kinds "
                             << r_tgt.get_plugin().get_name() << " and "
                             << r_src.get_plugin().get_name();
                        throw default_exception(sstm.str());
                    }
                    store_fn(r_tgt, r_src, fn);
                }
            }

            SASSERT(r_src.get_signature().size() == r_tgt.get_signature().size());
            TRACE("dl_verbose", r_tgt.display(tout <<"pre-union:"););

            (*fn)(r_tgt, r_src, r_delta);

            TRACE("dl_verbose", 
                r_src.display(tout <<"src:");
                r_tgt.display(tout <<"post-union:");
                if (r_delta) {
                    r_delta->display(tout <<"delta:");
                });

            if (r_delta && r_delta->fast_empty()) {
                ctx.make_empty(m_delta);
            }

            return true;
        }
        virtual void make_annotations(execution_context & ctx) {
            std::string str = "union";
            if (!ctx.get_register_annotation(m_tgt, str)) {
                ctx.set_register_annotation(m_tgt, "union");
            }
            if (m_delta != execution_context::void_register) {
                str = "delta of " + str;
            }
            ctx.set_register_annotation(m_delta, str);            
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << (m_widen ? "widen " : "union ") << m_src << " into " << m_tgt;
            if (m_delta!=execution_context::void_register) {
                out << " with delta " << m_delta;
            }
        }
    };

    instruction * instruction::mk_union(reg_idx src, reg_idx tgt, reg_idx delta) {
        return alloc(instr_union, src, tgt, delta, false);
    }

    instruction * instruction::mk_widen(reg_idx src, reg_idx tgt, reg_idx delta) {
        return alloc(instr_union, src, tgt, delta, true);
    }


    class instr_project_rename : public instruction {
        typedef unsigned_vector column_vector;
        bool m_projection;
        reg_idx m_src;
        column_vector m_cols;
        reg_idx m_tgt;
    public:
        instr_project_rename(bool projection, reg_idx src, unsigned col_cnt, const unsigned * cols, 
            reg_idx tgt) : m_projection(projection), m_src(src), 
            m_cols(col_cnt, cols), m_tgt(tgt) {}
        virtual bool perform(execution_context & ctx) {
            if (!ctx.reg(m_src)) {
                ctx.make_empty(m_tgt);
                return true;
            }

            log_verbose(ctx);            
            ++ctx.m_stats.m_project_rename;
            relation_transformer_fn * fn;
            relation_base & r_src = *ctx.reg(m_src);
            if (!find_fn(r_src, fn)) {
                if (m_projection) {
                    fn = r_src.get_manager().mk_project_fn(r_src, m_cols.size(), m_cols.c_ptr());
                }
                else {
                    fn = r_src.get_manager().mk_rename_fn(r_src, m_cols.size(), m_cols.c_ptr());
                }
                if (!fn) {
                    std::stringstream sstm;
                    sstm << "trying to perform unsupported " << (m_projection ? "project" : "rename");
                    sstm << " operation on a relation of kind " << r_src.get_plugin().get_name();
                    throw default_exception(sstm.str());
                }
                store_fn(r_src, fn);
            }
            ctx.set_reg(m_tgt, (*fn)(r_src));

            return true;
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << (m_projection ? "project " : "rename ") << m_src << " into " << m_tgt;
            out << (m_projection ? " deleting columns " : " with cycle ");
            print_container(m_cols, out);
        }
        virtual void make_annotations(execution_context & ctx) {
            std::stringstream s;
            std::string a = "rel_src";
            ctx.get_register_annotation(m_src, a);
            s << (m_projection ? "project " : "rename ") << a;
            ctx.set_register_annotation(m_tgt, s.str());
        }
    };

    instruction * instruction::mk_projection(reg_idx src, unsigned col_cnt, const unsigned * removed_cols, 
            reg_idx tgt) {
        return alloc(instr_project_rename, true, src, col_cnt, removed_cols, tgt);
    }
    instruction * instruction::mk_rename(reg_idx src, unsigned cycle_len, const unsigned * permutation_cycle, 
            reg_idx tgt) {
        return alloc(instr_project_rename, false, src, cycle_len, permutation_cycle, tgt);
    }


    class instr_join_project : public instruction {
        typedef unsigned_vector column_vector;
        reg_idx m_rel1;
        reg_idx m_rel2;
        column_vector m_cols1;
        column_vector m_cols2;
        column_vector m_removed_cols;
        reg_idx m_res;
    public:
        instr_join_project(reg_idx rel1, reg_idx rel2, unsigned joined_col_cnt, const unsigned * cols1, 
            const unsigned * cols2, unsigned removed_col_cnt, const unsigned * removed_cols, reg_idx result)
            : m_rel1(rel1), m_rel2(rel2), m_cols1(joined_col_cnt, cols1), 
            m_cols2(joined_col_cnt, cols2), m_removed_cols(removed_col_cnt, removed_cols), m_res(result) {
        }
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            if (!ctx.reg(m_rel1) || !ctx.reg(m_rel2)) {
                ctx.make_empty(m_res);
                return true;
            }
            ++ctx.m_stats.m_join_project;
            relation_join_fn * fn;
            const relation_base & r1 = *ctx.reg(m_rel1);
            const relation_base & r2 = *ctx.reg(m_rel2);
            if (!find_fn(r1, r2, fn)) {
                fn = r1.get_manager().mk_join_project_fn(r1, r2, m_cols1, m_cols2, m_removed_cols);
                if (!fn) {
                    throw default_exception("trying to perform unsupported join-project operation on relations of kinds %s and %s",
                        r1.get_plugin().get_name().bare_str(), r2.get_plugin().get_name().bare_str());
                }
                store_fn(r1, r2, fn);
            }
            TRACE("dl", tout<<r1.get_size_estimate_rows()<<" x "<<r2.get_size_estimate_rows()<<" jp->\n";);
            ctx.set_reg(m_res, (*fn)(r1, r2));
            TRACE("dl",  tout<<ctx.reg(m_res)->get_size_estimate_rows()<<"\n";);
            if (ctx.reg(m_res)->fast_empty()) {
                ctx.make_empty(m_res);
            }
            return true;
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            relation_base const* r1 = ctx.reg(m_rel1);
            relation_base const* r2 = ctx.reg(m_rel2);
            out << "join_project " << m_rel1;            
            if (r1) {
                out << ":" << r1->num_columns();
                out << "-" << r1->get_size_estimate_rows();
            }
            print_container(m_cols1, out);
            out << " and " << m_rel2;
            if (r2) {
                out << ":" << r2->num_columns();
                out << "-" << r2->get_size_estimate_rows();
            }
            print_container(m_cols2, out);
            out << " into " << m_res << " removing columns ";
            print_container(m_removed_cols, out);
        }
        virtual void make_annotations(execution_context & ctx) {
            std::string s1 = "rel1", s2 = "rel2";
            ctx.get_register_annotation(m_rel1, s1);
            ctx.get_register_annotation(m_rel2, s2);
            ctx.set_register_annotation(m_res, "join project " + s1 + " " + s2);            
        }
    };

    instruction * instruction::mk_join_project(reg_idx rel1, reg_idx rel2, unsigned joined_col_cnt,
        const unsigned * cols1, const unsigned * cols2, unsigned removed_col_cnt, 
        const unsigned * removed_cols, reg_idx result) {
            return alloc(instr_join_project, rel1, rel2, joined_col_cnt, cols1, cols2, removed_col_cnt,
                removed_cols, result);
    }


    class instr_select_equal_and_project : public instruction {
        reg_idx m_src;
        reg_idx m_result;
        app_ref m_value;
        unsigned m_col;
    public:
        instr_select_equal_and_project(ast_manager & m, reg_idx src, const relation_element & value, 
            unsigned col, reg_idx result)
            : m_src(src), m_result(result), m_value(value, m), m_col(col) {
            // [Leo]: does not compile on gcc
            // TRACE("dl", tout << "src:"  << m_src << " result: " << m_result << " value:" << m_value << " column:" << m_col << "\n";);
        }

        virtual bool perform(execution_context & ctx) {
            if (!ctx.reg(m_src)) {
                ctx.make_empty(m_result);
                return true;
            }
            log_verbose(ctx);            
            ++ctx.m_stats.m_select_equal_project;
            relation_transformer_fn * fn;
            relation_base & r = *ctx.reg(m_src);
            if (!find_fn(r, fn)) {
                fn = r.get_manager().mk_select_equal_and_project_fn(r, m_value, m_col);
                if (!fn) {
                    throw default_exception(
                        "trying to perform unsupported select_equal_and_project operation on a relation of kind %s",
                        r.get_plugin().get_name().bare_str());
                }
                store_fn(r, fn);
            }
            ctx.set_reg(m_result, (*fn)(r));

            if (ctx.reg(m_result)->fast_empty()) {
                ctx.make_empty(m_result);
            }
            return true;
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "select_equal_and_project " << m_src <<" into " << m_result << " col: " << m_col 
                << " val: " << ctx.get_rel_context().get_rmanager().to_nice_string(m_value);
        }
        virtual void make_annotations(execution_context & ctx) {
            std::stringstream s;
            std::string s1 = "src";
            ctx.get_register_annotation(m_src, s1);
            s << "select equal project col " << m_col << " val: " 
              << ctx.get_rel_context().get_rmanager().to_nice_string(m_value) << " " << s1;
            ctx.set_register_annotation(m_result, s.str());            
        }
    };

    instruction * instruction::mk_select_equal_and_project(ast_manager & m, reg_idx src, 
            const relation_element & value, unsigned col, reg_idx result) {
        return alloc(instr_select_equal_and_project, m, src, value, col, result);
    }


    class instr_filter_by_negation : public instruction {
        typedef unsigned_vector column_vector;
        reg_idx m_tgt;
        reg_idx m_neg_rel;
        column_vector m_cols1;
        column_vector m_cols2;
    public:
        instr_filter_by_negation(reg_idx tgt, reg_idx neg_rel, unsigned col_cnt, const unsigned * cols1, 
            const unsigned * cols2)
            : m_tgt(tgt), m_neg_rel(neg_rel), m_cols1(col_cnt, cols1), m_cols2(col_cnt, cols2) {}
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            if (!ctx.reg(m_tgt) || !ctx.reg(m_neg_rel)) {
                return true;
            }
            ++ctx.m_stats.m_filter_by_negation;

            relation_intersection_filter_fn * fn;
            relation_base & r1 = *ctx.reg(m_tgt);
            const relation_base & r2 = *ctx.reg(m_neg_rel);
            if (!find_fn(r1, r2, fn)) {
                fn = r1.get_manager().mk_filter_by_negation_fn(r1, r2, m_cols1.size(), m_cols1.c_ptr(), m_cols2.c_ptr());
                if (!fn) {
                    std::stringstream sstm;
                    sstm << "trying to perform unsupported filter_by_negation on relations of kinds ";
                    sstm << r1.get_plugin().get_name() << " and " << r2.get_plugin().get_name();
                    throw default_exception(sstm.str());
                }
                store_fn(r1, r2, fn);
            }
            (*fn)(r1, r2);

            if (r1.fast_empty()) {
                ctx.make_empty(m_tgt);
            }
            return true;
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "filter_by_negation on " << m_tgt;
            print_container(m_cols1, out);
            out << " with " << m_neg_rel;
            print_container(m_cols2, out);
            out << " as the negated table";
        }
        virtual void make_annotations(execution_context & ctx) {
            std::string s = "negated relation";
            ctx.get_register_annotation(m_neg_rel, s);
            ctx.set_register_annotation(m_tgt, "filter by negation " + s);            
        }
    };

    instruction * instruction::mk_filter_by_negation(reg_idx tgt, reg_idx neg_rel, unsigned col_cnt,
            const unsigned * cols1, const unsigned * cols2) {
        return alloc(instr_filter_by_negation, tgt, neg_rel, col_cnt, cols1, cols2);
    }

        
    class instr_mk_unary_singleton : public instruction {
        relation_signature m_sig;
        func_decl* m_pred;
        reg_idx m_tgt;
        relation_fact m_fact;
    public:
        instr_mk_unary_singleton(ast_manager & m, func_decl* head_pred, const relation_sort & s, const relation_element & val, 
            reg_idx tgt) : m_pred(head_pred), m_tgt(tgt), m_fact(m) {
            m_sig.push_back(s);
            m_fact.push_back(val);
        }
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            ++ctx.m_stats.m_unary_singleton;
            relation_base * rel = ctx.get_rel_context().get_rmanager().mk_empty_relation(m_sig, m_pred);
            rel->add_fact(m_fact);
            ctx.set_reg(m_tgt, rel);
            return true;
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "mk_unary_singleton into " << m_tgt << " sort:" 
                << ctx.get_rel_context().get_rmanager().to_nice_string(m_sig[0]) << " val:" 
                << ctx.get_rel_context().get_rmanager().to_nice_string(m_sig[0], m_fact[0]);
        }
        virtual void make_annotations(execution_context & ctx) {
            std::string s;
            if (!ctx.get_register_annotation(m_tgt, s)) {
                ctx.set_register_annotation(m_tgt, "mk unary singleton");
            }
        }
    };

    instruction * instruction::mk_unary_singleton(ast_manager & m, func_decl* head_pred, const relation_sort & s, 
            const relation_element & val, reg_idx tgt) {
        return alloc(instr_mk_unary_singleton, m, head_pred, s, val, tgt);
    }


    class instr_mk_total : public instruction {
        relation_signature m_sig;
        func_decl* m_pred;
        reg_idx m_tgt;
    public:
        instr_mk_total(const relation_signature & sig, func_decl* p, reg_idx tgt) : m_sig(sig), m_pred(p), m_tgt(tgt) {}
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            ++ctx.m_stats.m_total;
            ctx.set_reg(m_tgt, ctx.get_rel_context().get_rmanager().mk_full_relation(m_sig, m_pred));
            return true;
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "mk_total into " << m_tgt << " sort:" 
                << ctx.get_rel_context().get_rmanager().to_nice_string(m_sig);
        }
        virtual void make_annotations(execution_context & ctx) {
            std::string s;
            if (!ctx.get_register_annotation(m_tgt, s)) {
                ctx.set_register_annotation(m_tgt, "mk_total");
            }
        }
    };

    instruction * instruction::mk_total(const relation_signature & sig, func_decl* pred, reg_idx tgt) {
        return alloc(instr_mk_total, sig, pred, tgt);
    }

    class instr_mark_saturated : public instruction {
        func_decl_ref m_pred;
    public:
        instr_mark_saturated(ast_manager & m, func_decl * pred) 
            : m_pred(pred, m) {}
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            ctx.get_rel_context().get_rmanager().mark_saturated(m_pred);
            return true;
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "mark_saturated " << m_pred->get_name().bare_str();
        }
        virtual void make_annotations(execution_context & ctx) {            
        }
    };

    instruction * instruction::mk_mark_saturated(ast_manager & m, func_decl * pred) {
        return alloc(instr_mark_saturated, m, pred);
    }

    class instr_assert_signature : public instruction {
        relation_signature m_sig;
        reg_idx m_tgt;
    public:
        instr_assert_signature(const relation_signature & s, reg_idx tgt) 
            : m_sig(s), m_tgt(tgt) {}
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            if (ctx.reg(m_tgt)) {
                SASSERT(ctx.reg(m_tgt)->get_signature()==m_sig);
            }
            return true;
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "instr_assert_signature of " << m_tgt << " signature:";
            print_container(m_sig, out);
        }
        virtual void make_annotations(execution_context & ctx) {
            std::string s;
            if (!ctx.get_register_annotation(m_tgt, s)) {
                ctx.set_register_annotation(m_tgt, "assert signature");
            }
        }
    };
    
    instruction * instruction::mk_assert_signature(const relation_signature & s, reg_idx tgt) {
        return alloc(instr_assert_signature, s, tgt);
    }


    // -----------------------------------
    //
    // instruction_block
    //
    // -----------------------------------

    instruction_block::~instruction_block() {
        reset();
    }

    void instruction_block::reset() {
        instr_seq_type::iterator it = m_data.begin();
        instr_seq_type::iterator end = m_data.end();
        for(; it!=end; ++it) {
            dealloc(*it);
        }
        m_data.reset();
        m_observer = 0;
    }

    bool instruction_block::perform(execution_context & ctx) const {
        cost_recorder crec;
        instr_seq_type::const_iterator it = m_data.begin();
        instr_seq_type::const_iterator end = m_data.end();
        bool success = true;
        for(; it!=end && success; ++it) {

            instruction * instr=(*it);
            crec.start(instr); //finish is performed by the next start() or by the destructor of crec

            TRACE("dl",      
                tout <<"% ";
                  instr->display_head_impl(ctx, tout);
                tout <<"\n";);
            success = !ctx.should_terminate() && instr->perform(ctx);
        }
        return success;
    }

    void instruction_block::process_all_costs() {
        instr_seq_type::iterator it = m_data.begin();
        instr_seq_type::iterator end = m_data.end();
        for(; it!=end; ++it) {
            (*it)->process_all_costs();
        }
    }


    void instruction_block::collect_statistics(statistics& st) const {
        instr_seq_type::const_iterator it = m_data.begin();
        instr_seq_type::const_iterator end = m_data.end();
        for(; it!=end; ++it) {
            (*it)->collect_statistics(st);
        }
    }

    void instruction_block::make_annotations(execution_context & ctx) {
        instr_seq_type::iterator it = m_data.begin();
        instr_seq_type::iterator end = m_data.end();
        for(; it!=end; ++it) {
            (*it)->make_annotations(ctx);
        }
    }

    void instruction_block::display_indented(execution_context const& _ctx, std::ostream & out, std::string indentation) const {
        rel_context const& ctx = _ctx.get_rel_context();
        instr_seq_type::const_iterator it = m_data.begin();
        instr_seq_type::const_iterator end = m_data.end();
        for(; it!=end; ++it) {
            instruction * i = (*it);
            if (i->passes_output_thresholds(ctx.get_context()) || i->being_recorded()) {
                i->display_indented(_ctx, out, indentation);
            }
        }
    }
}

