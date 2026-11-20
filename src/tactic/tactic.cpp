/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    tactic.h

Abstract:

    Abstract tactic object.

Author:

    Leonardo (leonardo) 2011-10-13

Notes:

--*/
#include<iomanip>
#include<sstream>
#include<cstring>
#include "tactic/tactic.h"
#include "tactic/probe.h"
#include "util/stopwatch.h"
#include "util/gparams.h"
#include "model/model_v2_pp.h"


struct tactic_report::imp {
    char const *    m_id;
    goal const &    m_goal;
    stopwatch       m_watch;
    double          m_start_memory;

    imp(char const * id, goal const & g):
        m_id(id),
        m_goal(g),
        m_start_memory(static_cast<double>(memory::get_allocation_size())/static_cast<double>(1024*1024)) {
        m_watch.start();
        TRACE(tactic, g.display_with_proofs(tout << id << "\n"););
        SASSERT(g.is_well_formed());
    }
        
    ~imp() {
        m_watch.stop();
        double end_memory = static_cast<double>(memory::get_allocation_size())/static_cast<double>(1024*1024);
        TRACE(tactic, m_goal.display(tout << m_id << "\n");
              if (m_goal.mc()) m_goal.mc()->display(tout);
              );
        IF_VERBOSE(0, 
                   verbose_stream() << "(" << m_id
                   << " :num-exprs " << m_goal.num_exprs()
                   << " :num-asts " << m_goal.m().get_num_asts();
                   if (!get_suppress_platform_verbose())
                       verbose_stream()
                       << " :time " << std::fixed << std::setprecision(2) << m_watch.get_seconds()
                       << " :before-memory " << std::fixed << std::setprecision(2) << m_start_memory
                       << " :after-memory " << std::fixed << std::setprecision(2) << end_memory;
                   verbose_stream() << ")\n");
        IF_VERBOSE(20, m_goal.display(verbose_stream() << m_id << "\n"));
        SASSERT(m_goal.is_well_formed());
    }
};

tactic_report::tactic_report(char const * id, goal const & g) {
    if (get_verbosity_level() >= TACTIC_VERBOSITY_LVL)
        m_imp = alloc(imp, id, g);
    else
        m_imp = nullptr;
}

tactic_report::~tactic_report() {
    if (m_imp)
        dealloc(m_imp);
}

void report_tactic_progress(char const * id, unsigned val) {
    if (val > 0) {
        IF_VERBOSE(TACTIC_VERBOSITY_LVL, verbose_stream() << "(" << id << " " << val << ")\n");        
    }
}
statistics_report::~statistics_report() {
    statistics st;
    if (m_tactic)
        m_tactic->collect_statistics(st);
    else if (m_collector)
        m_collector(st);
    if (st.size() == 0)
        return;
    IF_VERBOSE(TACTIC_VERBOSITY_LVL, st.display_smt2(verbose_stream()));
}


void display_tactic_params(std::ostream & out, params_ref const & p, param_descrs const * descrs, bool annotate) {
    for (unsigned i = 0; i < p.size(); ++i) {
        symbol k = p.get_key(i);
        symbol name = k;
        if (descrs && descrs->get_kind_in_module(name) == CPK_INVALID)
            continue;
        out << " :" << k << " ";
        if (!p.is_default(k)) {
            p.display(out, k);
            continue;
        }
        // A default yields to the value the user set in the global module of k
        // (the getters with a fallback return it).
        char const * module = descrs ? descrs->get_module(k) : nullptr;
        params_ref g = module ? gparams::get_module(module) : params_ref();
        if (g.contains(k)) {
            g.display(out, k);
            if (annotate)
                out << " (global)";
        }
        else {
            p.display(out, k);
            if (annotate)
                out << " (default)";
        }
    }
}

// Name of a tactic class (tactic::name) -> name it is registered under, for the
// classes whose name differs from the registered one. nullptr: no registered name
// builds the class unless its factory sets one (tactic::set_display_name).
// tactic_unused_params.cpp checks that each registered tactic that is a single
// step displays as its registered name.
static char const * const g_registered_names[][2] = {
    { "add_bounds",          "add-bounds" },
    { "bit_blaster",         "bit-blast" },
    { "bv_size",             "reduce-bv-size" },
    { "collect_statistics",  "collect-statistics" },
    { "ctx_simplify",        "ctx-simplify" },
    { "ctx_solver_simplify", "ctx-solver-simplify" },
    { "diff_neq",            "diff-neq" },
    { "elim-unconstrained",  "elim-uncnstr2" },
    { "elim_small_bv",       "elim-small-bv" },
    { "elim_term_ite",       "elim-term-ite" },
    { "elim_uncstr",         "elim-uncnstr" },
    { "fix_dl_var",          "fix-dl-var" },
    { "fp2bv",               "fpa2bv" },
    { "macro_finder",        "macro-finder" },
    { "nnf",                 "snf" },            // "nnf" is (using-params snf :mode full)
    { "normalize_bounds",    "normalize-bounds" },
    { "propagate_values",    "propagate-values" },
    { "purify_arith",        "purify-arith" },
    { "qe-lite",             "qe-light" },
    { "qsat",                "qe2" },
    { "quasi_macros",        "quasi-macros" },
    { "recover_01",          "recover-01" },
    { "reduce-args",         "reduce-args2" },
    { "reduce_args",         "reduce-args" },
    { "solver_subsumption",  "solver-subsumption" },
    { "split_clause",        "split-clause" },
    { "symmetry_reduce",     "symmetry-reduce" },
    { "tseitin_cnf",         "tseitin-cnf-core" },
    { "unit_subsumption",    "unit-subsume-simplify" },
    { "parallel_tactic",     nullptr },          // psmt, pqffd, psat: set by the factory
    { "solver2tactic",       nullptr },          // qffd, smtfd, smt: set by the factory
    // registered only inside a pipeline: "fm" is (then simplify fm)
    { "degree_shift",        nullptr },
    { "ff-sat",              nullptr },
    { "fm",                  nullptr },
    { "qfufbv_ackr",         nullptr },
    { "sls",                 nullptr },
    { "sls-smt",             nullptr },
    { "subpaving",           nullptr },
};

char const * tactic::display_name() const {
    if (m_display_name)
        return m_display_name;
    char const * n = name();
    for (auto const & e : g_registered_names)
        if (strcmp(e[0], n) == 0)
            return e[1];
    return n;
}

std::string tactic_display_string(char const * s) {
    std::string r = "\"";
    for (; *s; ++s) {
        if (*s == '"')
            r += '"';
        r += *s;
    }
    return r + "\"";
}

static std::string join_comments(std::string const & a, std::string const & b) {
    if (a.empty())
        return b;
    if (b.empty())
        return a;
    return a + "; " + b;
}

void tactic_display_ctx::leaf(std::string const & text, std::string const & comment) {
    node n;
    n.head = text;
    n.comment = comment;
    m_stack.back().children.push_back(std::move(n));
}

void tactic_display_ctx::open(std::string const & head, std::string const & comment) {
    node n;
    n.head = head;
    n.comment = comment;
    n.is_leaf = false;
    m_stack.push_back(std::move(n));
}

void tactic_display_ctx::close(std::string const & tail, std::string const & tail_comment) {
    SASSERT(m_stack.size() > 1);
    node n = std::move(m_stack.back());
    m_stack.pop_back();
    n.tail = tail;
    n.tail_comment = tail_comment;
    // (then a (then b c)) is the tactic (then a b c) builds: display it flat. A nested
    // sequence can reach here through wrappers that display their child (cleanup, lazy).
    if ((n.head == "(then" || n.head == "(par-then") && !n.children.empty()) {
        node & last = n.children.back();
        if (!last.is_leaf && last.head == n.head && last.tail.empty() && last.comment.empty() && last.tail_comment.empty()) {
            std::vector<node> cs = std::move(last.children);
            n.children.pop_back();
            for (node & c : cs)
                n.children.push_back(std::move(c));
        }
    }
    m_stack.back().children.push_back(std::move(n));
}

namespace {
    typedef tactic_display_ctx::node display_node;

    struct display_line {
        unsigned    indent;
        std::string code;
        std::string comment;
    };

    // A subtree stays on one line if its code fits and the comment at the end of the
    // line can only be about one step: the subtree has no comment, or one leaf and
    // one comment.
    const unsigned display_width = 80;

    void count(display_node const & n, unsigned & leaves, unsigned & comments) {
        leaves += n.is_leaf;
        comments += !n.comment.empty() + !n.tail_comment.empty();
        for (display_node const & c : n.children)
            count(c, leaves, comments);
    }

    void flat(display_node const & n, std::string & code, std::string & comment) {
        code += n.head;
        comment = join_comments(comment, n.comment);
        if (n.is_leaf)
            return;
        for (display_node const & c : n.children) {
            code += " ";
            flat(c, code, comment);
        }
        if (!n.tail.empty())
            code += " " + n.tail;
        code += ")";
        comment = join_comments(comment, n.tail_comment);
    }

    void layout(display_node const & n, unsigned indent, std::vector<display_line> & lines) {
        if (n.is_leaf) {
            lines.push_back({ indent, n.head, n.comment });
            return;
        }
        unsigned leaves = 0, comments = 0;
        count(n, leaves, comments);
        if (comments == 0 || (leaves == 1 && comments == 1)) {
            display_line l = { indent, std::string(), std::string() };
            flat(n, l.code, l.comment);
            if (indent + l.code.size() <= display_width) {
                lines.push_back(l);
                return;
            }
        }
        lines.push_back({ indent, n.head, n.comment });
        for (display_node const & c : n.children)
            layout(c, indent + 2, lines);
        if (!n.tail.empty())
            lines.push_back({ indent + 2, n.tail, n.tail_comment });
        else
            lines.back().comment = join_comments(lines.back().comment, n.tail_comment);
        lines.back().code += ")";
    }
}

void tactic::display_pipeline(params_ref const & p, tactic_display_ctx & ctx) {
    param_descrs d;
    // collect first: some tactics only know their name once their state is created.
    collect_param_descrs(d);
    std::ostringstream ps;
    display_tactic_params(ps, p, &d, ctx.annotate);
    std::string comment = ps.str();
    if (!comment.empty())
        comment = "active:" + comment; // ps starts with a space
    char const * n = display_name();
    if (n)
        ctx.leaf(n, comment);
    else
        ctx.leaf(std::string("(") + name() + ")",
                 join_comments(std::string("not parseable: no registered tactic for ") + name(), comment));
    ctx.descrs.copy(d);
}

void display_tactic(std::ostream & out, tactic & t, params_ref const & p, svector<symbol> * unused, bool annotate) {
    // First walk: collect the descriptors of the whole pipeline.
    // lazy_tactic builds its tactic when displayed, so the walk cannot be replaced
    // by collect_param_descrs.
    tactic_display_ctx all;
    t.display_pipeline(p, all);
    tactic_display_ctx ctx;
    ctx.pipeline = &all.descrs;
    ctx.unused = unused;
    ctx.annotate = annotate;
    t.display_pipeline(p, ctx);
    std::vector<display_line> lines;
    for (display_node const & n : ctx.roots())
        layout(n, 0, lines);
    for (display_line const & l : lines) {
        out << std::string(l.indent, ' ') << l.code;
        if (!l.comment.empty())
            out << " ; " << l.comment;
        out << "\n";
    }
}

void skip_tactic::operator()(goal_ref const & in, goal_ref_buffer& result) {
    result.push_back(in.get());
}

tactic * mk_skip_tactic() {
    return alloc(skip_tactic);
}

class lazy_tactic : public tactic {
    ast_manager& m;
    params_ref p;
    std::function<tactic* (ast_manager& m, params_ref const& p)> m_mk_tactic;
    tactic* m_tactic = nullptr;
    symbol m_logic;
    void ensure_tactic() {
        if (!m_tactic) {
            m_tactic = m_mk_tactic(m, p);
            m_tactic->updt_params(p);
            m_tactic->set_logic(m_logic);
        }
    }
public:
    lazy_tactic(ast_manager& m, params_ref const& p, std::function<tactic* (ast_manager&, params_ref const&)> mk_tactic) : m(m), p(p), m_mk_tactic(mk_tactic) {}
    ~lazy_tactic() override { dealloc(m_tactic); }
    void operator()(goal_ref const& in, goal_ref_buffer& result) override {
        ensure_tactic();
        (*m_tactic)(in, result);
    }
    void updt_params(params_ref const& p) override { 
        this->p.append(p);
        if (m_tactic) m_tactic->updt_params(p);
    }
    void set_logic(symbol const& l) override {
        m_logic = l;
        if (m_tactic) m_tactic->set_logic(l);
    }
    void cleanup() override { if (m_tactic) m_tactic->cleanup(); }
    char const* name() const override { return "lazy tactic"; }
    void display_pipeline(params_ref const & p, tactic_display_ctx & ctx) override {
        // display the tactic that ensure_tactic would build after updt_params(p)
        params_ref new_p = this->p;
        new_p.append(p);
        if (m_tactic) {
            m_tactic->display_pipeline(new_p, ctx);
            return;
        }
        tactic_ref t = m_mk_tactic(m, new_p);
        t->updt_params(new_p);
        t->display_pipeline(new_p, ctx);
    }
    void collect_statistics(statistics& st) const override { if (m_tactic) m_tactic->collect_statistics(st); }
    void user_propagate_initialize_value(expr* var, expr* value) override { if (m_tactic) m_tactic->user_propagate_initialize_value(var, value); }
    tactic* translate(ast_manager& m) override { ensure_tactic(); return m_tactic->translate(m); }
    void reset() override { if (m_tactic) m_tactic->reset(); }
    void reset_statistics() override { if (m_tactic) m_tactic->reset_statistics(); }
    void register_on_clause(void* ctx, user_propagator::on_clause_eh_t& on_clause) override {
        ensure_tactic();
        m_tactic->register_on_clause(ctx, on_clause);
    }
};


tactic* mk_lazy_tactic(ast_manager& m, params_ref const& p, std::function<tactic*(ast_manager& m, params_ref const& p)> mkt) {
    return alloc(lazy_tactic, m, p, mkt);
}

class fail_tactic : public tactic {
public:
    void operator()(goal_ref const & in, goal_ref_buffer & result) override {
        throw tactic_exception("fail tactic");
    }

    void cleanup() override {}

    char const* name() const override { return "fail"; }

    tactic * translate(ast_manager & m) override { return this; }
};

tactic * mk_fail_tactic() {
    return alloc(fail_tactic);
}

class report_verbose_tactic : public skip_tactic {
    char const * m_msg;
    unsigned     m_lvl;
public:
    report_verbose_tactic(char const * msg, unsigned lvl) : m_msg(msg), m_lvl(lvl) {}

    char const* name() const override { return "report-verbose"; }

    void display_pipeline(params_ref const & p, tactic_display_ctx & ctx) override {
        ctx.leaf("(" + std::string(name()) + " " + tactic_display_string(m_msg) + ")", "not parseable: report-verbose");
    }

    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        IF_VERBOSE(m_lvl, verbose_stream() << m_msg << "\n";);
        skip_tactic::operator()(in, result);
    }
};

tactic * mk_report_verbose_tactic(char const * msg, unsigned lvl) {
    return alloc(report_verbose_tactic, msg, lvl);
}

class trace_tactic : public skip_tactic {
    char const * m_tag;
public:
    trace_tactic(char const * tag): m_tag(tag) {}

    char const* name() const override { return "trace"; }

    void display_pipeline(params_ref const & p, tactic_display_ctx & ctx) override {
        ctx.leaf("(" + std::string(name()) + " " + tactic_display_string(m_tag) + ")", "not parseable: trace");
    }
    
    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        TRACE(m_tag, in->display(tout););
        (void)m_tag;
        skip_tactic::operator()(in, result);
    }
};

tactic * mk_trace_tactic(char const * tag) {
    return alloc(trace_tactic, tag);
}

class fail_if_undecided_tactic : public skip_tactic {
public:
    char const* name() const override { return "fail-if-undecided"; }

    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        if (!in->is_decided()) 
            throw tactic_exception("undecided");
        skip_tactic::operator()(in, result);
    }
    void user_propagate_initialize_value(expr* var, expr* value) override { }
};

tactic * mk_fail_if_undecided_tactic() {
    return alloc(fail_if_undecided_tactic);
}

void exec(tactic & t, goal_ref const & in, goal_ref_buffer & result) {
    t.reset_statistics();
    try {
        t(in, result);
        t.cleanup();
    }
    catch (tactic_exception & ex) {
        IF_VERBOSE(TACTIC_VERBOSITY_LVL, verbose_stream() << "(tactic-exception \"" << escaped(ex.what()) << "\")\n");
        t.cleanup();
        throw ex;
    }
}


lbool check_sat(tactic & t, goal_ref & g, model_ref & md, labels_vec & labels, proof_ref & pr, expr_dependency_ref & core, std::string & reason_unknown) {
    bool models_enabled = g->models_enabled();
    bool cores_enabled  = g->unsat_core_enabled();
    md   = nullptr;
    pr   = nullptr;
    core = nullptr;
    ast_manager & m = g->m();
    goal_ref_buffer r;
    try {
        exec(t, g, r);
    }
    catch (z3_exception & ex) {
        reason_unknown = ex.what();
        if (r.size() > 0) pr = r[0]->pr(0);
        return l_undef;
    }
    TRACE(tactic,
          tout << "r.size(): " << r.size() << "\n";
          for (unsigned i = 0; i < r.size(); ++i) r[i]->display_with_dependencies(tout););

    if (r.size() > 0) {
        pr = r[0]->pr(0);
        CTRACE(tactic, pr, tout << pr << "\n";);
    }    

    for (goal * subgoal : r) {
        if (!subgoal->is_decided_sat())
            continue;
        pr = nullptr;
        model_converter_ref mc = subgoal->mc();
        if (mc.get()) {
            (*mc)(labels);
            model_converter2model(m, mc.get(), md);
        }
        if (!m.inc()) {
            reason_unknown = "canceled";
            return l_undef;
        }
        if (!md) {
            // create empty model.
            md = alloc(model, m);
        }
        return l_true;
    }
    if (is_decided_unsat(r)) {
        goal * final = r[0];
        SASSERT(m.is_false(final->form(0)));
        pr = final->pr(0);
        proof_converter_ref pc = final->pc();
        if (pc) {
            try {
                pr = apply(m, pc.get());
                final->set(static_cast<proof_converter*>(nullptr));
                final->update(0, m.mk_false(), pr, final->dep(0));
            }
            catch (z3_exception const& ex) {
                reason_unknown = ex.what();
                pr = nullptr;
                return l_undef;
            }
        }
        if (cores_enabled)  core = final->dep(0);
        return l_false;
    }
    else {
        if (models_enabled && !r.empty()) {
            model_converter_ref mc = r[0]->mc();            
            model_converter2model(m, mc.get(), md);
            if (mc)
                (*mc)(labels);
        }
        reason_unknown = get_reason_unknown(r);
        if (reason_unknown.empty())
            reason_unknown = "unknown";
        return l_undef;
    }
}

void fail_if_proof_generation(char const * tactic_name, goal_ref const & in) {
    if (in->proofs_enabled()) {
        std::string msg = tactic_name;
        msg += " does not support proof production";
        throw tactic_exception(std::move(msg));
    }
}

void fail_if_unsat_core_generation(char const * tactic_name, goal_ref const & in) {
    if (in->unsat_core_enabled()) {
        std::string msg = tactic_name;
        msg += " does not support unsat core production";
        throw tactic_exception(std::move(msg));
    }
}

void fail_if_model_generation(char const * tactic_name, goal_ref const & in) {
    if (in->models_enabled()) {
        std::string msg = tactic_name;
        msg += " does not generate models";
        throw tactic_exception(std::move(msg));
    }
}

void fail_if_has_quantifiers(char const* tactic_name, goal_ref const& g) {
    for (unsigned i = 0; i < g->size(); ++i)
        if (has_quantifiers(g->form(i))) {
            std::string msg = tactic_name;
            msg += " does not apply to quantified goals";
            throw tactic_exception(std::move(msg));
        }
}

void tactic::checkpoint(ast_manager& m) {
    if (!m.inc())
        throw tactic_exception(m.limit().get_cancel_msg());
}
