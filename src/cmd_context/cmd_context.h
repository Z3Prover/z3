/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    cmd_context.h

Abstract:
    Ultra-light command context.
    It provides a generic command pluging infrastructure.
    A command context also provides names (aka symbols) to Z3 objects.
    These names are used to reference Z3 objects in commands.

Author:

    Leonardo (leonardo) 2011-03-01

Notes:

--*/
#ifndef CMD_CONTEXT_H_
#define CMD_CONTEXT_H_

#include<sstream>
#include<vector>
#include "util/stopwatch.h"
#include "util/cmd_context_types.h"
#include "util/event_handler.h"
#include "util/sexpr.h"
#include "util/dictionary.h"
#include "util/scoped_ptr_vector.h"
#include "ast/ast.h"
#include "ast/ast_printer.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/recfun_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "tactic/generic_model_converter.h"
#include "solver/solver.h"
#include "solver/progress_callback.h"
#include "cmd_context/pdecl.h"
#include "cmd_context/tactic_manager.h"
#include "cmd_context/check_logic.h"
#include "cmd_context/context_params.h"


class func_decls {
    func_decl * m_decls;
    bool signatures_collide(func_decl* f, func_decl* g) const;
    bool signatures_collide(unsigned n, sort*const* domain, sort* range, func_decl* g) const;
public:
    func_decls():m_decls(nullptr) {}
    func_decls(ast_manager & m, func_decl * f);
    void finalize(ast_manager & m);
    bool contains(func_decl * f) const;
    bool contains(unsigned n, sort* const* domain, sort* range) const;
    bool insert(ast_manager & m, func_decl * f);
    void erase(ast_manager & m, func_decl * f);
    bool more_than_one() const;
    bool clash(func_decl * f) const;
    bool empty() const { return m_decls == nullptr; }
    func_decl * first() const;
    func_decl * find(unsigned arity, sort * const * domain, sort * range) const;
    func_decl * find(ast_manager & m, unsigned num_args, expr * const * args, sort * range) const;
    unsigned get_num_entries() const;
    func_decl * get_entry(unsigned inx);
};

struct macro_decl {
    ptr_vector<sort> m_domain;
    expr*            m_body;

    macro_decl(unsigned arity, sort *const* domain, expr* body):
        m_domain(arity, domain), m_body(body) {}

    void dec_ref(ast_manager& m) { m.dec_ref(m_body); }

};

class macro_decls {
    vector<macro_decl>* m_decls;
public:
    macro_decls() { m_decls = nullptr; }
    void finalize(ast_manager& m);
    bool insert(ast_manager& m, unsigned arity, sort *const* domain, expr* body);
    expr* find(unsigned arity, sort *const* domain) const;
    void erase_last(ast_manager& m);
    vector<macro_decl>::iterator begin() const { return m_decls->begin(); }
    vector<macro_decl>::iterator end() const { return m_decls->end(); }
};

/**
   \brief Generic wrapper.
*/
class object_ref {
    unsigned m_ref_count;
public:
    object_ref():m_ref_count(0) {}
    virtual ~object_ref() {}
    virtual void finalize(cmd_context & ctx) = 0;
    void inc_ref(cmd_context & ctx) {
        m_ref_count++;
    }
    void dec_ref(cmd_context & ctx) {
        SASSERT(m_ref_count > 0);
        m_ref_count--;
        if (m_ref_count == 0) {
            finalize(ctx);
            dealloc(this);
        }
    }
    virtual char const * kind() const = 0;
};

class ast_object_ref : public object_ref {
    ast * m_ast;
public:
    ast_object_ref(cmd_context & ctx, ast * a);
    void finalize(cmd_context & ctx) override;
    ast * get_ast() const { return m_ast; }
    static char const * cls_kind() { return "AST"; }
    char const * kind() const override { return cls_kind(); }
};

class stream_ref {
    std::string    m_default_name;
    std::ostream & m_default;
    std::string    m_name;
    std::ostream * m_stream;
    bool           m_owner;
public:
    stream_ref(const std::string& n, std::ostream & d):m_default_name(n), m_default(d), m_name(n), m_stream(&d), m_owner(false) {}
    ~stream_ref() { reset(); }
    void set(char const * name);
    void set(std::ostream& strm);
    void reset();
    std::ostream & operator*() { return *m_stream; }
    char const * name() const { return m_name.c_str(); }
};

struct builtin_decl {
    family_id      m_fid;
    decl_kind      m_decl;
    builtin_decl * m_next;
    builtin_decl():m_fid(null_family_id), m_decl(0), m_next(nullptr) {}
    builtin_decl(family_id fid, decl_kind k, builtin_decl * n = nullptr):m_fid(fid), m_decl(k), m_next(n) {}
};

class opt_wrapper : public check_sat_result {
public:
    virtual bool empty() = 0;
    virtual void push() = 0;
    virtual void pop(unsigned n) = 0;
    virtual lbool optimize(expr_ref_vector const& asms) = 0;
    virtual void set_hard_constraints(expr_ref_vector const & hard) = 0;
    virtual void display_assignment(std::ostream& out) = 0;
    virtual bool is_pareto() = 0;
    virtual void set_logic(symbol const& s) = 0;
    virtual void get_box_model(model_ref& mdl, unsigned index) = 0;
    virtual void updt_params(params_ref const& p) = 0;
};

class cmd_context : public progress_callback, public tactic_manager, public ast_printer_context {
public:
    enum status {
        UNSAT, SAT, UNKNOWN
    };

    enum check_sat_state {
        css_unsat, css_sat, css_unknown, css_clear
    };

    typedef std::pair<unsigned, expr*> macro;

    struct scoped_watch {
        cmd_context &   m_ctx;
    public:
        scoped_watch(cmd_context & ctx):m_ctx(ctx) { m_ctx.m_watch.reset(); m_ctx.m_watch.start(); }
        ~scoped_watch() { m_ctx.m_watch.stop(); }
    };

protected:
    context_params               m_params;
    bool                         m_main_ctx;
    symbol                       m_logic;
    bool                         m_interactive_mode;
    bool                         m_global_decls;
    bool                         m_print_success;
    unsigned                     m_random_seed;
    bool                         m_produce_unsat_cores;
    bool                         m_produce_unsat_assumptions;
    bool                         m_produce_assignments;
    status                       m_status;
    bool                         m_numeral_as_real;
    bool                         m_ignore_check;      // used by the API to disable check-sat() commands when parsing SMT 2.0 files.
    bool                         m_processing_pareto; // used when re-entering check-sat for pareto front.
    bool                         m_exit_on_error;

    static std::ostringstream    g_error_stream;

    generic_model_converter_ref  m_mc0;
    ast_manager *                m_manager;
    bool                         m_own_manager;
    bool                         m_manager_initialized;
    pdecl_manager *              m_pmanager;
    sexpr_manager *              m_sexpr_manager;
    check_logic                  m_check_logic;
    stream_ref                   m_regular;
    stream_ref                   m_diagnostic;
    dictionary<cmd*>             m_cmds;
    dictionary<builtin_decl>     m_builtin_decls;
    scoped_ptr_vector<builtin_decl> m_extra_builtin_decls; // make sure that dynamically allocated builtin_decls are deleted
    dictionary<object_ref*>      m_object_refs; // anything that can be named.
    dictionary<sexpr*>           m_user_tactic_decls;

    dictionary<func_decls>       m_func_decls;
    obj_map<func_decl, symbol>   m_func_decl2alias;
    dictionary<psort_decl*>      m_psort_decls;
    dictionary<macro_decls>      m_macros;
    // the following fields m_func_decls_stack, m_psort_decls_stack and m_exprs_stack are used when m_global_decls == false
    typedef std::pair<symbol, func_decl *> sf_pair;
    svector<sf_pair>             m_func_decls_stack;
    svector<symbol>              m_psort_decls_stack;
    svector<symbol>              m_macros_stack;
    ptr_vector<pdecl>            m_psort_inst_stack;

    //
    ptr_vector<pdecl>            m_aux_pdecls;
    ptr_vector<expr>             m_assertions;
    std::vector<std::string>     m_assertion_strings;
    ptr_vector<expr>             m_assertion_names; // named assertions are represented using boolean variables.

    struct scope {
        unsigned m_func_decls_stack_lim;
        unsigned m_psort_decls_stack_lim;
        unsigned m_macros_stack_lim;
        unsigned m_aux_pdecls_lim;
        unsigned m_psort_inst_stack_lim;
        // only m_assertions_lim is relevant when m_global_decls = true
        unsigned m_assertions_lim;
    };

    svector<scope>               m_scopes;
    scoped_ptr<solver_factory>   m_solver_factory;
    ref<solver>                  m_solver;
    ref<check_sat_result>        m_check_sat_result;
    ref<opt_wrapper>             m_opt;

    stopwatch                    m_watch;

    class dt_eh : public new_datatype_eh {
        cmd_context &             m_owner;
        datatype_util             m_dt_util;
    public:
        dt_eh(cmd_context & owner);
        ~dt_eh() override;
        void operator()(sort * dt, pdecl* pd) override;
    };

    friend class dt_eh;
    scoped_ptr<dt_eh>             m_dt_eh;

    class pp_env;
    friend class pp_env;

    scoped_ptr<pp_env>            m_pp_env;
    pp_env & get_pp_env() const;

    void register_builtin_sorts(decl_plugin * p);
    void register_builtin_ops(decl_plugin * p);
    void load_plugin(symbol const & name, bool install_names, svector<family_id>& fids);
    void init_manager_core(bool new_manager);
    void init_manager();
    void init_external_manager();
    void reset_cmds();
    void finalize_cmds();
    void add_declared_functions(model& mdl);

    void restore_func_decls(unsigned old_sz);
    void restore_psort_decls(unsigned old_sz);
    void restore_macros(unsigned old_sz);
    void restore_aux_pdecls(unsigned old_sz);
    void restore_assertions(unsigned old_sz);
    void restore_psort_inst(unsigned old_sz);

    void erase_func_decl_core(symbol const & s, func_decl * f);
    void erase_psort_decl_core(symbol const & s);

    bool logic_has_arith() const;
    bool logic_has_bv() const;
    bool logic_has_pb() const;
    bool logic_has_seq() const;
    bool logic_has_array() const;
    bool logic_has_datatype() const;
    bool logic_has_fpa() const;
    bool logic_has_recfun() const;

    void print_unsupported_msg() { regular_stream() << "unsupported" << std::endl; }
    void print_unsupported_info(symbol const& s, int line, int pos) { if (s != symbol::null) diagnostic_stream() << "; " << s << " line: " << line << " position: " << pos << std::endl;}

    void mk_solver();

    bool contains_func_decl(symbol const& s, unsigned n, sort* const* domain, sort* range) const;

    bool contains_macro(symbol const& s) const;
    bool contains_macro(symbol const& s, func_decl* f) const;
    bool contains_macro(symbol const& s, unsigned arity, sort *const* domain) const;
    void insert_macro(symbol const& s, unsigned arity, sort*const* domain, expr* t);
    void erase_macro(symbol const& s);
    bool macros_find(symbol const& s, unsigned n, expr*const* args, expr*& t) const;

    recfun::decl::plugin& get_recfun_plugin();

public:
    cmd_context(bool main_ctx = true, ast_manager * m = nullptr, symbol const & l = symbol::null);
    ~cmd_context() override;
    void set_cancel(bool f);
    context_params  & params() { return m_params; }
    solver_factory &get_solver_factory() { return *m_solver_factory; }
    opt_wrapper*  get_opt();
    void          set_opt(opt_wrapper* o);
    void global_params_updated(); // this method should be invoked when global (and module) params are updated.
    bool set_logic(symbol const & s);
    bool has_logic() const { return m_logic != symbol::null; }
    symbol const & get_logic() const { return m_logic; }
    bool is_logic(char const * l_name) const { return has_logic() && strcmp(m_logic.bare_str(), l_name) == 0; }
    bool numeral_as_real() const { return m_numeral_as_real; }
    void set_numeral_as_real(bool f) { m_numeral_as_real = f; }
    void set_interactive_mode(bool flag) { m_interactive_mode = flag; }
    void set_ignore_check(bool flag) { m_ignore_check = flag; }
    bool ignore_check() const { return m_ignore_check; }
    void set_exit_on_error(bool flag) { m_exit_on_error = flag; }
    bool exit_on_error() const { return m_exit_on_error; }
    bool interactive_mode() const { return m_interactive_mode; }
    void set_print_success(bool flag) { m_print_success = flag; }
    bool print_success_enabled() const { return m_print_success; }
    void print_success() { if (print_success_enabled())  regular_stream() << "success" << std::endl; }
    void print_unsupported(symbol const & s, int line, int pos) { print_unsupported_msg(); print_unsupported_info(s, line, pos); }
    bool global_decls() const { return m_global_decls; }
    void set_global_decls(bool flag) { SASSERT(!has_manager()); m_global_decls = flag; }
    unsigned random_seed() const { return m_random_seed; }
    void set_random_seed(unsigned s) { m_random_seed = s; }
    bool produce_models() const;
    bool produce_proofs() const;
    bool produce_unsat_cores() const;
    bool well_sorted_check_enabled() const;
    bool validate_model_enabled() const;
    void set_produce_models(bool flag);
    void set_produce_unsat_cores(bool flag);
    void set_produce_proofs(bool flag);
    void set_produce_unsat_assumptions(bool flag) { m_produce_unsat_assumptions = flag; }
    bool produce_assignments() const { return m_produce_assignments; }
    bool produce_unsat_assumptions() const { return m_produce_unsat_assumptions; }
    void set_produce_assignments(bool flag) { m_produce_assignments = flag; }
    void set_status(status st) { m_status = st; }
    status get_status() const { return m_status; }
    std::string reason_unknown() const;

    bool has_manager() const { return m_manager != nullptr; }
    ast_manager & m() const { const_cast<cmd_context*>(this)->init_manager(); return *m_manager; }
    ast_manager & get_ast_manager() override { return m(); }
    pdecl_manager & pm() const { if (!m_pmanager) const_cast<cmd_context*>(this)->init_manager(); return *m_pmanager; }
    sexpr_manager & sm() const { if (!m_sexpr_manager) const_cast<cmd_context*>(this)->m_sexpr_manager = alloc(sexpr_manager); return *m_sexpr_manager; }

    void set_solver_factory(solver_factory * s);
    void set_check_sat_result(check_sat_result * r) { m_check_sat_result = r; }
    check_sat_result * get_check_sat_result() const { return m_check_sat_result.get(); }
    check_sat_state cs_state() const;
    void complete_model(model_ref& mdl) const;
    void validate_model();
    void analyze_failure(model_evaluator& ev, expr* e, bool expected_value);
    void display_detailed_analysis(std::ostream& out, model_evaluator& ev, expr* e);
    void display_model(model_ref& mdl);

    void register_plugin(symbol const & name, decl_plugin * p, bool install_names);
    bool is_func_decl(symbol const & s) const;
    bool is_sort_decl(symbol const& s) const { return m_psort_decls.contains(s); }
    void insert(cmd * c);
    void insert(symbol const & s, func_decl * f);
    void insert(func_decl * f) { insert(f->get_name(), f); }
    void insert(symbol const & s, psort_decl * p);
    void insert(psort_decl * p) { insert(p->get_name(), p); }
    void insert(symbol const & s, unsigned arity, sort *const* domain, expr * t);
    void insert(symbol const & s, object_ref *);
    void insert(tactic_cmd * c) { tactic_manager::insert(c); }
    void insert(probe_info * p) { tactic_manager::insert(p); }
    void insert_user_tactic(symbol const & s, sexpr * d);
    void insert_aux_pdecl(pdecl * p);
    void model_add(symbol const & s, unsigned arity, sort *const* domain, expr * t);
    void model_del(func_decl* f);
    void insert_rec_fun(func_decl* f, expr_ref_vector const& binding, svector<symbol> const& ids, expr* e);
    void insert_rec_fun_as_axiom(func_decl* f, expr_ref_vector const& binding, svector<symbol> const& ids, expr* e);
    func_decl * find_func_decl(symbol const & s) const;
    func_decl * find_func_decl(symbol const & s, unsigned num_indices, unsigned const * indices,
                               unsigned arity, sort * const * domain, sort * range) const;
    recfun::promise_def decl_rec_fun(const symbol &name, unsigned int arity, sort *const *domain, sort *range);
    psort_decl * find_psort_decl(symbol const & s) const;
    cmd * find_cmd(symbol const & s) const;
    sexpr * find_user_tactic(symbol const & s) const;
    object_ref * find_object_ref(symbol const & s) const;
    void mk_const(symbol const & s, expr_ref & result) const;
    void mk_app(symbol const & s, unsigned num_args, expr * const * args, unsigned num_indices, parameter const * indices, sort * range,
                expr_ref & r) const;
    void erase_cmd(symbol const & s);
    void erase_func_decl(symbol const & s);
    void erase_func_decl(symbol const & s, func_decl * f);
    void erase_func_decl(func_decl * f) { erase_func_decl(f->get_name(), f); }
    void erase_psort_decl(symbol const & s);
    void erase_object_ref(symbol const & s);
    void erase_user_tactic(symbol const & s);
    void reset_func_decls();
    void reset_psort_decls();
    void reset_macros();
    void reset_object_refs();
    void reset_user_tactics();
    void set_regular_stream(char const * name) { m_regular.set(name); }
    void set_regular_stream(std::ostream& out) { m_regular.set(out); }
    void set_diagnostic_stream(std::ostream& out) { m_diagnostic.set(out); }
    void set_diagnostic_stream(char const * name);
    std::ostream & regular_stream() override { return *m_regular; }
    std::ostream & diagnostic_stream() override { return *m_diagnostic; }
    char const * get_regular_stream_name() const { return m_regular.name(); }
    char const * get_diagnostic_stream_name() const { return m_diagnostic.name(); }
    typedef dictionary<cmd*>::iterator cmd_iterator;
    cmd_iterator begin_cmds() const { return m_cmds.begin(); }
    cmd_iterator end_cmds() const { return m_cmds.end(); }

    typedef dictionary<sexpr*>::iterator user_tactic_iterator;
    user_tactic_iterator begin_user_tactics() const { return m_user_tactic_decls.begin(); }
    user_tactic_iterator end_user_tactics() const { return m_user_tactic_decls.end(); }

    void display_assertions();
    void display_statistics(bool show_total_time = false, double total_time = 0.0);
    void display_dimacs();
    void reset(bool finalize = false);
    void assert_expr(expr * t);
    void assert_expr(symbol const & name, expr * t);
    void push_assert_string(std::string const & s) { SASSERT(m_interactive_mode); m_assertion_strings.push_back(s); }
    void push();
    void push(unsigned n);
    void pop(unsigned n);
    void check_sat(unsigned num_assumptions, expr * const * assumptions);
    void get_consequences(expr_ref_vector const& assumptions, expr_ref_vector const& vars, expr_ref_vector & conseq);
    void reset_assertions();
    // display the result produced by a check-sat or check-sat-using commands in the regular stream
    void display_sat_result(lbool r);
    // check if result produced by check-sat or check-sat-using matches the known status
    void validate_check_sat_result(lbool r);
    unsigned num_scopes() const { return m_scopes.size(); }

    dictionary<macro_decls> const & get_macros() const { return m_macros; }

    model_converter* get_model_converter() { return m_mc0.get(); }

    bool is_model_available(model_ref& md) const;

    double get_seconds() const { return m_watch.get_seconds(); }

    ptr_vector<expr> const& assertions() const { return m_assertions; }
    ptr_vector<expr> const& assertion_names() const { return m_assertion_names; }

    /**
       \brief Hack: consume assertions if there are no scopes.
       This method is useful for reducing memory consumption in huge benchmarks were incrementality is not an issue.
    */
    bool consume_assertions() {
        if (num_scopes() > 0)
            return false;
        restore_assertions(0);
        return true;
    }

    format_ns::format * pp(sort * s) const;
    void pp(sort * s, format_ns::format_ref & r) const override { r = pp(s); }
    void pp(func_decl * f, format_ns::format_ref & r) const override;
    void pp(expr * n, unsigned num_vars, char const * var_prefix, format_ns::format_ref & r, sbuffer<symbol> & var_names) const override;
    void pp(expr * n, format_ns::format_ref & r) const override;
    void display(std::ostream & out, sort * s, unsigned indent = 0) const override;
    void display(std::ostream & out, expr * n, unsigned indent, unsigned num_vars, char const * var_prefix, sbuffer<symbol> & var_names) const override;
    void display(std::ostream & out, expr * n, unsigned indent = 0) const override;
    void display(std::ostream & out, func_decl * f, unsigned indent = 0) const override;

    // dump assertions in out using the pretty printer.
    void dump_assertions(std::ostream & out) const;

    // display assertions as a SMT2 benchmark.
    void display_smt2_benchmark(std::ostream & out, unsigned num, expr * const * assertions, symbol const & logic = symbol::null) const;


    void slow_progress_sample() override;
    void fast_progress_sample() override;
};

std::ostream & operator<<(std::ostream & out, cmd_context::status st);


class th_solver : public expr_solver {
    cmd_context& m_ctx;
    params_ref   m_params;
    ref<solver> m_solver;
public:
    th_solver(cmd_context& ctx): m_ctx(ctx) {}
    
    lbool check_sat(expr* e) override {
        if (!m_solver) {
            m_solver = m_ctx.get_solver_factory()(m_ctx.m(), m_params, false, true, false, symbol::null);
        }
        m_solver->push();
        m_solver->assert_expr(e);
        lbool r = m_solver->check_sat(0,nullptr);
        m_solver->pop(1);
        return r;
    }
};

#endif
