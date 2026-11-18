/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    tactic.h

Abstract:

    Abstract tactic object.
    It used to be called assertion_set_strategy.
    The main improvement is the support for multiple subgoals.

Author:

    Leonardo (leonardo) 2011-10-13

Notes:

--*/
#pragma once

#include <string>
#include <vector>
#include "util/params.h"
#include "util/lbool.h"
#include "util/statistics.h"
#include "tactic/user_propagator_base.h"
#include "tactic/goal.h"
#include "tactic/tactic_exception.h"

class progress_callback;

/**
   \brief State of a tactic::display walk.

   A walk builds a tree of nodes that display_tactic prints as an s-expression in the
   syntax of the tactic language (the syntax check-sat-using parses). A node is a leaf
   ("simplify", "(fail-if produce-proofs)") or a combinator opened with open("(then")
   and closed with close(), whose children are the nodes added in between.
   Comments hold what has no syntax: the effective parameters of a leaf, and the
   constructs marked "not parseable:".
*/
struct tactic_display_ctx {
    struct node {
        std::string       head;      // leaf text, or the opening of a combinator: "(then", "(if is-qfbv"
        std::string       tail;      // arguments after the children: ":som true", "5"
        std::string       comment;   // comment on the head line (the only line of a leaf)
        std::string       tail_comment; // comment on the last line
        std::vector<node> children;
        bool              is_leaf = true;
    };
    // out: descriptors of the tactics displayed with this context
    param_descrs           descrs;
    // in: descriptors of every tactic of the pipeline, collected by a previous walk
    param_descrs const *   pipeline = nullptr;
    // out: the parameters marked [unused]
    svector<symbol> *      unused = nullptr;

    tactic_display_ctx() { m_stack.push_back(node()); }
    void leaf(std::string const & text, std::string const & comment = std::string());
    void open(std::string const & head, std::string const & comment = std::string());
    void close(std::string const & tail = std::string(), std::string const & tail_comment = std::string());
    // the nodes displayed at the top level
    std::vector<node> const & roots() const { return m_stack[0].children; }
private:
    std::vector<node> m_stack;
};

typedef ptr_buffer<goal> goal_buffer;

class tactic : public user_propagator::core {
    unsigned m_ref_count = 0;
    char const * m_display_name = nullptr;
public:
    void inc_ref() { m_ref_count++; }
    void dec_ref() { SASSERT(m_ref_count > 0); m_ref_count--; if (m_ref_count == 0) dealloc(this); }

    virtual void updt_params(params_ref const & p) {}
    virtual void collect_param_descrs(param_descrs & r) {}

    /**
       \brief Display the pipeline rooted at this tactic into \c ctx.

       \c p are the parameters the tactic receives from its parent through updt_params.
       Combinators display their children with the parameters the children receive,
       so a leaf shows the values in effect for it. The default displays a leaf: the
       display name, with the entries of \c p declared by collect_param_descrs in a
       comment, and adds its descriptors to ctx.descrs. Parameters that a tactic only
       receives through its constructor are not shown. Use display_tactic to display
       a pipeline.
    */
    virtual void display(params_ref const & p, tactic_display_ctx & ctx);

    /**
       \brief Name of the tactic in the tactic language: the name under which the
       tactic is registered with Z3_ADD_TACTIC, or nullptr if no registered name
       builds it. It differs from name(), which is kept as is because it appears in
       verbose output. Factories whose class serves several registered names set it
       with set_display_name.
    */
    char const * display_name() const;
    void set_display_name(char const * n) { m_display_name = n; }

    /**
       \brief Apply tactic to goal \c in.
       
       The list of resultant subgoals is stored in \c result.
       The content of \c in may be destroyed during the operation.
                
       The output parameter \c core is used to accumulate the unsat core of closed subgoals.
       It must be 0 if dependency tracking is disabled, or the result is decided unsat, or 
       no tagged assertions were used to close any subgoal.
       
       Note that, this signature is not compatible with the one described in the paper:
       "The Strategy Challenge in SMT Solving".
       The approach in the paper is conceptually simpler, but (for historical reasons) it would
       require a lot of re-engineering in the Z3 code. In Z3, we keep a proof/justification for every formula
       in a goal.
       
       Therefore, in most cases, pc == 0 and core == 0 for non-branching tactics.
    */
    virtual void operator()(goal_ref const & in, goal_ref_buffer& result) = 0;

    virtual void collect_statistics(statistics& st) const {  }
    virtual void reset_statistics() {}
    virtual void cleanup() = 0;
    virtual void reset() { cleanup(); }

    // for backward compatibility
    virtual void set_logic(symbol const & l) {}
    virtual void set_progress_callback(progress_callback * callback) {}

    // translate tactic to the given manager
    virtual tactic * translate(ast_manager & m) = 0;

    static void checkpoint(ast_manager& m);

    void register_on_clause(void* ctx, user_propagator::on_clause_eh_t& on_clause) override {
        throw default_exception("tactic does not support clause logging");
    }

    void user_propagate_init(
        void* ctx,
        user_propagator::push_eh_t& push_eh,
        user_propagator::pop_eh_t& pop_eh,
        user_propagator::fresh_eh_t& fresh_eh) override {
        throw default_exception("tactic does not support user propagation");
    }

    void user_propagate_register_expr(expr* e) override { }
    virtual char const* name() const = 0;

protected:
    friend class nary_tactical;
    friend class binary_tactical;
    friend class unary_tactical;

};

typedef ref<tactic>         tactic_ref;
typedef sref_vector<tactic> tactic_ref_vector;
typedef sref_buffer<tactic> tactic_ref_buffer;

/**
   \brief Self-registration for built-in tactics, consumed by cmd_context/tactic_manager.cpp's
   install_tactics() to populate a tactic_manager (once per Z3 context) -- replaces the old
   ADD_TACTIC('name', 'descr', 'code') comment scraped by scripts/mk_install_tactic_cpp.py.
   Lives here (rather than in cmd_context, which depends on tactic) so headers declaring
   tactics don't need to depend "upward" on the frontend layer.
   Each Z3_ADD_TACTIC(...) instantiates one as an `inline` global (safe across however many
   translation units include the declaring header); the factory itself is a plain function
   pointer, not invoked at registration time -- only later, once per tactic_manager, from
   install_tactics().
*/
struct tactic_registration {
    typedef tactic* (*factory_t)(ast_manager&, const params_ref&);
    char const * name;
    char const * descr;
    factory_t factory;
    tactic_registration * next;
    static inline tactic_registration * g_head = nullptr;
    tactic_registration(char const * name, char const * descr, factory_t factory):
        name(name), descr(descr), factory(factory), next(g_head) {
        g_head = this;
    }
};

#define Z3_ADD_TACTIC(TAG, NAME, DESCR, CODE) \
  inline tactic_registration g_z3_tactic_registration_##TAG(NAME, DESCR, [](ast_manager & m, params_ref const & p) -> tactic* { return CODE; })

// minimum verbosity level for tactics
#define TACTIC_VERBOSITY_LVL 10

class tactic_report {
    struct imp;
    imp *  m_imp;
public:
    tactic_report(char const * id, goal const & g);
    ~tactic_report();
};

void report_tactic_progress(char const * id, unsigned val);

class statistics_report {
    tactic* m_tactic = nullptr;
    std::function<void(statistics& st)> m_collector;
public:
    statistics_report(tactic& t):m_tactic(&t) {}
    statistics_report(std::function<void(statistics&)>&& coll): m_collector(std::move(coll)) {}
    ~statistics_report();
};

class skip_tactic : public tactic {
public:
    void operator()(goal_ref const & in, goal_ref_buffer& result) override;
    void cleanup() override {}
    tactic * translate(ast_manager & m) override { return this; } 
    char const* name() const override { return "skip"; }
    void collect_statistics(statistics& st) const override {}
    void user_propagate_initialize_value(expr* var, expr* value) override { }
};

/**
   \brief Display the entries of \c p as " :key value", restricted to the keys declared
   in \c descrs if it is not null. Default values are marked "(default)".
*/
void display_tactic_params(std::ostream & out, params_ref const & p, param_descrs const * descrs = nullptr);

/**
   \brief Display the pipeline rooted at \c t when it receives the parameters \c p,
   in the syntax of the tactic language.

   The output parses back with check-sat-using unless it contains a comment
   "not parseable:". A parameter set by using_params is marked [unused] if no tactic
   of the pipeline declares it in collect_param_descrs, and it is then added to \c unused.
*/
void display_tactic(std::ostream & out, tactic & t, params_ref const & p, svector<symbol> * unused = nullptr);

/**
   \brief Quote \c s as a string of the tactic language.
*/
std::string tactic_display_string(char const * s);

tactic * mk_skip_tactic();
tactic * mk_fail_tactic();
tactic * mk_fail_if_undecided_tactic();
tactic*  mk_lazy_tactic(ast_manager& m, params_ref const& p, std::function<tactic*(ast_manager& m, params_ref const& p)>);

Z3_ADD_TACTIC(skip, "skip", "do nothing tactic.", mk_skip_tactic());
Z3_ADD_TACTIC(fail, "fail", "always fail tactic.", mk_fail_tactic());
Z3_ADD_TACTIC(fail_if_undecided, "fail-if-undecided", "fail if goal is undecided.", mk_fail_if_undecided_tactic());

tactic * mk_report_verbose_tactic(char const * msg, unsigned lvl);
tactic * mk_trace_tactic(char const * tag);

void exec(tactic & t, goal_ref const & in, goal_ref_buffer & result);
lbool check_sat(tactic & t, goal_ref & g, model_ref & md, labels_vec & labels, proof_ref & pr, expr_dependency_ref & core, std::string & reason_unknown);

// Throws an exception if goal \c in requires proof generation.
void fail_if_proof_generation(char const * tactic_name, goal_ref const & in);
void fail_if_unsat_core_generation(char const * tactic_name, goal_ref const & in);
void fail_if_model_generation(char const * tactic_name, goal_ref const & in);
void fail_if_has_quantifiers(char const* tactic_name, goal_ref const& in);

