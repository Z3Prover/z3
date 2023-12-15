/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    dependent_expr_state.h

Abstract:

    abstraction for simplification of dependent expression states.
    A dependent_expr_state is an interface to a set of dependent expressions.
    Dependent expressions are formulas together with a set of dependencies that are coarse grained 
    proof hints or justifications for them. Input assumptions can be self-justified.

    The dependent_expr_simplifier implements main services:
    - push, pop - that scope the local state
    - reduce - to process formulas in a dependent_expr_state between the current value of m_qhead and the size() 
      of the depdenent_expr_state

    A dependent expr_simplifier can be used to:
    - to build a tactic
    - for incremental pre-processing

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-2.
    
--*/

#pragma once

#include "util/trail.h"
#include "util/statistics.h"
#include "util/params.h"
#include "util/z3_exception.h"
#include "ast/converters/model_converter.h"
#include "ast/simplifiers/dependent_expr.h"
#include "ast/simplifiers/model_reconstruction_trail.h"


/**
   abstract interface to state updated by simplifiers.
 */
class dependent_expr_state {
    unsigned m_qhead = 0;
    bool     m_suffix_frozen = false;
    unsigned m_num_recfun = 0, m_num_lambdas = 0;
    lbool    m_has_quantifiers = l_undef;
    ast_mark m_frozen;
    func_decl_ref_vector m_frozen_trail;
    void freeze_prefix();
    void freeze_recfun();
    void freeze_lambda();
    void freeze_terms(expr* term, bool only_as_array, ast_mark& visited);
    void freeze(func_decl* f);
    struct thaw : public trail {
        unsigned sz;
        dependent_expr_state& st;
        thaw(dependent_expr_state& st) : sz(st.m_frozen_trail.size()), st(st) {}
        void undo() override {
            for (unsigned i = st.m_frozen_trail.size(); i-- > sz; )
                st.m_frozen.mark(st.m_frozen_trail.get(i), false);
            st.m_frozen_trail.shrink(sz);
        }
    };
public:
    dependent_expr_state(ast_manager& m) : m_frozen_trail(m) {}
    virtual ~dependent_expr_state() {}
    unsigned qhead() const { return m_qhead; }
    virtual unsigned qtail() const = 0;
    virtual dependent_expr const& operator[](unsigned i) = 0;
    virtual void update(unsigned i, dependent_expr const& j) = 0;
    virtual void add(dependent_expr const& j) = 0;
    virtual bool inconsistent() = 0;
    virtual model_reconstruction_trail& model_trail() = 0;
    virtual void flatten_suffix() {}
    virtual bool updated() = 0;
    virtual void reset_updated() = 0;

    trail_stack    m_trail;
    void push() {
        m_trail.push_scope(); 
        m_trail.push(value_trail(m_qhead)); 
        m_trail.push(thaw(*this));
    }
    void pop(unsigned n) { m_trail.pop_scope(n); }
    
    void advance_qhead() { freeze_prefix(); m_suffix_frozen = false; m_has_quantifiers = l_undef;  m_qhead = qtail(); }
    unsigned num_exprs();

    /**
    * Freeze internal functions
    */
    void freeze(expr* term);
    void freeze(expr_ref_vector const& terms) { for (expr* t : terms) freeze(t); }
    bool frozen(func_decl* f) const { return m_frozen.is_marked(f); }    
    bool frozen(expr* f) const { return is_app(f) && m_frozen.is_marked(to_app(f)->get_decl()); }
    void freeze_suffix();

    virtual std::ostream& display(std::ostream& out) const { return out; }

    bool has_quantifiers();
};

class default_dependent_expr_state : public dependent_expr_state {
public:
    default_dependent_expr_state(ast_manager& m): dependent_expr_state(m) {}
    unsigned qtail() const override { return 0; }
    dependent_expr const& operator[](unsigned i) override { throw default_exception("unexpected access"); }
    void update(unsigned i, dependent_expr const& j) override { throw default_exception("unexpected update"); }
    void add(dependent_expr const& j) override { throw default_exception("unexpected addition"); }
    bool inconsistent() override { return false; }
    model_reconstruction_trail& model_trail() override { throw default_exception("unexpected access to model reconstruction"); }
    bool updated() override { return false; }
    void reset_updated() override {}

};

inline std::ostream& operator<<(std::ostream& out, dependent_expr_state& st) {
    return st.display(out);
}

/**
   Shared interface of simplifiers. 
 */
class dependent_expr_simplifier {
protected:
    ast_manager& m;
    dependent_expr_state& m_fmls;
    trail_stack& m_trail;

    unsigned num_scopes() const { return m_trail.get_num_scopes(); }

    unsigned qhead() const { return m_fmls.qhead(); }
    unsigned qtail() const { return m_fmls.qtail(); }
    struct iterator {
        dependent_expr_simplifier& s;
        unsigned m_index, m_end;
        iterator(dependent_expr_simplifier& s, unsigned i, unsigned end) : s(s), m_index(i), m_end(end) {}
        bool operator!=(iterator const& other) const { return m_index != other.m_index; }
        iterator& operator++() { if (!s.m.inc() || s.m_fmls.inconsistent() || m_index >= s.qtail()) m_index = m_end; else ++m_index; return *this; }
        unsigned operator*() const { return m_index; }
    };

    struct index_set {
        dependent_expr_simplifier& s;
        iterator begin() { return iterator(s, s.qhead(), s.qtail()); }
        iterator end() { return iterator(s, s.qtail(), s.qtail()); }
        index_set(dependent_expr_simplifier& s) : s(s) {}
    };

    index_set indices() { return index_set(*this); }

    proof* mp(proof* a, proof* b) { return (a && b) ? m.mk_modus_ponens(a, b) : nullptr;  }
    proof* tr(proof* a, proof* b) { return m.mk_transitivity(a, b); }
public:
    dependent_expr_simplifier(ast_manager& m, dependent_expr_state& s) : m(m), m_fmls(s), m_trail(s.m_trail) {}
    virtual ~dependent_expr_simplifier() {}
    virtual char const* name() const = 0;
    virtual void push() { }
    virtual void pop(unsigned n) { }
    virtual void reduce() = 0;
    virtual void collect_statistics(statistics& st) const {}
    virtual void reset_statistics() {}
    virtual void updt_params(params_ref const& p) {}
    virtual void collect_param_descrs(param_descrs& r) {}
    virtual bool supports_proofs() const { return false; }
    ast_manager& get_manager() { return m; }
    dependent_expr_state& get_fmls() { return m_fmls; }
};

typedef std::function<dependent_expr_simplifier*(ast_manager&, const params_ref&, dependent_expr_state& s)> simplifier_factory;
