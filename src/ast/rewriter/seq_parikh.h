/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_parikh.h

Abstract:

    Parikh abstraction for word equations.

    An observer (k, n) maps a word w to the multiset of pairs (factor, start position mod n)
    over the factors of w of length k.  Since w1 = w2 implies obs(w1) = obs(w2) for every
    observer, an unsatisfiable observation system refutes the equation.  The observer with
    k = n = 1 is the Parikh image; larger k and n refine it.

    Each variable X gets a profile of integer counters, one per factor and residue, tied to
    len(X) by window marginals and to the neighbouring level by de-Bruijn flow.  A side of
    the equation is traversed block by block, rotating each block's counters by the running
    position clock and adding the factors that straddle block boundaries.  Empty blocks are
    handled exactly: a boundary factor connects a block to the next block that is non-empty.

    The abstraction only refutes.  Nothing is claimed when the observation system is
    satisfiable - the abstraction sees factor frequencies, not their order, so it cannot
    for instance refute a X X Y = X b X X for any k and n.

    k is capped at 2: a longer factor can span three or more blocks, which the boundary
    encoding does not cover.

    Counters are shared between equations, so an index has to mean the same thing
    everywhere.  The projected alphabet therefore only grows, and both its size and the
    observer's modulus are part of the identity of the symbols indexed by them.

Author:

    Clemens Eisenhofer 2026

--*/
#pragma once

#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "util/obj_hashtable.h"
#include "util/uint_set.h"

namespace seq {

class parikh {
public:
    struct config {
        unsigned m_k = 2;          // maximal factor length, 0 disables the abstraction
        unsigned m_n = 2;          // maximal position modulus
        unsigned m_max_chars = 6;  // how many distinct characters are kept apart
        unsigned m_max_counters = 5000;
    };

private:
    // one element of a side of the equation
    struct block {
        expr*    m_e = nullptr;
        unsigned m_char = 0;        // alphabet index, only if m_is_char
        bool     m_is_char = false; // a unit over a concrete character
        bool     m_unit = false;    // a unit, hence of length exactly one
    };

    typedef std::pair<unsigned, unsigned> block_pair;

    ast_manager&      m;
    seq_util          m_util;
    arith_util        m_autil;
    config            m_config;

    obj_hashtable<expr> m_defined;
    expr_ref_vector     m_pinned;

    unsigned            m_p = 0;   // size of the projected alphabet
    unsigned            m_mod = 1; // modulus of the observer being built
    indexed_uint_set    m_chars;   // projected characters, index m_chars.size() is the rest

    expr_ref mk_sk(char const* name, std::initializer_list<expr*> args, sort* range);
    expr_ref num(int i);
    expr_ref sum(expr_ref_vector const& args);
    expr_ref conj(expr_ref_vector const& args);
    void     push_impl(expr_ref_vector& defs, expr* cond, expr* e);
    bool     fresh(expr* key);
    rational num_grams(unsigned level) const;

    unsigned char_index(unsigned ch) const;
    bool has_char(expr_ref_vector const& side) const;
    void collect_chars(expr_ref_vector const& side);
    void collect_blocks(expr_ref_vector const& side, vector<block>& blocks);
    static void adjacent(vector<block> const& blocks, svector<block_pair>& out);

    expr_ref len(block const& b);
    expr_ref is_empty(block const& b);
    expr_ref first(block const& b, unsigned c);
    expr_ref last(block const& b, unsigned c);
    expr_ref count(block const& b, unsigned level, unsigned gram, unsigned r);
    expr_ref window(block const& b, unsigned level, expr_ref_vector& defs);
    expr_ref indicator(expr* cond, expr_ref_vector& defs);
    expr_ref clock(expr* prefix_len, expr_ref_vector& defs);
    expr_ref clock_is(expr* clk, unsigned v);

    void define_block(block const& b, expr_ref_vector& defs);
    void define_letters(block const& b, expr_ref_vector& defs);
    void define_level(block const& b, unsigned level, expr_ref_vector& defs);
    void define_flow(block const& b, expr_ref_vector& defs);
    void totals(vector<block> const& blocks, unsigned level, expr_ref_vector& out, expr_ref_vector& defs);
    void add_observer(vector<block> const& l, vector<block> const& r, unsigned mod,
                      expr_ref_vector& defs, expr_ref_vector& eqs);
    bool over_budget(vector<block> const& l, vector<block> const& r, unsigned_vector const& moduli);

public:
    parikh(ast_manager& m, config const& c);

    void updt_config(config const& c);

    // Encode l = r.  `defs` receives the profile definitions, which constrain fresh symbols
    // only and are satisfiable on their own.  `eqs` receives the observation equalities,
    // which hold whenever l = r does.  Returns false if the equation is out of scope.
    bool operator()(expr_ref_vector const& l, expr_ref_vector const& r,
                    expr_ref_vector& defs, expr_ref_vector& eqs);
};

}
