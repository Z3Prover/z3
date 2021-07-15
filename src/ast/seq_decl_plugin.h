/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_decl_plugin.h

Abstract:

    decl_plugin for the theory of sequences

Author:

    Nikolaj Bjorner (nbjorner) 2011-11-14

Revision History:

    Updated to string sequences 2015-12-5

    Add SMTLIB 2.6 support 2020-5-17

--*/
#pragma once

#include "ast/ast.h"
#include "ast/char_decl_plugin.h"
#include "util/lbool.h"
#include "util/zstring.h"

enum seq_sort_kind {
    SEQ_SORT,
    RE_SORT,
    _STRING_SORT,  
    _REGLAN_SORT
};

enum seq_op_kind {
    OP_SEQ_UNIT,
    OP_SEQ_EMPTY,
    OP_SEQ_CONCAT,
    OP_SEQ_PREFIX,
    OP_SEQ_SUFFIX,
    OP_SEQ_CONTAINS,
    OP_SEQ_EXTRACT,
    OP_SEQ_REPLACE,
    OP_SEQ_AT,
    OP_SEQ_NTH,         // NTH function exposed over API. Rewritten to NTH(s,i) := if (0 <= i < len(s)) then NTH_I(s,i) else NTH_U(s,i)
    OP_SEQ_NTH_I,       // Interpreted variant of Nth for indices within defined domain.
    OP_SEQ_NTH_U,       // Uninterpreted variant of Nth for indices outside of uniquely defined domain.
    OP_SEQ_LENGTH,
    OP_SEQ_INDEX,
    OP_SEQ_LAST_INDEX,
    OP_SEQ_TO_RE,
    OP_SEQ_IN_RE,
    OP_SEQ_REPLACE_RE_ALL, // Seq -> RegEx -> Seq -> Seq
    OP_SEQ_REPLACE_RE,     // Seq -> RegEx -> Seq -> Seq
    OP_SEQ_REPLACE_ALL,    // Seq -> Seq -> Seq -> Seq

    OP_RE_PLUS,
    OP_RE_STAR,
    OP_RE_OPTION,
    OP_RE_RANGE,
    OP_RE_CONCAT,
    OP_RE_UNION,
    OP_RE_DIFF,
    OP_RE_INTERSECT,
    OP_RE_LOOP,
    OP_RE_POWER,
    OP_RE_COMPLEMENT,
    OP_RE_EMPTY_SET,
    OP_RE_FULL_SEQ_SET,
    OP_RE_FULL_CHAR_SET,
    OP_RE_OF_PRED,
    OP_RE_REVERSE,
    OP_RE_DERIVATIVE, // Char -> RegEx -> RegEx


    // string specific operators.
    OP_STRING_CONST,
    OP_STRING_ITOS,
    OP_STRING_STOI,
    OP_STRING_UBVTOS,
    OP_STRING_LT,
    OP_STRING_LE,
    OP_STRING_IS_DIGIT,
    OP_STRING_TO_CODE,
    OP_STRING_FROM_CODE,

    // internal only operators. Converted to SEQ variants.
    _OP_STRING_FROM_CHAR,
    _OP_STRING_STRREPL,
    _OP_STRING_CONCAT,
    _OP_STRING_LENGTH,
    _OP_STRING_STRCTN,
    _OP_STRING_PREFIX,
    _OP_STRING_SUFFIX,
    _OP_STRING_IN_REGEXP,
    _OP_STRING_TO_REGEXP,
    _OP_STRING_CHARAT,
    _OP_STRING_SUBSTR,
    _OP_STRING_STRIDOF,
    _OP_REGEXP_EMPTY,
    _OP_REGEXP_FULL_CHAR,
    _OP_RE_IS_NULLABLE,
    _OP_RE_ANTIMOROV_UNION, // Lifted union for antimorov-style derivatives
    _OP_SEQ_SKOLEM,
    LAST_SEQ_OP
};


class seq_decl_plugin : public decl_plugin {
    struct psig {
        symbol          m_name;
        unsigned        m_num_params;
        sort_ref_vector m_dom;
        sort_ref        m_range;
        psig(ast_manager& m, char const* name, unsigned n, unsigned dsz, sort* const* dom, sort* rng):
            m_name(name),
            m_num_params(n),
            m_dom(m),
            m_range(rng, m)
        {
            m_dom.append(dsz, dom);
        }
    };

    ptr_vector<psig> m_sigs;
    ptr_vector<sort> m_binding;
    bool             m_init;
    symbol           m_stringc_sym;
    sort*            m_string;
    sort*            m_char;
    sort*            m_reglan;
    bool             m_has_re;
    bool             m_has_seq;
    char_decl_plugin* m_char_plugin { nullptr };

    void match(psig& sig, unsigned dsz, sort* const* dom, sort* range, sort_ref& rng);

    void match_assoc(psig& sig, unsigned dsz, sort* const* dom, sort* range, sort_ref& rng);

    bool match(ptr_vector<sort>& binding, sort* s, sort* sP);

    sort* apply_binding(ptr_vector<sort> const& binding, sort* s);

    bool is_sort_param(sort* s, unsigned& idx);

    func_decl* mk_seq_fun(decl_kind k, unsigned arity, sort* const* domain, sort* range, decl_kind k_string);
    func_decl* mk_str_fun(decl_kind k, unsigned arity, sort* const* domain, sort* range, decl_kind k_seq);
    func_decl* mk_assoc_fun(decl_kind k, unsigned arity, sort* const* domain, sort* range, decl_kind k_string, decl_kind k_seq);
    func_decl* mk_left_assoc_fun(decl_kind k, unsigned arity, sort* const* domain, sort* range, decl_kind k_string, decl_kind k_seq);
    func_decl* mk_assoc_fun(decl_kind k, unsigned arity, sort* const* domain, sort* range, decl_kind k_string, decl_kind k_seq, bool is_right);
    func_decl* mk_ubv2s(unsigned arity, sort* const* domain);


    void init();

    void set_manager(ast_manager * m, family_id id) override;

    sort* mk_reglan();

public:
    seq_decl_plugin();

    void finalize() override;

    bool unicode() const { return get_char_plugin().unicode(); }

    decl_plugin * mk_fresh() override { return alloc(seq_decl_plugin); }

    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override;

    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                             unsigned arity, sort * const * domain, sort * range) override;

    void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;

    void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) override;

    bool is_value(app * e) const override;

    bool is_unique_value(app * e) const override;

    bool are_equal(app* a, app* b) const override;

    bool are_distinct(app* a, app* b) const override;

    expr * get_some_value(sort * s) override;

    bool is_char(sort* a) const { return a == m_char; }

    unsigned max_char() const { return get_char_plugin().max_char(); }
    unsigned num_bits() const { return get_char_plugin().num_bits(); }

    app* mk_string(zstring const& s);
    app* mk_char(unsigned ch);

    bool has_re() const { return m_has_re; }
    bool has_seq() const { return m_has_seq; }

    bool is_considered_uninterpreted(func_decl * f) override;

    sort* char_sort() const { return m_char; }
    sort* string_sort() const { return m_string; }

    char_decl_plugin& get_char_plugin() const { return *m_char_plugin; }

};

class seq_util {
    ast_manager& m;
    seq_decl_plugin& seq;
    char_decl_plugin& ch;
    family_id m_fid;

public:

    unsigned max_plus(unsigned x, unsigned y) const;
    unsigned max_mul(unsigned x, unsigned y) const;

    ast_manager& get_manager() const { return m; }

    sort* mk_char_sort() const { return seq.char_sort(); }
    sort* mk_string_sort() const { return seq.string_sort(); }

    bool is_char(sort* s) const { return seq.is_char(s); }
    bool is_char(expr* e) const { return is_char(e->get_sort()); }
    bool is_string(sort* s) const { return is_seq(s) && seq.is_char(to_sort(s->get_parameter(0).get_ast())); }
    bool is_seq(sort* s) const { return is_sort_of(s, m_fid, SEQ_SORT); }
    bool is_re(sort* s) const { return is_sort_of(s, m_fid, RE_SORT); }
    bool is_re(sort* s, sort*& seq) const { return is_sort_of(s, m_fid, RE_SORT)  && (seq = to_sort(s->get_parameter(0).get_ast()), true); }
    bool is_seq(expr* e) const  { return is_seq(e->get_sort()); }
    bool is_seq(sort* s, sort*& seq) const { return is_seq(s) && (seq = to_sort(s->get_parameter(0).get_ast()), true); }
    bool is_re(expr* e) const { return is_re(e->get_sort()); }
    bool is_re(expr* e, sort*& seq) const { return is_re(e->get_sort(), seq); }
    bool is_const_char(expr* e, unsigned& c) const;
    bool is_const_char(expr* e) const { unsigned c; return is_const_char(e, c); }
    bool is_char_le(expr const* e) const;
    bool is_char_is_digit(expr const* e, expr*& d) const { return ch.is_is_digit(e, d); }
    bool is_char_is_digit(expr const* e) const { return ch.is_is_digit(e); }
    bool is_char2int(expr const* e) const;
    app* mk_char_bit(expr* e, unsigned i);
    app* mk_char(unsigned ch) const;
    app* mk_char_is_digit(expr* e) { return ch.mk_is_digit(e); }
    app* mk_le(expr* ch1, expr* ch2) const;
    app* mk_lt(expr* ch1, expr* ch2) const;    
    app* mk_char2int(expr* e) { return ch.mk_to_int(e); }
    unsigned max_char() const { return seq.max_char(); }
    unsigned num_bits() const { return seq.num_bits(); }

    app* mk_skolem(symbol const& name, unsigned n, expr* const* args, sort* range);
    bool is_skolem(expr const* e) const { return is_app_of(e, m_fid, _OP_SEQ_SKOLEM); }

    MATCH_BINARY(is_char_le);
    MATCH_UNARY(is_char2int);

    bool has_re() const { return seq.has_re(); }
    bool has_seq() const { return seq.has_seq(); }

    class str {
        seq_util&    u;
        ast_manager& m;
        family_id    m_fid;


    public:
        str(seq_util& u): u(u), m(u.m), m_fid(u.m_fid) {}

        sort* mk_seq(sort* s) const { parameter param(s); return m.mk_sort(m_fid, SEQ_SORT, 1, &param); }
        sort* mk_string_sort() const { return m.mk_sort(m_fid, _STRING_SORT, 0, nullptr); }
        app* mk_empty(sort* s) const { return m.mk_const(m.mk_func_decl(m_fid, OP_SEQ_EMPTY, 0, nullptr, 0, (expr*const*)nullptr, s)); }
        app* mk_string(zstring const& s) const;
        app* mk_char(unsigned ch) const;
        app* mk_concat(expr* a, expr* b) const { expr* es[2] = { a, b }; return m.mk_app(m_fid, OP_SEQ_CONCAT, 2, es); }
        app* mk_concat(expr* a, expr* b, expr* c) const { return mk_concat(a, mk_concat(b, c)); }
        expr* mk_concat(unsigned n, expr* const* es, sort* s) const { 
            if (n == 0) return mk_empty(s);
            if (n == 1) return es[0]; 
            return m.mk_app(m_fid, OP_SEQ_CONCAT, n, es); }
        expr* mk_concat(expr_ref_vector const& es, sort* s) const { return mk_concat(es.size(), es.data(), s); }
        app* mk_length(expr* a) const { return m.mk_app(m_fid, OP_SEQ_LENGTH, 1, &a); }
        app* mk_at(expr* s, expr* i) const { expr* es[2] = { s, i }; return m.mk_app(m_fid, OP_SEQ_AT, 2, es); }
        app* mk_nth(expr* s, expr* i) const { expr* es[2] = { s, i }; return m.mk_app(m_fid, OP_SEQ_NTH, 2, es); }
        app* mk_nth_i(expr* s, expr* i) const { expr* es[2] = { s, i }; return m.mk_app(m_fid, OP_SEQ_NTH_I, 2, es); }
        app* mk_nth_i(expr* s, unsigned i) const;

        app* mk_substr(expr* a, expr* b, expr* c) const { expr* es[3] = { a, b, c }; return m.mk_app(m_fid, OP_SEQ_EXTRACT, 3, es); }
        app* mk_contains(expr* a, expr* b) const { expr* es[2] = { a, b }; return m.mk_app(m_fid, OP_SEQ_CONTAINS, 2, es); }
        app* mk_prefix(expr* a, expr* b) const { expr* es[2] = { a, b }; return m.mk_app(m_fid, OP_SEQ_PREFIX, 2, es); }
        app* mk_suffix(expr* a, expr* b) const { expr* es[2] = { a, b }; return m.mk_app(m_fid, OP_SEQ_SUFFIX, 2, es); }
        app* mk_index(expr* a, expr* b, expr* i) const { expr* es[3] = { a, b, i}; return m.mk_app(m_fid, OP_SEQ_INDEX, 3, es); }
        app* mk_last_index(expr* a, expr* b) const { expr* es[2] = { a, b}; return m.mk_app(m_fid, OP_SEQ_LAST_INDEX, 2, es); }
        app* mk_replace(expr* a, expr* b, expr* c) const { expr* es[3] = { a, b, c}; return m.mk_app(m_fid, OP_SEQ_REPLACE, 3, es); }
        app* mk_unit(expr* u) const { return m.mk_app(m_fid, OP_SEQ_UNIT, 1, &u); }
        app* mk_char(zstring const& s, unsigned idx) const;
        app* mk_char_bit(expr* e, unsigned i);
        app* mk_itos(expr* i) const { return m.mk_app(m_fid, OP_STRING_ITOS, 1, &i); }
        app* mk_stoi(expr* s) const { return m.mk_app(m_fid, OP_STRING_STOI, 1, &s); }
        app* mk_ubv2s(expr* b) const { return m.mk_app(m_fid, OP_STRING_UBVTOS, 1, &b); }
        app* mk_is_empty(expr* s) const;
        app* mk_lex_lt(expr* a, expr* b) const { expr* es[2] = { a, b }; return m.mk_app(m_fid, OP_STRING_LT, 2, es); }
        app* mk_lex_le(expr* a, expr* b) const { expr* es[2] = { a, b }; return m.mk_app(m_fid, OP_STRING_LE, 2, es); }
        app* mk_to_code(expr* e) const { return m.mk_app(m_fid, OP_STRING_TO_CODE, 1, &e); }
        app* mk_from_code(expr* e) const { return m.mk_app(m_fid, OP_STRING_FROM_CODE, 1, &e); }
        app* mk_is_digit(expr* e) const { return m.mk_app(m_fid, OP_STRING_IS_DIGIT, 1, &e); }


        bool is_nth_i(func_decl const* f)       const { return is_decl_of(f, m_fid, OP_SEQ_NTH_I); }
        bool is_nth_u(func_decl const* f)       const { return is_decl_of(f, m_fid, OP_SEQ_NTH_U); }
        bool is_skolem(func_decl const* f)      const { return is_decl_of(f, m_fid, _OP_SEQ_SKOLEM); }

        bool is_string(expr const * n) const { return is_app_of(n, m_fid, OP_STRING_CONST); }
        bool is_string(func_decl const* f) const { return is_decl_of(f, m_fid, OP_STRING_CONST); }
        bool is_string(expr const* n, zstring& s) const;
        bool is_string(func_decl const* f, zstring& s) const;
        bool is_empty(expr const* n) const {
            zstring s;
            return is_app_of(n, m_fid, OP_SEQ_EMPTY) || (is_string(n, s) && s.empty());
        }
        bool is_concat(expr const* n)   const { return is_app_of(n, m_fid, OP_SEQ_CONCAT); }
        bool is_length(expr const* n)   const { return is_app_of(n, m_fid, OP_SEQ_LENGTH); }
        bool is_extract(expr const* n)  const { return is_app_of(n, m_fid, OP_SEQ_EXTRACT); }
        bool is_contains(expr const* n) const { return is_app_of(n, m_fid, OP_SEQ_CONTAINS); }
        bool is_at(expr const* n)       const { return is_app_of(n, m_fid, OP_SEQ_AT); }
        bool is_nth_i(expr const* n)       const { return is_app_of(n, m_fid, OP_SEQ_NTH_I); }
        bool is_nth_u(expr const* n)       const { return is_app_of(n, m_fid, OP_SEQ_NTH_U); }
        bool is_nth_i(expr const* n, expr*& s, unsigned& idx) const;
        bool is_index(expr const* n)    const { return is_app_of(n, m_fid, OP_SEQ_INDEX); }
        bool is_last_index(expr const* n)    const { return is_app_of(n, m_fid, OP_SEQ_LAST_INDEX); }
        bool is_replace(expr const* n)  const { return is_app_of(n, m_fid, OP_SEQ_REPLACE); }
        bool is_replace_re(expr const* n)  const { return is_app_of(n, m_fid, OP_SEQ_REPLACE_RE); }
        bool is_replace_re_all(expr const* n)  const { return is_app_of(n, m_fid, OP_SEQ_REPLACE_RE_ALL); }
        bool is_replace_all(expr const* n)  const { return is_app_of(n, m_fid, OP_SEQ_REPLACE_ALL); }
        bool is_prefix(expr const* n)   const { return is_app_of(n, m_fid, OP_SEQ_PREFIX); }
        bool is_suffix(expr const* n)   const { return is_app_of(n, m_fid, OP_SEQ_SUFFIX); }
        bool is_itos(expr const* n)     const { return is_app_of(n, m_fid, OP_STRING_ITOS); }
        bool is_stoi(expr const* n)     const { return is_app_of(n, m_fid, OP_STRING_STOI); }
        bool is_ubv2s(expr const* n)    const { return is_app_of(n, m_fid, OP_STRING_UBVTOS); }
        bool is_in_re(expr const* n)    const { return is_app_of(n, m_fid, OP_SEQ_IN_RE); }
        bool is_unit(expr const* n)     const { return is_app_of(n, m_fid, OP_SEQ_UNIT); }
        bool is_lt(expr const* n)       const { return is_app_of(n, m_fid, OP_STRING_LT); }
        bool is_le(expr const* n)       const { return is_app_of(n, m_fid, OP_STRING_LE); }
        bool is_is_digit(expr const* n) const { return is_app_of(n, m_fid, OP_STRING_IS_DIGIT); }
        bool is_from_code(expr const* n) const { return is_app_of(n, m_fid, OP_STRING_FROM_CODE); }
        bool is_to_code(expr const* n) const { return is_app_of(n, m_fid, OP_STRING_TO_CODE); }

        bool is_string_term(expr const * n) const {
            return u.is_string(n->get_sort());
        }

        bool is_non_string_sequence(expr const * n) const {
            sort * s = n->get_sort();
            return (u.is_seq(s) && !u.is_string(s));
        }

        MATCH_BINARY(is_concat);
        MATCH_UNARY(is_length);
        MATCH_TERNARY(is_extract);
        MATCH_BINARY(is_contains);
        MATCH_BINARY(is_at);
        MATCH_BINARY(is_nth_i);
        MATCH_BINARY(is_nth_u);
        MATCH_BINARY(is_index);
        MATCH_TERNARY(is_index);
        MATCH_BINARY(is_last_index);
        MATCH_TERNARY(is_replace);
        MATCH_TERNARY(is_replace_re);
        MATCH_TERNARY(is_replace_re_all);
        MATCH_TERNARY(is_replace_all);
        MATCH_BINARY(is_prefix);
        MATCH_BINARY(is_suffix);
        MATCH_BINARY(is_lt);
        MATCH_BINARY(is_le);
        MATCH_UNARY(is_itos);
        MATCH_UNARY(is_stoi);
        MATCH_UNARY(is_ubv2s);
        MATCH_UNARY(is_is_digit);
        MATCH_UNARY(is_from_code);
        MATCH_UNARY(is_to_code);
        MATCH_BINARY(is_in_re);
        MATCH_UNARY(is_unit);

        void get_concat(expr* e, expr_ref_vector& es) const;
        void get_concat_units(expr* e, expr_ref_vector& es) const;
        expr* get_leftmost_concat(expr* e) const { expr* e1, *e2; while (is_concat(e, e1, e2)) e = e1; return e; }
        expr* get_rightmost_concat(expr* e) const { expr* e1, *e2; while (is_concat(e, e1, e2)) e = e2; return e; }

        unsigned min_length(expr* s) const;
        unsigned max_length(expr* s) const;
    };

    class rex {
    public:
        struct info {
            /* Value is either undefined (known=l_undef) or defined and known (l_true) or defined but unknown (l_false)*/
            lbool known { l_undef };
            /* No complement, no intersection, no difference, and no if-then-else is used. Reverse is allowed. */
            bool classical { false };
            /* Boolean-reverse combination of classical regexes (using reverse, union, complement, intersection or difference). */
            bool standard { false };
            /* There are no uninterpreted symbols. */
            bool interpreted { false };
            /* No if-then-else is used. */
            bool nonbranching { false };
            /* Concatenations are right associative and if a loop body is nullable then the lower bound is zero. */
            bool normalized { false };
            /* All bounded loops have a body that is a singleton. */
            bool monadic { false };
            /* Positive Boolean combination of ranges or predicates or singleton sequences. */
            bool singleton { false };
            /* If l_true then empty word is accepted, if l_false then empty word is not accepted. */
            lbool nullable { l_undef };
            /* Lower bound  on the length of all accepted words. */
            unsigned min_length { 0 };
            /* Maximum nesting depth of Kleene stars. */
            unsigned star_height { 0 };

            /*
              Default constructor of invalid info.
            */
            info() {}

            /*
              Used for constructing either an invalid info that is only used to indicate uninitialzed entry, or valid but unknown info value.
            */
            info(lbool is_known) : known(is_known) {}

            /*
              General info constructor.
            */
            info(bool is_classical,
                bool is_standard,
                bool is_interpreted,
                bool is_nonbranching,
                bool is_normalized,
                bool is_monadic,
                bool is_singleton,
                lbool is_nullable,
                unsigned min_l,
                unsigned star_h) :
                known(l_true), classical(is_classical), standard(is_standard), interpreted(is_interpreted), nonbranching(is_nonbranching),
                normalized(is_normalized), monadic(is_monadic), singleton(is_singleton), nullable(is_nullable),
                min_length(min_l), star_height(star_h) {}

            /*
              Appends a string representation of the info into the stream.
            */
            std::ostream& display(std::ostream&) const;

            /*
              Returns a string representation of the info.
            */
            std::string str() const;

            bool is_valid() const { return known != l_undef; }

            bool is_known() const { return known == l_true; }

            info star() const;
            info plus() const;
            info opt() const;
            info complement() const;
            info concat(info const& rhs, bool lhs_is_concat) const;
            info disj(info const& rhs) const;
            info conj(info const& rhs) const; 
            info diff(info const& rhs) const;
            info orelse(info const& rhs) const;
            info loop(unsigned lower, unsigned upper) const;
        };
    private:
        seq_util&    u;
        ast_manager& m;
        family_id    m_fid;
        vector<info> mutable m_infos;
        expr_ref_vector mutable m_info_pinned;
        info invalid_info { info(l_undef) };
        info unknown_info { info(l_false) };

        bool has_valid_info(expr* r) const;
        info get_info_rec(expr* r) const;
        info mk_info_rec(app* r) const;
        info get_cached_info(expr* e) const;

    public:
        rex(seq_util& u): u(u), m(u.m), m_fid(u.m_fid), m_info_pinned(u.m) {}

        sort* mk_re(sort* seq) { parameter param(seq); return m.mk_sort(m_fid, RE_SORT, 1, &param); }
        sort* to_seq(sort* re);

        app* mk_to_re(expr* s) { return m.mk_app(m_fid, OP_SEQ_TO_RE, 1, &s); }
        app* mk_in_re(expr* s, expr* r) { return m.mk_app(m_fid, OP_SEQ_IN_RE, s, r); }
        app* mk_range(expr* s1, expr* s2) { return m.mk_app(m_fid, OP_RE_RANGE, s1, s2); }
        app* mk_concat(expr* r1, expr* r2) { return m.mk_app(m_fid, OP_RE_CONCAT, r1, r2); }
        app* mk_union(expr* r1, expr* r2) { return m.mk_app(m_fid, OP_RE_UNION, r1, r2); }
        app* mk_inter(expr* r1, expr* r2) { return m.mk_app(m_fid, OP_RE_INTERSECT, r1, r2); }
        app* mk_diff(expr* r1, expr* r2) { return m.mk_app(m_fid, OP_RE_DIFF, r1, r2); }
        app* mk_complement(expr* r) { return m.mk_app(m_fid, OP_RE_COMPLEMENT, r); }
        app* mk_star(expr* r) { return m.mk_app(m_fid, OP_RE_STAR, r); }
        app* mk_plus(expr* r) { return m.mk_app(m_fid, OP_RE_PLUS, r); }
        app* mk_opt(expr* r) { return m.mk_app(m_fid, OP_RE_OPTION, r); }
        app* mk_loop(expr* r, unsigned lo);
        app* mk_loop(expr* r, unsigned lo, unsigned hi);
        app* mk_loop(expr* r, expr* lo);
        app* mk_loop(expr* r, expr* lo, expr* hi);
        app* mk_full_char(sort* s);
        app* mk_full_seq(sort* s);
        app* mk_empty(sort* s);
        app* mk_of_pred(expr* p);
        app* mk_reverse(expr* r) { return m.mk_app(m_fid, OP_RE_REVERSE, r); }
        app* mk_derivative(expr* ele, expr* r) { return m.mk_app(m_fid, OP_RE_DERIVATIVE, ele, r); }
        app* mk_antimorov_union(expr* r1, expr* r2) { return m.mk_app(m_fid, _OP_RE_ANTIMOROV_UNION, r1, r2); }

        bool is_to_re(expr const* n)    const { return is_app_of(n, m_fid, OP_SEQ_TO_RE); }
        bool is_concat(expr const* n)    const { return is_app_of(n, m_fid, OP_RE_CONCAT); }
        bool is_union(expr const* n)    const { return is_app_of(n, m_fid, OP_RE_UNION); }
        bool is_intersection(expr const* n)    const { return is_app_of(n, m_fid, OP_RE_INTERSECT); }
        bool is_diff(expr const* n)    const { return is_app_of(n, m_fid, OP_RE_DIFF); }
        bool is_complement(expr const* n)    const { return is_app_of(n, m_fid, OP_RE_COMPLEMENT); }
        bool is_star(expr const* n)    const { return is_app_of(n, m_fid, OP_RE_STAR); }
        bool is_plus(expr const* n)    const { return is_app_of(n, m_fid, OP_RE_PLUS); }
        bool is_opt(expr const* n)    const { return is_app_of(n, m_fid, OP_RE_OPTION); }
        bool is_range(expr const* n)    const { return is_app_of(n, m_fid, OP_RE_RANGE); }
        bool is_loop(expr const* n)    const { return is_app_of(n, m_fid, OP_RE_LOOP); }
        bool is_empty(expr const* n)  const { return is_app_of(n, m_fid, OP_RE_EMPTY_SET); }
        bool is_full_char(expr const* n)  const { return is_app_of(n, m_fid, OP_RE_FULL_CHAR_SET); }
        bool is_full_seq(expr const* n)  const { return is_app_of(n, m_fid, OP_RE_FULL_SEQ_SET); }
        bool is_of_pred(expr const* n) const { return is_app_of(n, m_fid, OP_RE_OF_PRED); }
        bool is_reverse(expr const* n) const { return is_app_of(n, m_fid, OP_RE_REVERSE); }
        bool is_derivative(expr const* n) const { return is_app_of(n, m_fid, OP_RE_DERIVATIVE); }
        bool is_antimorov_union(expr const* n) const { return is_app_of(n, m_fid, _OP_RE_ANTIMOROV_UNION); }
        MATCH_UNARY(is_to_re);
        MATCH_BINARY(is_concat);
        MATCH_BINARY(is_union);
        MATCH_BINARY(is_intersection);
        MATCH_BINARY(is_diff);
        MATCH_BINARY(is_range);
        MATCH_UNARY(is_complement);
        MATCH_UNARY(is_star);
        MATCH_UNARY(is_plus);
        MATCH_UNARY(is_opt);
        MATCH_UNARY(is_of_pred);
        MATCH_UNARY(is_reverse);
        MATCH_BINARY(is_derivative);
        MATCH_BINARY(is_antimorov_union);
        bool is_loop(expr const* n, expr*& body, unsigned& lo, unsigned& hi) const;
        bool is_loop(expr const* n, expr*& body, unsigned& lo) const;
        bool is_loop(expr const* n, expr*& body, expr*& lo, expr*& hi) const;
        bool is_loop(expr const* n, expr*& body, expr*& lo) const;
        unsigned min_length(expr* r) const;
        unsigned max_length(expr* r) const;
        bool is_epsilon(expr* r) const;
        app* mk_epsilon(sort* seq_sort);
        info get_info(expr* r) const;
        std::string to_str(expr* r) const;

        class pp {
            seq_util::rex& re;
            expr* e;
            bool html_encode;
            bool can_skip_parenth(expr* r) const;
            std::ostream& seq_unit(std::ostream& out, expr* s) const;
            std::ostream& compact_helper_seq(std::ostream& out, expr* s) const;
            std::ostream& compact_helper_range(std::ostream& out, expr* s1, expr* s2) const;

        public:
            pp(seq_util::rex& r, expr* e, bool html = false) : re(r), e(e), html_encode(html) {}
            std::ostream& display(std::ostream&) const;
        };
    };
    str str;
    rex  re;

    seq_util(ast_manager& m):
        m(m),
        seq(*static_cast<seq_decl_plugin*>(m.get_plugin(m.mk_family_id("seq")))),
        ch(seq.get_char_plugin()),
        m_fid(seq.get_family_id()),
        str(*this),
        re(*this) {
    }

    family_id get_family_id() const { return m_fid; }
};

inline std::ostream& operator<<(std::ostream& out, seq_util::rex::pp const & p) { return p.display(out); }

inline std::ostream& operator<<(std::ostream& out, seq_util::rex::info const& p) { return p.display(out); }

