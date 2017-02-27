/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    str_rewriter.h

Abstract:

    AST rewriting rules for string terms.

Author:

    Murphy Berzish

Notes:

--*/

#if 0

#include"str_decl_plugin.h"
#include"arith_decl_plugin.h"
#include"rewriter_types.h"
#include"params.h"
#include<set>
#include<map>

class str_rewriter {
    str_util m_strutil;
    arith_util m_autil;

public:
    str_rewriter(ast_manager & m, params_ref const & p = params_ref()) :
        m_strutil(m), m_autil(m) {
    }

    ast_manager & m() const { return m_strutil.get_manager(); }
    family_id get_fid() const { return m_strutil.get_family_id(); }

    void updt_params(params_ref const & p) {}
    static void get_param_descrs(param_descrs & r) {}

    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_eq_core(expr * lhs, expr * rhs, expr_ref & result);

    br_status mk_str_Concat(expr * arg0, expr * arg1, expr_ref & result);
    br_status mk_str_Length(expr * arg0, expr_ref & result);
    br_status mk_str_CharAt(expr * arg0, expr * arg1, expr_ref & result);
    br_status mk_str_StartsWith(expr * haystack, expr * needle, expr_ref & result);
    br_status mk_str_EndsWith(expr * haystack, expr * needle, expr_ref & result);
    br_status mk_str_Contains(expr * haystack, expr * needle, expr_ref & result);
    br_status mk_str_Indexof(expr * haystack, expr * needle, expr_ref & result);
    br_status mk_str_Indexof2(expr * arg0, expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_str_LastIndexof(expr * haystack, expr * needle, expr_ref & result);
    br_status mk_str_Replace(expr * base, expr * source, expr * target, expr_ref & result);
    br_status mk_str_Substr(expr * base, expr * start, expr * len, expr_ref & result);
    br_status mk_str_prefixof(expr * pre, expr * full, expr_ref & result);
    br_status mk_str_suffixof(expr * post, expr * full, expr_ref & result);
    br_status mk_str_to_int(expr * arg0, expr_ref & result);
    br_status mk_str_from_int(expr * arg0, expr_ref & result);

    br_status mk_re_Str2Reg(expr * str, expr_ref & result);
    br_status mk_re_RegexIn(expr * str, expr * re, expr_ref & result);
    br_status mk_re_RegexPlus(expr * re, expr_ref & result);
    br_status mk_re_RegexStar(expr * re, expr_ref & result);
    br_status mk_re_RegexConcat(expr * r0, expr * r1, expr_ref & result);
    br_status mk_re_RegexCharRange(expr * start, expr * end, expr_ref & result);

    bool reduce_eq(expr * l, expr * r, expr_ref_vector & lhs, expr_ref_vector & rhs, bool & change);
    bool reduce_eq(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_vector& lhs, expr_ref_vector& rhs, bool& change);

};

class nfa {
protected:
    bool m_valid;
    unsigned m_next_id;

    unsigned next_id() {
        unsigned retval = m_next_id;
        ++m_next_id;
        return retval;
    }

    unsigned m_start_state;
    unsigned m_end_state;

    std::map<unsigned, std::map<char, unsigned> > transition_map;
    std::map<unsigned, std::set<unsigned> > epsilon_map;

    void make_transition(unsigned start, char symbol, unsigned end) {
        transition_map[start][symbol] = end;
    }

    void make_epsilon_move(unsigned start, unsigned end) {
        epsilon_map[start].insert(end);
    }

    // Convert a regular expression to an e-NFA using Thompson's construction
    void convert_re(expr * e, unsigned & start, unsigned & end, str_util & m_strutil);

public:
    nfa(str_util & m_strutil, expr * e)
: m_valid(true), m_next_id(0), m_start_state(0), m_end_state(0) {
        convert_re(e, m_start_state, m_end_state, m_strutil);
    }

    nfa() : m_valid(false), m_next_id(0), m_start_state(0), m_end_state(0) {}

    bool is_valid() const {
        return m_valid;
    }

    void epsilon_closure(unsigned start, std::set<unsigned> & closure);

    bool matches(std::string input);
};

#endif /* disable */
