/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_decl_plugin.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2011-14-11

Revision History:

--*/
#ifndef SEQ_DECL_PLUGIN_H_
#define SEQ_DECL_PLUGIN_H_

#include "ast.h"


enum seq_sort_kind {
    SEQ_SORT,
    RE_SORT,
    STRING_SORT,
    CHAR_SORT
};

enum seq_op_kind {
    OP_SEQ_UNIT,
    OP_SEQ_EMPTY,
    OP_SEQ_CONCAT,
    OP_SEQ_PREFIX_OF,
    OP_SEQ_SUFFIX_OF,
    OP_SEQ_SUBSEQ_OF,
    OP_SEQ_EXTRACT,
    OP_SEQ_NTH,
    OP_SEQ_LENGTH,

    OP_RE_PLUS,
    OP_RE_STAR,
    OP_RE_OPTION,
    OP_RE_RANGE,
    OP_RE_CONCAT,
    OP_RE_UNION,
    OP_RE_INTERSECT,
    OP_RE_LOOP,
    OP_RE_EMPTY_SET,
    OP_RE_FULL_SET,
    OP_RE_EMPTY_SEQ,
    OP_RE_OF_SEQ,
    OP_RE_OF_PRED,
    OP_RE_MEMBER,


    // string specific operators.
    OP_STRING_CONST,
    _OP_STRING_CONCAT, 
    OP_STRING_LENGTH, 
    OP_STRING_SUBSTR, 
    OP_STRING_STRCTN, 
    OP_STRING_CHARAT, 
    OP_STRING_STRIDOF, 
    OP_STRING_STRREPL, 
    OP_STRING_PREFIX, 
    OP_STRING_SUFFIX, 
    OP_STRING_ITOS, 
    OP_STRING_STOI, 
    OP_STRING_IN_REGEXP, 
    OP_STRING_TO_REGEXP, 
    OP_REGEXP_LOOP, 
    
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
    bool             m_init;
    symbol           m_stringc_sym;
    sort*            m_string;
    sort*            m_char;

    void match(psig& sig, unsigned dsz, sort* const* dom, sort* range, sort_ref& rng);

    void match_left_assoc(psig& sig, unsigned dsz, sort* const* dom, sort* range, sort_ref& rng);

    bool match(ptr_vector<sort>& binding, sort* s, sort* sP);

    sort* apply_binding(ptr_vector<sort> const& binding, sort* s);

    bool is_sort_param(sort* s, unsigned& idx);

    void init();

    virtual void set_manager(ast_manager * m, family_id id);

public:
    seq_decl_plugin();

    virtual ~seq_decl_plugin() {}
    virtual void finalize();
   
    virtual decl_plugin * mk_fresh() { return alloc(seq_decl_plugin); }
    
    virtual sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters);
    
    virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                     unsigned arity, sort * const * domain, sort * range);
    
    virtual void get_op_names(svector<builtin_name> & op_names, symbol const & logic);
    
    virtual void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic);
    
    virtual bool is_value(app * e) const;

    virtual bool is_unique_value(app * e) const { return is_value(e); }

    bool is_char(ast* a) const { return a == m_char; }

    app* mk_string(symbol const& s);  
};

class seq_util {
    ast_manager& m;
    seq_decl_plugin& seq;
    family_id m_fid;
public:

    ast_manager& get_manager() const { return m; }

    bool is_string(sort* s) const { return is_seq(s) && seq.is_char(s->get_parameter(0).get_ast()); }
    bool is_seq(sort* s) const { return is_sort_of(s, m_fid, SEQ_SORT); }

    class str {
        seq_util&    u;
        ast_manager& m;
        family_id    m_fid;
    public:
        str(seq_util& u):u(u), m(u.m), m_fid(u.m_fid) {}

        app* mk_string(symbol const& s);
        app* mk_string(char const* s) { return mk_string(symbol(s)); }
        app* mk_string(std::string const& s) { return mk_string(symbol(s.c_str())); }
        app* mk_concat(expr* a, expr* b) { expr* es[2] = { a, b }; return m.mk_app(m_fid, OP_SEQ_CONCAT, 2, es); }
        app* mk_length(expr* a) { return m.mk_app(m_fid, OP_STRING_LENGTH, 1, &a); }
        app* mk_substr(expr* a, expr* b, expr* c) { expr* es[3] = { a, b, c }; return m.mk_app(m_fid, OP_STRING_SUBSTR, 3, es); }
        app* mk_strctn(expr* a, expr* b) { expr* es[2] = { a, b }; return m.mk_app(m_fid, OP_STRING_STRCTN, 2, es); }

        bool is_const(expr const * n) const { return is_app_of(n, m_fid, OP_STRING_CONST); }
        
        bool is_const(expr const* n, std::string& s) const {
            return is_const(n) && (s = to_app(n)->get_decl()->get_parameter(0).get_symbol().str(), true);
        }
        bool is_const(expr const* n, symbol& s) const {
            return is_const(n) && (s = to_app(n)->get_decl()->get_parameter(0).get_symbol(), true);
        }
        
        bool is_concat(expr const* n)  const { return is_app_of(n, m_fid, OP_SEQ_CONCAT); }
        bool is_length(expr const* n)  const { return is_app_of(n, m_fid, OP_STRING_LENGTH); }
        bool is_substr(expr const* n)  const { return is_app_of(n, m_fid, OP_STRING_SUBSTR); }
        bool is_strctn(expr const* n)  const { return is_app_of(n, m_fid, OP_STRING_STRCTN); }
        bool is_charat(expr const* n)  const { return is_app_of(n, m_fid, OP_STRING_CHARAT); }
        bool is_stridof(expr const* n) const { return is_app_of(n, m_fid, OP_STRING_STRIDOF); }
        bool is_repl(expr const* n)    const { return is_app_of(n, m_fid, OP_STRING_STRREPL); }
        bool is_prefix(expr const* n)  const { return is_app_of(n, m_fid, OP_STRING_PREFIX); }
        bool is_suffix(expr const* n)  const { return is_app_of(n, m_fid, OP_STRING_SUFFIX); }
        bool is_itos(expr const* n)    const { return is_app_of(n, m_fid, OP_STRING_ITOS); }
        bool is_stoi(expr const* n)    const { return is_app_of(n, m_fid, OP_STRING_STOI); }
        bool is_in_regexp(expr const* n) const { return is_app_of(n, m_fid, OP_STRING_IN_REGEXP); }

        
        MATCH_BINARY(is_concat);
        MATCH_UNARY(is_length);
        MATCH_TERNARY(is_substr);
        MATCH_BINARY(is_strctn);
        MATCH_BINARY(is_charat);
        MATCH_BINARY(is_stridof);
        MATCH_BINARY(is_repl);
        MATCH_BINARY(is_prefix);
        MATCH_BINARY(is_suffix);
        MATCH_UNARY(is_itos);
        MATCH_UNARY(is_stoi);
        MATCH_BINARY(is_in_regexp);        

        void get_concat(expr* e, ptr_vector<expr>& es) const;
    };

    class re {
        seq_util&    u;
        ast_manager& m;
        family_id    m_fid;
    public:
        re(seq_util& u):u(u), m(u.m), m_fid(u.m_fid) {}

        bool is_to_regexp(expr const* n)    const { return is_app_of(n, m_fid, OP_STRING_TO_REGEXP); }
        bool is_concat(expr const* n)    const { return is_app_of(n, m_fid, OP_RE_CONCAT); }
        bool is_union(expr const* n)    const { return is_app_of(n, m_fid, OP_RE_UNION); }
        bool is_inter(expr const* n)    const { return is_app_of(n, m_fid, OP_RE_INTERSECT); }
        bool is_star(expr const* n)    const { return is_app_of(n, m_fid, OP_RE_STAR); }
        bool is_plus(expr const* n)    const { return is_app_of(n, m_fid, OP_RE_PLUS); }
        bool is_opt(expr const* n)    const { return is_app_of(n, m_fid, OP_RE_OPTION); }
        bool is_range(expr const* n)    const { return is_app_of(n, m_fid, OP_RE_RANGE); }
        bool is_loop(expr const* n)    const { return is_app_of(n, m_fid, OP_REGEXP_LOOP); }
       
        MATCH_UNARY(is_to_regexp);
        MATCH_BINARY(is_concat);
        MATCH_BINARY(is_union);
        MATCH_BINARY(is_inter);
        MATCH_UNARY(is_star);
        MATCH_UNARY(is_plus);
        MATCH_UNARY(is_opt);
        
    };
    str str;
    re  re;

    seq_util(ast_manager& m): 
        m(m), 
        seq(*static_cast<seq_decl_plugin*>(m.get_plugin(m.mk_family_id("seq")))),
        m_fid(seq.get_family_id()),
        str(*this),
        re(*this) {        
    }

    ~seq_util() {}

    family_id get_family_id() const { return m_fid; }
    
};

#endif /* SEQ_DECL_PLUGIN_H_ */

