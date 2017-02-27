/*++
Module Name:

    str_decl_plugin.h

Abstract:

    <abstract>

Author:

    Murphy Berzish (mtrberzi) 2015-09-02.

Revision History:

--*/

#if 0

#ifndef _STR_DECL_PLUGIN_H_
#define _STR_DECL_PLUGIN_H_

#include"ast.h"
#include"arith_decl_plugin.h"
#include<map>

enum str_sort_kind {
   STRING_SORT,
   REGEX_SORT,
};

enum str_op_kind {
    OP_STR, /* string constants */
    // basic string operators
    OP_STRCAT,
    OP_STRLEN,
    // higher-level string functions -- these are reduced to basic operations
    OP_STR_CHARAT,
    OP_STR_STARTSWITH,
    OP_STR_ENDSWITH,
    OP_STR_CONTAINS,
    OP_STR_INDEXOF,
    OP_STR_INDEXOF2,
    OP_STR_LASTINDEXOF,
    OP_STR_SUBSTR,
    OP_STR_REPLACE,
    // SMT-LIB 2.5 standard operators -- these are rewritten to internal ones
    OP_STR_PREFIXOF,
    OP_STR_SUFFIXOF,
	// string-integer conversion
	OP_STR_STR2INT,
	OP_STR_INT2STR, OP_STR_PLACEHOLDER1, OP_STR_PLACEHOLDER2,
	// regular expression operators
	OP_RE_STR2REGEX,
	OP_RE_REGEXIN,
	OP_RE_REGEXCONCAT,
	OP_RE_REGEXSTAR,
	OP_RE_REGEXUNION,
	OP_RE_UNROLL,
	// higher-level regex operators
	OP_RE_REGEXPLUS,
	OP_RE_REGEXCHARRANGE,
    // end
    LAST_STR_OP
};

class str_decl_plugin : public decl_plugin {
protected:
    symbol m_strv_sym;
    sort * m_str_decl;
    sort * m_regex_decl;

    func_decl * m_concat_decl;
    func_decl * m_length_decl;

    func_decl * m_charat_decl;
    func_decl * m_startswith_decl;
    func_decl * m_endswith_decl;
    func_decl * m_contains_decl;
    func_decl * m_indexof_decl;
    func_decl * m_indexof2_decl;
    func_decl * m_lastindexof_decl;
    func_decl * m_substr_decl;
    func_decl * m_replace_decl;
    func_decl * m_str2int_decl;
    func_decl * m_int2str_decl;
    func_decl * m_prefixof_decl;
    func_decl * m_suffixof_decl;

    func_decl * m_re_str2regex_decl;
    func_decl * m_re_regexin_decl;
    func_decl * m_re_regexconcat_decl;
    func_decl * m_re_regexstar_decl;
    func_decl * m_re_regexunion_decl;
    func_decl * m_re_unroll_decl;
    func_decl * m_re_regexplus_decl;
    func_decl * m_re_regexcharrange_decl;

    arith_decl_plugin * m_arith_plugin;
    family_id           m_arith_fid;
    sort *              m_int_sort;

    std::map<std::string, app*> string_cache;

    virtual void set_manager(ast_manager * m, family_id id);

    func_decl * mk_func_decl(decl_kind k);
public:
    str_decl_plugin();
    virtual ~str_decl_plugin();
    virtual void finalize();

    virtual decl_plugin * mk_fresh();
    virtual sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters);
    virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                         unsigned arity, sort * const * domain, sort * range);

    app * mk_string(const char * val);
    app * mk_string(std::string & val);
    app * mk_fresh_string();

    virtual void get_op_names(svector<builtin_name> & op_names, symbol const & logic);
    virtual void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic);

    virtual bool is_value(app * e) const;
    virtual bool is_unique_value(app * e) const { return is_value(e); }
};

class str_recognizers {
    family_id m_afid;
public:
    str_recognizers(family_id fid):m_afid(fid) {}
    family_id get_fid() const { return m_afid; }
    family_id get_family_id() const { return get_fid(); }

    bool is_str_sort(sort* s) const { return is_sort_of(s, m_afid, STRING_SORT); }

    bool is_string(expr const * n, const char ** val) const;
    bool is_string(expr const * n) const;

    bool is_re_Str2Reg(expr const * n) const { return is_app_of(n, get_fid(), OP_RE_STR2REGEX); }
    bool is_re_RegexConcat(expr const * n) const { return is_app_of(n, get_fid(), OP_RE_REGEXCONCAT); }
    bool is_re_RegexUnion(expr const * n) const { return is_app_of(n, get_fid(), OP_RE_REGEXUNION); }
    bool is_re_RegexStar(expr const * n) const { return is_app_of(n, get_fid(), OP_RE_REGEXSTAR); }
    bool is_re_RegexPlus(expr const * n) const { return is_app_of(n, get_fid(), OP_RE_REGEXPLUS); }

    std::string get_string_constant_value(expr const *n) const;
};

class str_util : public str_recognizers {
    ast_manager & m_manager;
    str_decl_plugin * m_plugin;
    family_id m_fid;
public:
    str_util(ast_manager & m);
    ast_manager & get_manager() const { return m_manager; }
    str_decl_plugin & plugin() { return *m_plugin; }

    sort* mk_string_sort() const { return get_manager().mk_sort(m_fid, STRING_SORT, 0, 0); }

    app * mk_string(const char * val) {
        return m_plugin->mk_string(val);
    }
    app * mk_string(std::string & val) {
    	return m_plugin->mk_string(val);
    }

    app * mk_fresh_string() {
        return m_plugin->mk_fresh_string();
    }

    app * mk_string_with_escape_characters(const char * val) {
        std::string str(val);
        return mk_string_with_escape_characters(str);
    }
    app * mk_string_with_escape_characters(std::string & val);

    app * mk_str_StartsWith(expr * haystack, expr * needle) {
        expr * es[2] = {haystack, needle};
        return m_manager.mk_app(get_fid(), OP_STR_STARTSWITH, 2, es);
    }

    app * mk_str_EndsWith(expr * haystack, expr * needle) {
        expr * es[2] = {haystack, needle};
        return m_manager.mk_app(get_fid(), OP_STR_ENDSWITH, 2, es);
    }

    app * mk_re_Str2Reg(expr * s) {
        expr * es[1] = {s};
        return m_manager.mk_app(get_fid(), OP_RE_STR2REGEX, 1, es);
    }

    app * mk_re_Str2Reg(std::string s) {
        return mk_re_Str2Reg(mk_string(s));
    }

    app * mk_re_RegexUnion(expr * e1, expr * e2) {
        expr * es[2] = {e1, e2};
        return m_manager.mk_app(get_fid(), OP_RE_REGEXUNION, 2, es);
    }

    app * mk_re_RegexConcat(expr * e1, expr * e2) {
        expr * es[2] = {e1, e2};
        return m_manager.mk_app(get_fid(), OP_RE_REGEXCONCAT, 2, es);
    }

    app * mk_re_RegexStar(expr * r) {
        expr * es[1] = {r};
        return m_manager.mk_app(get_fid(), OP_RE_REGEXSTAR, 1, es);
    }

    std::string get_std_regex_str(expr * regex);

};

#endif /* _STR_DECL_PLUGIN_H_ */

#endif /* disable */
