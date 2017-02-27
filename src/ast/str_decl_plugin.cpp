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

#include<sstream>
#include"str_decl_plugin.h"
#include"string_buffer.h"
#include"warning.h"
#include"ast_pp.h"
#include"ast_smt2_pp.h"

str_decl_plugin::str_decl_plugin():
    m_strv_sym("String"),
    m_str_decl(0),
	m_regex_decl(0),
    m_concat_decl(0),
    m_length_decl(0),
    m_charat_decl(0),
    m_startswith_decl(0),
    m_endswith_decl(0),
    m_contains_decl(0),
    m_indexof_decl(0),
    m_indexof2_decl(0),
    m_lastindexof_decl(0),
    m_substr_decl(0),
    m_replace_decl(0),
	m_str2int_decl(0),
	m_int2str_decl(0),
	m_prefixof_decl(0),
	m_suffixof_decl(0),
	m_re_str2regex_decl(0),
	m_re_regexin_decl(0),
	m_re_regexconcat_decl(0),
	m_re_regexstar_decl(0),
	m_re_regexunion_decl(0),
	m_re_unroll_decl(0),
    m_re_regexplus_decl(0),
    m_re_regexcharrange_decl(0),
    m_arith_plugin(0),
    m_arith_fid(0),
    m_int_sort(0){
}

str_decl_plugin::~str_decl_plugin(){
}

void str_decl_plugin::finalize(void) {
    #define DEC_REF(decl) if (decl) { m_manager->dec_ref(decl); } ((void) 0)
    DEC_REF(m_str_decl);
    DEC_REF(m_regex_decl);
    DEC_REF(m_concat_decl);
    DEC_REF(m_length_decl);
    DEC_REF(m_charat_decl);
    DEC_REF(m_startswith_decl);
    DEC_REF(m_endswith_decl);
    DEC_REF(m_contains_decl);
    DEC_REF(m_indexof_decl);
    DEC_REF(m_indexof2_decl);
    DEC_REF(m_lastindexof_decl);
    DEC_REF(m_substr_decl);
    DEC_REF(m_replace_decl);
    DEC_REF(m_prefixof_decl);
    DEC_REF(m_suffixof_decl);
    DEC_REF(m_str2int_decl);
    DEC_REF(m_int2str_decl);
    DEC_REF(m_re_str2regex_decl);
    DEC_REF(m_re_regexin_decl);
    DEC_REF(m_re_regexconcat_decl);
    DEC_REF(m_re_regexstar_decl);
    DEC_REF(m_re_regexunion_decl);
    DEC_REF(m_re_regexplus_decl);
    DEC_REF(m_re_regexcharrange_decl);
    DEC_REF(m_re_unroll_decl);
    DEC_REF(m_int_sort);
}

void str_decl_plugin::set_manager(ast_manager * m, family_id id) {
    decl_plugin::set_manager(m, id);
    m_str_decl = m->mk_sort(symbol("String"), sort_info(id, STRING_SORT));
    m->inc_ref(m_str_decl);
    sort * s = m_str_decl;

    m_regex_decl = m->mk_sort(symbol("Regex"), sort_info(id, REGEX_SORT));
    m->inc_ref(m_regex_decl);
    sort * re = m_regex_decl;

    SASSERT(m_manager->has_plugin(symbol("arith")));
    m_arith_fid = m_manager->mk_family_id("arith");
    m_arith_plugin = static_cast<arith_decl_plugin*>(m_manager->get_plugin(m_arith_fid));
    SASSERT(m_arith_plugin);

    m_int_sort = m_manager->mk_sort(m_arith_fid, INT_SORT);
    SASSERT(m_int_sort != 0); // arith_decl_plugin must be installed before str_decl_plugin.
    m_manager->inc_ref(m_int_sort);
    sort * i = m_int_sort;

    sort* boolT = m_manager->mk_bool_sort();

#define MK_OP(FIELD, NAME, KIND, SORT)                                                  \
    FIELD = m->mk_func_decl(symbol(NAME), SORT, SORT, SORT, func_decl_info(id, KIND));  \
    m->inc_ref(FIELD)

    MK_OP(m_concat_decl, "str.++", OP_STRCAT, s);

    m_length_decl = m->mk_func_decl(symbol("str.len"), s, i, func_decl_info(id, OP_STRLEN));
    m_manager->inc_ref(m_length_decl);

    m_charat_decl = m->mk_func_decl(symbol("str.at"), s, i, s, func_decl_info(id, OP_STR_CHARAT));
    m_manager->inc_ref(m_charat_decl);

    m_startswith_decl = m->mk_func_decl(symbol("StartsWith"), s, s, boolT, func_decl_info(id, OP_STR_STARTSWITH));
    m_manager->inc_ref(m_startswith_decl);

    m_endswith_decl = m->mk_func_decl(symbol("EndsWith"), s, s, boolT, func_decl_info(id, OP_STR_ENDSWITH));
    m_manager->inc_ref(m_endswith_decl);

    m_contains_decl = m->mk_func_decl(symbol("str.contains"), s, s, boolT, func_decl_info(id, OP_STR_CONTAINS));
    m_manager->inc_ref(m_contains_decl);

    m_indexof_decl = m->mk_func_decl(symbol("str.indexof"), s, s, i, func_decl_info(id, OP_STR_INDEXOF));
    m_manager->inc_ref(m_indexof_decl);

    {
        sort * d[3] = { s, s, i };
        m_indexof2_decl = m->mk_func_decl(symbol("Indexof2"), 3, d, i, func_decl_info(id, OP_STR_INDEXOF2));
        m_manager->inc_ref(m_indexof2_decl);
    }

    m_lastindexof_decl = m->mk_func_decl(symbol("str.lastindexof"), s, s, i, func_decl_info(id, OP_STR_LASTINDEXOF));
    m_manager->inc_ref(m_lastindexof_decl);

    {
        sort * d[3] = {s, i, i };
        m_substr_decl = m->mk_func_decl(symbol("str.substr"), 3, d, s, func_decl_info(id, OP_STR_SUBSTR));
        m_manager->inc_ref(m_substr_decl);
    }

    {
        sort * d[3] = {s, s, s};
        m_replace_decl = m->mk_func_decl(symbol("str.replace"), 3, d, s, func_decl_info(id, OP_STR_REPLACE));
        m_manager->inc_ref(m_replace_decl);
    }

    m_prefixof_decl = m->mk_func_decl(symbol("str.prefixof"), s, s, boolT, func_decl_info(id, OP_STR_PREFIXOF));
    m_manager->inc_ref(m_prefixof_decl);

    m_suffixof_decl = m->mk_func_decl(symbol("str.suffixof"), s, s, boolT, func_decl_info(id, OP_STR_SUFFIXOF));
    m_manager->inc_ref(m_suffixof_decl);

    m_str2int_decl = m->mk_func_decl(symbol("str.to-int"), s, i, func_decl_info(id, OP_STR_STR2INT));
    m_manager->inc_ref(m_str2int_decl);

    m_int2str_decl = m->mk_func_decl(symbol("str.from-int"), i, s, func_decl_info(id, OP_STR_INT2STR));
    m_manager->inc_ref(m_int2str_decl);

    m_re_str2regex_decl = m->mk_func_decl(symbol("str.to.re"), s, re, func_decl_info(id, OP_RE_STR2REGEX));
    m_manager->inc_ref(m_re_str2regex_decl);

    m_re_regexin_decl = m->mk_func_decl(symbol("str.in.re"), s, re, boolT, func_decl_info(id, OP_RE_REGEXIN));
    m_manager->inc_ref(m_re_regexin_decl);

    m_re_regexconcat_decl = m->mk_func_decl(symbol("re.++"), re, re, re, func_decl_info(id, OP_RE_REGEXCONCAT));
    m_manager->inc_ref(m_re_regexconcat_decl);

    m_re_regexstar_decl = m->mk_func_decl(symbol("re.*"), re, re, func_decl_info(id, OP_RE_REGEXSTAR));
    m_manager->inc_ref(m_re_regexstar_decl);

    m_re_regexplus_decl = m->mk_func_decl(symbol("re.+"), re, re, func_decl_info(id, OP_RE_REGEXPLUS));
    m_manager->inc_ref(m_re_regexplus_decl);

    m_re_regexunion_decl = m->mk_func_decl(symbol("re.union"), re, re, re, func_decl_info(id, OP_RE_REGEXUNION));
    m_manager->inc_ref(m_re_regexunion_decl);

    m_re_unroll_decl = m->mk_func_decl(symbol("Unroll"), re, i, s, func_decl_info(id, OP_RE_UNROLL));
    m_manager->inc_ref(m_re_unroll_decl);

    m_re_regexcharrange_decl = m->mk_func_decl(symbol("re.range"), s, s, re, func_decl_info(id, OP_RE_REGEXCHARRANGE));
    m_manager->inc_ref(m_re_regexcharrange_decl);

}

decl_plugin * str_decl_plugin::mk_fresh() {
    return alloc(str_decl_plugin);
}

sort * str_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    switch (k) {
    case STRING_SORT: return m_str_decl;
    case REGEX_SORT: return m_regex_decl;
    default: return 0;
    }
}

func_decl * str_decl_plugin::mk_func_decl(decl_kind k) {
    switch(k) {
    case OP_STRCAT: return m_concat_decl;
    case OP_STRLEN: return m_length_decl;
    case OP_STR_CHARAT: return m_charat_decl;
    case OP_STR_STARTSWITH: return m_startswith_decl;
    case OP_STR_ENDSWITH: return m_endswith_decl;
    case OP_STR_CONTAINS: return m_contains_decl;
    case OP_STR_INDEXOF: return m_indexof_decl;
    case OP_STR_INDEXOF2: return m_indexof2_decl;
    case OP_STR_LASTINDEXOF: return m_lastindexof_decl;
    case OP_STR_SUBSTR: return m_substr_decl;
    case OP_STR_REPLACE: return m_replace_decl;
    case OP_STR_PREFIXOF: return m_prefixof_decl;
    case OP_STR_SUFFIXOF: return m_suffixof_decl;
    case OP_STR_STR2INT: return m_str2int_decl;
    case OP_STR_INT2STR: return m_int2str_decl;
    case OP_RE_STR2REGEX: return m_re_str2regex_decl;
    case OP_RE_REGEXIN: return m_re_regexin_decl;
    case OP_RE_REGEXCONCAT: return m_re_regexconcat_decl;
    case OP_RE_REGEXSTAR: return m_re_regexstar_decl;
    case OP_RE_REGEXPLUS: return m_re_regexplus_decl;
    case OP_RE_REGEXUNION: return m_re_regexunion_decl;
    case OP_RE_UNROLL: return m_re_unroll_decl;
    case OP_RE_REGEXCHARRANGE: return m_re_regexcharrange_decl;
    default: return 0;
    }
}

func_decl * str_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                         unsigned arity, sort * const * domain, sort * range) {
    if (k == OP_STR) {
        m_manager->raise_exception("OP_STR not yet implemented in mk_func_decl!");
        return 0;
    }
    if (arity == 0) {
        m_manager->raise_exception("no arguments supplied to string operator");
        return 0;
    }
    return mk_func_decl(k);
}

app * str_decl_plugin::mk_string(std::string & val) {
	std::map<std::string, app*>::iterator it = string_cache.find(val);
	//if (it == string_cache.end()) {
	if (true) {
		char * new_buffer = alloc_svect(char, (val.length() + 1));
		strcpy(new_buffer, val.c_str());
		parameter p[1] = {parameter(new_buffer)};
		func_decl * d;
		d = m_manager->mk_const_decl(m_strv_sym, m_str_decl, func_decl_info(m_family_id, OP_STR, 1, p));
		app * str = m_manager->mk_const(d);
		string_cache[val] = str;
		return str;
	} else {
		return it->second;
	}
}

app * str_decl_plugin::mk_string(const char * val) {
	std::string key(val);
	return mk_string(key);
}

app * str_decl_plugin::mk_fresh_string() {
    // cheating.
    // take the longest string in the cache, append the letter "A", and call it fresh.
    std::string longestString = "";
    std::map<std::string, app*>::iterator it = string_cache.begin();
    for (; it != string_cache.end(); ++it) {
        if (it->first.length() > longestString.length()) {
            longestString = it->first;
        }
    }
    longestString += "A";
    return mk_string(longestString);
}

void str_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    op_names.push_back(builtin_name("str.++", OP_STRCAT));
    op_names.push_back(builtin_name("str.len", OP_STRLEN));
    op_names.push_back(builtin_name("str.at", OP_STR_CHARAT));
    op_names.push_back(builtin_name("StartsWith", OP_STR_STARTSWITH));
    op_names.push_back(builtin_name("EndsWith", OP_STR_ENDSWITH));
    op_names.push_back(builtin_name("str.contains", OP_STR_CONTAINS));
    op_names.push_back(builtin_name("str.indexof", OP_STR_INDEXOF));
    op_names.push_back(builtin_name("Indexof2", OP_STR_INDEXOF2));
    op_names.push_back(builtin_name("str.lastindexof", OP_STR_LASTINDEXOF));
    op_names.push_back(builtin_name("str.substr", OP_STR_SUBSTR));
    op_names.push_back(builtin_name("str.replace", OP_STR_REPLACE));
    op_names.push_back(builtin_name("str.prefixof", OP_STR_PREFIXOF));
    op_names.push_back(builtin_name("str.suffixof", OP_STR_SUFFIXOF));
    op_names.push_back(builtin_name("str.to-int", OP_STR_STR2INT));
    op_names.push_back(builtin_name("str.from-int", OP_STR_INT2STR));
    op_names.push_back(builtin_name("str.to.re", OP_RE_STR2REGEX));
    op_names.push_back(builtin_name("str.in.re", OP_RE_REGEXIN));
    op_names.push_back(builtin_name("re.++", OP_RE_REGEXCONCAT));
    op_names.push_back(builtin_name("re.*", OP_RE_REGEXSTAR));
    op_names.push_back(builtin_name("re.union", OP_RE_REGEXUNION));
    op_names.push_back(builtin_name("re.+", OP_RE_REGEXPLUS));
    op_names.push_back(builtin_name("Unroll", OP_RE_UNROLL));
    op_names.push_back(builtin_name("re.range", OP_RE_REGEXCHARRANGE));
}

void str_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
    sort_names.push_back(builtin_name("String", STRING_SORT));
    sort_names.push_back(builtin_name("Regex", REGEX_SORT));
}

bool str_decl_plugin::is_value(app * e) const {
    if (e->get_family_id() != m_family_id) {
        return false;
    }
    switch (e->get_decl_kind()) {
    case OP_STR:
        return true;
    default:
        return false;
    }
}

bool str_recognizers::is_string(expr const * n, const char ** val) const {
    if (!is_app_of(n, m_afid, OP_STR))
            return false;
    func_decl * decl = to_app(n)->get_decl();
    *val    = decl->get_parameter(0).get_string();
    return true;
}

bool str_recognizers::is_string(expr const * n) const {
    const char * tmp = 0;
    return is_string(n, & tmp);
}

std::string str_recognizers::get_string_constant_value(expr const *n) const {
    const char * cstr = 0;
    bool isString = is_string(n, & cstr);
    SASSERT(isString);
    std::string strval(cstr);
    return strval;
}

str_util::str_util(ast_manager &m) :
    str_recognizers(m.mk_family_id(symbol("str"))),
    m_manager(m) {
    SASSERT(m.has_plugin(symbol("str")));
    m_plugin = static_cast<str_decl_plugin*>(m.get_plugin(m.mk_family_id(symbol("str"))));
    m_fid = m_plugin->get_family_id();
}

/*
 * Scan through the string 'val' and interpret each instance of "backslash followed by a character"
 * as a possible escape sequence. Emit all other characters as-is.
 * This exists because the SMT-LIB 2.5 standard does not recognize escape sequences other than "" -> " .
 * The escape sequences recognized are as follows:
 *   \a \b \e \f \n \r \t \v \\ : as specified by the C++ standard
 *   \ooo : produces the ASCII character corresponding to the octal value "ooo", where each "o" is a
 *          single octal digit and between 1 and 3 valid digits are given
 *   \xhh : produces the ASCII character corresponding to the hexadecimal value "hh", where each "h" is a
 *          single case-insensitive hex digit (0-9A-F) and exactly 2 digits are given
 *   \C, for any character C that does not start a legal escape sequence : the backslash is ignored and "C" is produced.
 */
app * str_util::mk_string_with_escape_characters(std::string & val) {
    std::string parsedStr;
    parsedStr.reserve(val.length());
    for (unsigned i = 0; i < val.length(); ++i) {
        char nextChar = val.at(i);

        if (nextChar == '\\') {
            // check escape sequence
            i++;
            if (i >= val.length()) {
                get_manager().raise_exception("invalid escape sequence");
            }
            char escapeChar1 = val.at(i);
            if (escapeChar1 == 'a') {
                parsedStr.push_back('\a');
            } else if (escapeChar1 == 'b') {
                parsedStr.push_back('\b');
            } else if (escapeChar1 == 'e') {
                parsedStr.push_back('\e');
            } else if (escapeChar1 == 'f') {
                parsedStr.push_back('\f');
            } else if (escapeChar1 == 'n') {
                parsedStr.push_back('\n');
            } else if (escapeChar1 == 'r') {
                parsedStr.push_back('\r');
            } else if (escapeChar1 == 't') {
                parsedStr.push_back('\t');
            } else if (escapeChar1 == 'v') {
                parsedStr.push_back('\v');
            } else if (escapeChar1 == '\\') {
                parsedStr.push_back('\\');
            } else if (escapeChar1 == 'x') {
                // hex escape: we expect 'x' to be followed by exactly two hex digits
                // which means that i+2 must be a valid index
                if (i+2 >= val.length()) {
                    get_manager().raise_exception("invalid hex escape: \\x must be followed by exactly two hex digits");
                }
                char hexDigitHi = val.at(i+1);
                char hexDigitLo = val.at(i+2);
                i += 2;
                if (!isxdigit((int)hexDigitHi) || !isxdigit((int)hexDigitLo)) {
                    get_manager().raise_exception("invalid hex escape: \\x must be followed by exactly two hex digits");
                }
                char tmp[3] = {hexDigitHi, hexDigitLo, '\0'};
                long converted = strtol(tmp, NULL, 16);
                unsigned char convChar = (unsigned char)converted;
                parsedStr.push_back(convChar);
            } else if (escapeChar1 == '0' || escapeChar1 == '1' || escapeChar1 == '2' || escapeChar1 == '3' ||
                    escapeChar1 == '4' || escapeChar1 == '5' || escapeChar1 == '6' || escapeChar1 == '7') {
                // octal escape: we expect exactly three octal digits
                // which means that val[i], val[i+1], val[i+2] must all be octal digits
                // and that i+2 must be a valid index
                if (i+2 >= val.length()) {
                    get_manager().raise_exception("invalid octal escape: exactly three octal digits required");
                }
                char c2 = escapeChar1;
                char c1 = val.at(i+1);
                char c0 = val.at(i+2);
                i += 2;

                if (!isdigit(c2) || !isdigit(c1) || !isdigit(c0)) {
                    get_manager().raise_exception("invalid octal escape: exactly three octal digits required");
                }

                if (c2 == '8' || c2 == '9' || c1 == '8' || c1 == '9' || c0 == '8' || c0 == '9') {
                    get_manager().raise_exception("invalid octal escape: exactly three octal digits required");
                }

                char tmp[4] = {c2, c1, c0, '\0'};
                long converted = strtol(tmp, NULL, 8);
                unsigned char convChar = (unsigned char)converted;
                parsedStr.push_back(convChar);
            } else {
                // unrecognized escape sequence -- just emit that character
                parsedStr.push_back(escapeChar1);
            }
        } else {
            parsedStr.push_back(nextChar);
        }

        // i is incremented at the end of this loop.
        // If it is modified, ensure that it points to the index before
        // the next character.
    }
    return mk_string(parsedStr);
}

static std::string str2RegexStr(std::string str) {
    std::string res = "";
    int len = str.size();
    for (int i = 0; i < len; i++) {
      char nc = str[i];
      // 12 special chars
      if (nc == '\\' || nc == '^' || nc == '$' || nc == '.' || nc == '|' || nc == '?'
          || nc == '*' || nc == '+' || nc == '(' || nc == ')' || nc == '[' || nc == '{') {
        res.append(1, '\\');
      }
      res.append(1, str[i]);
    }
    return res;
}

std::string str_util::get_std_regex_str(expr * regex) {
    app * a_regex = to_app(regex);
    if (is_re_Str2Reg(a_regex)) {
        expr * regAst = a_regex->get_arg(0);
        std::string regStr = str2RegexStr(get_string_constant_value(regAst));
        return regStr;
    } else if (is_re_RegexConcat(a_regex)) {
        expr * reg1Ast = a_regex->get_arg(0);
        expr * reg2Ast = a_regex->get_arg(1);
        std::string reg1Str = get_std_regex_str(reg1Ast);
        std::string reg2Str = get_std_regex_str(reg2Ast);
        return "(" + reg1Str + ")(" + reg2Str + ")";
    } else if (is_re_RegexUnion(a_regex)) {
        expr * reg1Ast = a_regex->get_arg(0);
        expr * reg2Ast = a_regex->get_arg(1);
        std::string reg1Str = get_std_regex_str(reg1Ast);
        std::string reg2Str = get_std_regex_str(reg2Ast);
        return  "(" + reg1Str + ")|(" + reg2Str + ")";
    } else if (is_re_RegexStar(a_regex)) {
        expr * reg1Ast = a_regex->get_arg(0);
        std::string reg1Str = get_std_regex_str(reg1Ast);
        return  "(" + reg1Str + ")*";
    } else {
        TRACE("t_str", tout << "BUG: unrecognized regex term " << mk_pp(regex, get_manager()) << std::endl;);
        UNREACHABLE(); return "";
    }
}

#endif /* disable */
