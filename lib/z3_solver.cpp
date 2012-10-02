/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    z3_solver.cpp

Abstract:

    Native ast parser.

Author:

    Nikolaj Bjorner (nbjorner) 2007-07-17

Revision History:

--*/

#include "z3_solver.h"
#include "z3_private.h"
#include "warning.h"
#include "ast_pp.h"
#include "ast_ll_pp.h"
#include "ast_smt_pp.h"
#include "version.h"
#include "array_decl_plugin.h"
#include "bv_decl_plugin.h"
#include "arith_decl_plugin.h"
#include "lbool.h"
#include <sstream>

#define CHECK(_b_) if (!(_b_)) { return false; }

#define CHECK_P(_b_,_m_) if (!(_b_)) { warning_msg(_m_); return false; }

#define CHECK_CB(_b_,_cb_) if (!(_b_)) { _cb_; return false; }

#define TRY_CHECK(_b_) if (!(_b_)) { return false; }


ast_manager& Z3_get_manager(Z3_context c);
Z3_context Z3_mk_context_from_params(front_end_params const& p);  
void Z3_display_statistics(Z3_context c, std::ostream& s);
void Z3_display_istatistics(Z3_context c, std::ostream& s);

z3_solver::z3_solver(
    Z3_context context,
    std::istream& ins,
    std::ostream& ous,
    front_end_params & params,
    bool is_active
    )
    : 
    m_context(context?context:Z3_mk_context_from_params(params)),
    m_owns_context(context?false:true),
    m_manager(Z3_get_manager(m_context)),
    m_params(params),
    m_in(ins),
    m_out(ous),
    m_is_active(is_active),
    m_assumptions(m_manager),
    m_num_checks(0),
    m_eof(false),
    m_line(1),
    m_arith(m_manager),
    m_bv(m_manager),
    m_pinned(m_manager),
    m_last_check_result(Z3_L_UNDEF)
{
    add_builtins(m_manager.get_family_id("bv"));
    add_builtins(m_manager.get_family_id("arith"));
    add_builtins(m_manager.get_basic_family_id());
    add_builtins(m_manager.get_family_id("array"));
    add_builtins(m_manager.get_family_id("datatype"));
}

z3_solver::z3_solver(
    ast_manager&  m,
    std::istream& ins,
    std::ostream& ous,
    front_end_params & params
    )
    : 
    m_context(0),
    m_owns_context(true),
    m_manager(m),
    m_params(params),
    m_in(ins),
    m_out(ous),
    m_is_active(false),
    m_assumptions(m_manager),
    m_num_checks(0),
    m_eof(false),
    m_line(1),
    m_arith(m_manager),
    m_bv(m_manager),
    m_pinned(m_manager)
{
    add_builtins(m_manager.get_family_id("bv"));
    add_builtins(m_manager.get_family_id("arith"));
    add_builtins(m_manager.get_basic_family_id());
    add_builtins(m_manager.get_family_id("array"));
    add_builtins(m_manager.get_family_id("datatype"));

}


z3_solver::~z3_solver()
{
    m_assumptions.reset();
    m_pinned.reset();
    if (m_owns_context && m_context) {
        Z3_del_context(m_context);
    }
}

void z3_solver::skip_blank() {
    while (*m_in == ' ' || *m_in == '\t' || *m_in == '\r') {
        ++m_in;
    }
}

bool z3_solver::next_token() {    
    if (m_eof) {
        warning_msg("line %d. EOF reached, expecting string", m_line);
        return false;
    }
    skip_blank();
    if (*m_in == EOF) {
        m_eof = true;
        return true;
    }
    m_string.clear();
    while (*m_in != '\n' && *m_in != ' ' && 
           *m_in != '\r' &&
           *m_in != '\t' && *m_in != EOF) {
        m_string.push_back(*m_in);
        ++m_in;
    }   
    if (*m_in == '\n' && m_string.empty()) {
        m_string = "\n";
        ++m_in;
    }
    return true;
}


bool z3_solver::try_parse(char const* token) {
    CHECK(!m_eof);
    TRY_CHECK(strcmp(token, m_string.c_str()) == 0);
    CHECK(next_token());
    return true;
}

bool z3_solver::parse_int(int& i) {
    if (m_eof) {
        warning_msg("line %d. EOF reached, expecting numeral", m_line);
        return false;
    }
    const char* s = m_string.c_str();    
    i = 0;
    bool negate = false;
    if (*s == '-') {
        negate = true;
        ++s;
    }
    // NB: overflow checks are ignored.
    while ('0' <= *s && *s <= '9') {
        i = (i*10) + (*s - '0');
        ++s;
    }
    if (negate) {
        i = -i;
    }
    CHECK(next_token());    
    return true;
}

bool z3_solver::check_int(int& i) {
    if (m_eof) {
        return false;
    }
    const char* s = m_string.c_str();    
    bool negate = false;
    i = 0;
    if (!(('0' <= *s && *s <= '9') || *s == '-')) {
        return false;
    }
    if (*s == '-') {
        negate = true;
        ++s;
    }
    while ('0' <= *s && *s <= '9') {
        i = (i*10) + (*s - '0');
        ++s;
    }
    if (negate) {
        i = -i;
    }
    return true;
}

bool z3_solver::parse_unsigned(unsigned& i) {
    if (m_eof) {
        warning_msg("line %d. EOF reached, expecting numeral", m_line);
        return false;
    }
    const char* s = m_string.c_str();    
    i = 0;
    // NB: overflow checks are ignored.
    while ('0' <= *s && *s <= '9') {
        i = (i*10) + (*s - '0');
        ++s;
    }
    CHECK(next_token());    
    return true;
}

bool z3_solver::check_unsigned(unsigned& i) {
    if (m_eof) {
        return false;
    }
    const char* s = m_string.c_str();    
    i = 0;
    if (!('0' <= *s && *s <= '9')) {
        return false;
    }
    while ('0' <= *s && *s <= '9') {
        i = (i*10) + (*s - '0');
        ++s;
    }
    return true;
}


bool z3_solver::parse_id(symbol& id) {
    size_t sz = m_string.size();
    char const* str = m_string.c_str();
    if (strcmp(str,"\"null\"") == 0) {
        id = symbol();
    }
    else if (sz > 0 && str[0] == '"' && str[sz-1] == '"') {
        std::string s(str,sz-1);
        id = s.c_str();
    }
    else {
        id = m_string.c_str();
    }
    CHECK(next_token());
    return true;
}


bool z3_solver::parse_rational(rational& r) {
    if (m_eof) {
        warning_msg("line %d. EOF reached, expecting rational", m_line);
        return false;
    }
    r = rational(m_string.c_str());
    CHECK(next_token());
    return true;
}


bool z3_solver::parse_eol() {
    if (m_eof) {
        warning_msg("line %d. EOF reached, expecting newline", m_line);
        return false;
    }
    if (m_string[0] != '\n') {
        warning_msg("line %d. Expecting newline, got '%s'\n", m_line, m_string.c_str());
        return false;
    }    
    ++m_line;
    CHECK(next_token());

    return true;
}


z3_solver::kind z3_solver::parse_kind() {
 try_again:
    if (m_eof) {
        return T_EOF;
    }
    kind k = T_ERR;

    switch(m_string[0]) {
    case 'A':
        if (strcmp(m_string.c_str(), "Assert") == 0) {
            k = T_ASSERT;
        }
        else if (strcmp(m_string.c_str(), "App") == 0) {
            k = T_BUILTIN_CONST;
        }
        break;
    case 'C':
        if (strcmp(m_string.c_str(), "Const") == 0) {
            k = T_NULLARY_CONST;
        }
        else if (strcmp(m_string.c_str(), "Check") == 0) {
            k = T_CHECK;
        }
        else if (strcmp(m_string.c_str(), "CheckAssumptions") == 0) {
            k = T_CHECK_ASSUMPTIONS;
        }
        break;
    case 'D':
        if (strcmp(m_string.c_str(), "Dec") == 0) {
            k = T_DEC;
        }
        else if (strcmp(m_string.c_str(), "DbgSat") == 0) {
            k = T_DBG_SAT;
        }
        else if (strcmp(m_string.c_str(), "DbgUnsat") == 0) {
            k = T_DBG_UNSAT;
        }
        break;
    case 'E':
        if (strcmp(m_string.c_str(), "Echo") == 0) {
            k = T_ECHO;
        }
        break;
    case 'F':
        if (strcmp(m_string.c_str(), "Fun") == 0) {
            k = T_FUNCTION_CONST;
        }
        break;
    case 'G':
        if (strcmp(m_string.c_str(), "GetImpliedEqualities") == 0) {
            k = T_GET_IMPLIED_EQUALITIES;
        }
        break;
    case 'L':
        if (strcmp(m_string.c_str(), "Lab") == 0) {
            k = T_LAB;
        }
        break;
    case 'N':
        if (strcmp(m_string.c_str(), "Num") == 0) {
            k = T_NUM;
        }
        break;
    case 'P':
        if (strcmp(m_string.c_str(), "Pat") == 0) {
            k = T_PAT;
        }
        else if (strcmp(m_string.c_str(), "Push") == 0) {
            k = T_PUSH;
        }
        else if (strcmp(m_string.c_str(), "Pop") == 0) {
            k = T_POP;
        }
        break;
    case ';':
        k = T_COMMENT;
        break;
    case '\n':
        if (!next_token()) {
            k = T_ERR;
            break;
        }
        goto try_again;
    case 'Q':
        if (strcmp(m_string.c_str(), "Qua") == 0) {
            k = T_QUA;
        }
        break;
    case 'R':
        if (strcmp(m_string.c_str(), "Reset") == 0) {
            k = T_RESET;
        }
        break;
    case 'S':
        if (strcmp(m_string.c_str(), "Solver") == 0) {
            k = T_SOLVER;
        }
        else if (strcmp(m_string.c_str(), "Simplify") == 0) {
            k = T_SIMPLIFY;
        }
        break;
    case 'T':
        if (strcmp(m_string.c_str(), "Ty") == 0) {
            k = T_TY;
        }
        else if (strcmp(m_string.c_str(), "Type") == 0) {
            k = T_TYPE;
        }
        break;
    case 'V':
        if (strcmp(m_string.c_str(), "Var") == 0) {
            k = T_VAR;
        }
        else if (strcmp(m_string.c_str(), "Version") == 0) {
            k = T_VERSION;
        }
        break;
    default:
        break;
    }
    if (k == T_ERR) {
        warning_msg("line %d. could not recognize token '%s'", m_line, m_string.c_str());
    }
    else if (!next_token()) {
        k = T_ERR;
        warning_msg("line %d. could not recognize token '%s'", m_line, m_string.c_str());
    }
    return k;
    
}

bool z3_solver::parse_comment() {
    while (m_string[0] != '\n') {
        CHECK(next_token());
    }
    CHECK(parse_eol());
    return true;
}

bool z3_solver::parse_numeral() {
    symbol    id;
    rational  r;
    sort* s;
    expr* n;
    CHECK(parse_id(id));
    CHECK(parse_rational(r));
    CHECK(parse_ast<sort>(s, sort_coerce()));
    CHECK(parse_eol());
    if (m_arith.is_int(s)) {
        n = m_arith.mk_numeral(r, true);
    }
    else if (m_arith.is_real(s)) {
        n = m_arith.mk_numeral(r, false);
    }
    else if (m_bv.is_bv_sort(s)) {
        n = m_bv.mk_numeral(r, s);
    }
    else {
        return false;
    }
    add_id(id, n);
    return true;
}


bool z3_solver::parse_var() {
    symbol    id;
    unsigned  n;
    sort* ty;

    CHECK(parse_id(id));
    CHECK(parse_unsigned(n));
    CHECK(parse_ast<sort>(ty,sort_coerce()));
    CHECK(parse_eol());

    var* v = m_manager.mk_var(n, ty);
    add_id(id, v);
    return true;
}


family_id z3_solver::get_family_id(char const* s) {
    symbol sym(s);
    if (sym == "null") {
        return null_family_id;
    }
    else {
        return m_manager.get_family_id(sym);
    }
 
}

bool z3_solver::parse_info(scoped_ptr<func_decl_info>& info) {
    bool is_assoc = false;
    bool is_comm = false;
    bool is_inj = false;
    vector<parameter> params;
    family_id fid = null_family_id;
    decl_kind kind = null_decl_kind;

    if (!try_parse("BUILTIN")) {
        info = 0;
        return true;
    }
    
    fid = get_family_id(m_string.c_str());

    CHECK(next_token());
    CHECK(parse_int(kind));
    
    while (m_string[0] != '\n') {
        std::string s;

        if (strcmp(m_string.c_str(), ":assoc") == 0) {
            is_assoc = true;
        }
        else if (strcmp(m_string.c_str(), ":comm") == 0) {
            is_comm = true;
        }
        else if (strcmp(m_string.c_str(), ":inj") == 0) {
            is_inj = true;
        }
        else {
            CHECK(parse_parameter(params));
            continue;
        }
        CHECK(next_token());
    }

    
    info = alloc(func_decl_info, fid, kind, params.size(), params.c_ptr());
    info->set_associative(is_assoc);
    info->set_commutative(is_comm);
    info->set_injective(is_inj);
    return true;
}


bool z3_solver::parse_info(scoped_ptr<sort_info>& info) {
    vector<parameter> params;
    bool is_infinite = true;
    rational num_elems;
    family_id fid = null_family_id;
    decl_kind kind = null_decl_kind;

    if (!try_parse("BUILTIN")) {
        info = 0;
        return true;
    }

    fid = get_family_id(m_string.c_str());
    std::string th = m_string.c_str();

    CHECK(next_token());
    CHECK(parse_int(kind));

    if (try_parse("Size")) {
        CHECK(parse_rational(num_elems)); 
        is_infinite = false;
    }
    
    while (m_string[0] != '\n') {
        CHECK(parse_parameter(params));
    }
    
    if (!is_infinite && num_elems.is_uint64()) {
        info = alloc(sort_info, fid, kind, num_elems.get_uint64(), params.size(), params.c_ptr());
    }
    else {
        info = alloc(sort_info, fid, kind, params.size(), params.c_ptr());
    }
    return true;
}


bool z3_solver::parse_nullary_const() {
    func_decl* d = 0;
    app* n = 0;
    symbol id;
    CHECK(parse_func_decl(id, d));
    SASSERT(d);
    n = m_manager.mk_const(d);
    CHECK(n);
    add_id(id, n);
    return true;

}

bool z3_solver::parse_func_decl() {
    func_decl* d = 0;
    symbol id;
    CHECK(parse_func_decl(id, d));
    CHECK(d);
    add_id(id, d);
    return true;
}

bool z3_solver::parse_func_decl(symbol& id, func_decl*& n) {
    symbol name;
    sort_ref_vector args(m_manager);
    scoped_ptr<func_decl_info> info;
    CHECK(parse_id(id));
    CHECK(parse_id(name));
    CHECK(parse_asts<sort>(args,sort_coerce()));
    CHECK(parse_info(info));
    CHECK(parse_eol());
    if (args.size() == 0) {
        warning_msg("line %d. Expecting more than 0 arguments", m_line);
        return false;
    }
    unsigned dom_size = args.size()-1;
    sort* rng = args[dom_size].get();

    if (info.get()) {
        n = m_manager.mk_func_decl(
            info.get()->get_family_id(),
            info.get()->get_decl_kind(),
            info.get()->get_num_parameters(), 
            info.get()->get_parameters(), 
            dom_size, args.c_ptr());

        // HACK: not all theories have name-less decl_kinds:
        // constructors, tuples, marbles, etc.
        if (!n) {
            n = m_manager.mk_func_decl(name, dom_size, args.c_ptr(), rng, *info.get());
        }
    }
    else {
        n = m_manager.mk_func_decl(name, dom_size, args.c_ptr(), rng);
    }
    CHECK(n);
    add_id(id, n);
    return true;
}

bool z3_solver::parse_const() {
    symbol id;
    func_decl* d;
    expr_ref_vector args(m_manager);
    CHECK(parse_id(id));
    CHECK(parse_ast<func_decl>(d,func_decl_coerce()));
    CHECK(parse_asts<expr>(args, expr_coerce()));
    CHECK(parse_eol());
    app* n = m_manager.mk_app(d, args.size(), args.c_ptr());
    CHECK(n);
    if (!m_manager.check_sorts(n))
        return false;
    add_id(id, n);
    return true;
}


// App n name [ params ] args 

bool z3_solver::find_builtin_op(symbol name, family_id & fid, decl_kind& kind) {
    builtin_info bi;
    CHECK(m_builtin_ops.find(name, bi));
    fid = bi.m_fid;
    kind = bi.m_kind;
    return true;
}

bool z3_solver::find_builtin_type(symbol name, family_id & fid, decl_kind& kind) {
    builtin_info bi;
    if (!m_builtin_types.find(name, bi)) {
        return false;
    }
    fid = bi.m_fid;
    kind = bi.m_kind;    
    return true;
}

void z3_solver::add_builtins(family_id fid) {
    decl_plugin* plugin = m_manager.get_plugin(fid);
    SASSERT(plugin);
    if (!plugin) {
        return;
    }
    svector<builtin_name> op_names;
    plugin->get_op_names(op_names);
    for (unsigned i = 0; i < op_names.size(); ++i) {
        m_builtin_ops.insert(op_names[i].m_name, builtin_info(fid, op_names[i].m_kind));
    }
    
    svector<builtin_name> sort_names;
    plugin->get_sort_names(sort_names);
    for (unsigned i = 0; i < sort_names.size(); ++i) {
        m_builtin_types.insert(sort_names[i].m_name, builtin_info(fid, sort_names[i].m_kind));
    }
}



bool z3_solver::parse_parameter(vector<parameter>& params) {
    ast* a = 0;
    int n;
    if (check_int(n)) {
        params.push_back(parameter(n));
    }
    else if (m_table.find(symbol(m_string.c_str()), a)) {
        params.push_back(parameter(a));
    }
    else {
        symbol sym;
        if (!parse_id(sym)) {
            return false;
        }
        params.push_back(parameter(sym));
        return true;
    }
    CHECK(next_token());
    return true;
}


bool z3_solver::parse_params(vector<parameter>& params) {
    if (strcmp(m_string.c_str(),"[") == 0) {
        CHECK(next_token());
        while (strcmp(m_string.c_str(),"]") != 0) {
            CHECK(parse_parameter(params));
        }
        CHECK(next_token());
    }
    return true;
}



bool z3_solver::parse_builtin_const() {
    symbol id, name;
    vector<parameter> params;
    family_id fid;
    decl_kind kind;
    app* n = 0;
    expr_ref_vector args(m_manager);
    CHECK(parse_id(id));
    CHECK(parse_id(name));
    CHECK(parse_params(params));
    CHECK(parse_asts<expr>(args, expr_coerce()));
    CHECK(parse_eol());

    if (find_builtin_op(name, fid, kind)) {        
        n = m_manager.mk_app(fid, kind, 
                               params.size(), params.c_ptr(), 
                               args.size(), args.c_ptr());
    }
    else {
        func_decl* d = 0;
        CHECK(parse_ast<func_decl>(name, d, func_decl_coerce()));
        CHECK(d);
        n = m_manager.mk_app(d, args.size(), args.c_ptr());
    }

    CHECK(n);
    if (!m_manager.check_sorts(n))
        return false;
    add_id(id, n);
    return true;
}


bool z3_solver::parse_type() {
    symbol id, name;
    scoped_ptr<sort_info> info;
    CHECK(parse_id(id));
    CHECK(parse_id(name));
    CHECK(parse_info(info));
    CHECK(parse_eol());
    sort* ty;
    if (info.get()) {
        ty = m_manager.mk_sort(name, *info.get());
    }
    else {
        ty = m_manager.mk_sort(name);
    }
    CHECK(ty);
    add_id(id, ty);
    return true;
}


bool z3_solver::parse_type_new() {
    symbol id, name;
    vector<parameter> params;
    CHECK(parse_id(id));
    CHECK(parse_id(name));
    CHECK(parse_params(params));
    CHECK(parse_eol());
    sort* ty;
    family_id fid;
    decl_kind kind;
    if (find_builtin_type(name, fid, kind)) {
        ty = m_manager.mk_sort(fid, kind, params.size(), params.c_ptr());
    }
    else {
        ty = m_manager.mk_sort(name);
    }
    CHECK(ty);
    add_id(id, ty);
    return true;
}


bool z3_solver::parse_label() {
    symbol id, name;
    std::string s;
    expr* a;
    CHECK(parse_id(id));
    CHECK(next_token());
    s = m_string;
    CHECK(parse_id(name));
    CHECK(parse_ast<expr>(a, expr_coerce()));
    CHECK(parse_eol());
    bool pos = (strcmp("LBLPOS",s.c_str()) == 0);
    app* n = m_manager.mk_label(pos, name, a);
    CHECK(n);
    add_id(id, n);
    return true;    
}

bool z3_solver::parse_quantifier() {
    std::string s;
    symbol id;
    unsigned num_decls, num_patterns;
    expr* body;
    bool is_forall;
    unsigned weight;
    symbol skid, qid;
    svector<symbol> names;
    ptr_vector<sort> types;
    ptr_vector<expr> patterns;

    CHECK(parse_id(id));
    s = m_string;
    CHECK(next_token());
    is_forall = (strcmp("FORALL",s.c_str()) == 0);
    CHECK_P(parse_unsigned(weight), "Expected unsigned integer");
    CHECK_P(parse_id(skid), "Expected symbol identifier");
    CHECK_P(parse_id(qid), "Expected symbol identifier");
    CHECK_P(parse_unsigned(num_decls), "Expected unsigned integer for number of declarations");
    for (unsigned i = 0; i < num_decls; ++i) {
        symbol name;
        sort* ty;
        CHECK_P(parse_id(name), "Expected identifier");
        CHECK_P(parse_ast<sort>(ty, sort_coerce()), "Expected sort");
        names.push_back(name);
        types.push_back(ty);
    }
    CHECK_P(parse_unsigned(num_patterns), "Expected unsigned integer for number of patterns");
    for (unsigned i = 0; i < num_patterns; ++i) {
        app* p;
        CHECK_P(parse_ast<app>(p, pattern_coerce(m_manager)), "Expected pattern");
        patterns.push_back(p);
    }
    CHECK_P(parse_ast<expr>(body, expr_coerce()), "Expected expression");
    CHECK(parse_eol());

    CHECK_P(m_manager.is_bool(body), "Body of quantifier should be Boolean type");
    CHECK_P(!m_manager.is_pattern(body), "Body of quantifier cannot be a pattern");


#if 0
    if (qid == symbol() && m_params.m_default_qid) {
        qid = symbol(m_line);
    }
#endif
    if (num_decls > 0) {
        quantifier* n = m_manager.mk_quantifier(
            is_forall, 
            num_decls, types.c_ptr(), names.c_ptr(), body,
            weight, qid, skid, 
            num_patterns, patterns.c_ptr()
            );
        CHECK(n);
        add_id(id, n);
    }
    else {
        add_id(id, body);
    }
    return true;
}



bool z3_solver::parse_pattern() {
    symbol id;
    app_ref_vector patterns(m_manager);
    CHECK(parse_id(id));
    CHECK(parse_asts<app>(patterns, app_coerce()));
    CHECK(parse_eol());
    app* n = m_manager.mk_pattern(patterns.size(), patterns.c_ptr());
    CHECK(n);
    add_id(id, n);
    return true;
}



bool z3_solver::parse_assert()
{
    expr* a = 0;
    CHECK(parse_ast<expr>(a, expr_coerce()));
    CHECK(parse_eol());
    if (m_params.m_ast_ll_pp) {
        ast_ll_pp(m_out, m_manager, a, true);
        m_out.flush();
    }
    if (m_params.m_ast_smt_pp) {
        for (unsigned i = 0; i < m_pinned_lim.size(); ++i) {
            m_out << " ";
        }
        m_out << mk_pp(a, m_manager) << "\n";
        m_out.flush();
    }
    if (m_is_active && m_context) {
        Z3_assert_cnstr(m_context, reinterpret_cast<Z3_ast>(a));
        if (m_params.m_smtlib_trace_path.size() > 0) {
            m_assumptions.push_back(a);
        }
    }
    else {
        m_assumptions.push_back(a);
    }
    return true;
}


bool z3_solver::parse_simplify()
{
    expr* a = 0;
    CHECK(parse_ast<expr>(a, expr_coerce()));
    CHECK(parse_eol());
    if (m_params.m_ast_ll_pp) {
        ast_ll_pp(m_out, m_manager, a, true);
        m_out.flush();
    }
    if (m_params.m_ast_smt_pp) {
        for (unsigned i = 0; i < m_pinned_lim.size(); ++i) {
            m_out << " ";
        }
        m_out << mk_pp(a, m_manager) << "\n";
        m_out.flush();
    }
    if (m_is_active && m_context) {
        Z3_ast r = Z3_simplify(m_context, reinterpret_cast<Z3_ast>(a));
        m_out << mk_pp(reinterpret_cast<ast*>(r), m_manager) << "\n";
        m_out.flush();        
    }
    return true;
}



bool z3_solver::parse_check()
{
    CHECK(parse_eol());

    if (!m_context || !m_is_active) {
        return true;
    }
    
    Z3_model m = 0;    
    Z3_ast pr  = 0;
    Z3_lbool result = Z3_check_assumptions(m_context, 0, 0, &m, &pr, 0, 0);
    m_last_check_result = result;
    
    // display the model.

    if (m && m_params.m_model) {
        char const* md = Z3_model_to_string(m_context, m);
        if (md) {
            m_out << md;
        }
    }
    if (m) {
        Z3_del_model(m_context, m);
    }

    if (result == Z3_L_FALSE && pr != 0 && m_params.m_display_proof) {
        m_out << mk_ll_pp(reinterpret_cast<ast*>(pr), m_manager, true, false);
    }

    switch(result) {
    case l_false: m_out << "unsat\n"; break;
    case l_true: m_out << "sat\n"; break;
    case l_undef: m_out << "unknown\n"; break;
    }
    m_out.flush();

    dump_smtlib_benchmark(0, 0, result);    
    return true;
}

void z3_solver::dump_smtlib_benchmark(unsigned num_assumptions, expr* const* assumptions, Z3_lbool result) {
    //
    // Generate SMT-LIB benchmark from current set of assertions.
    // 
    if (m_params.m_dump_goal_as_smt || m_params.m_smtlib_trace_path.size() > 0) {
        ast_smt_pp pp(m_manager);
        pp.set_logic(m_params.m_smtlib_logic.c_str());
        pp.set_source_info(m_params.m_smtlib_source_info.c_str());
        pp.set_category(m_params.m_smtlib_category.c_str());
        for (unsigned i = 0; i < m_assumptions.size(); ++i) {
            pp.add_assumption(m_assumptions[i].get());
        }
        for (unsigned i = 0; i < num_assumptions; ++i) {
            pp.add_assumption_star(assumptions[i]);
        }
        char const* status = (result == Z3_L_FALSE)?"unsat":((result == Z3_L_TRUE)?"sat":"unknown");
        pp.set_status(status);
        std::ostringstream buffer;
        if (m_params.m_smtlib_trace_path.size() > 0) {
            buffer << m_params.m_smtlib_trace_path.c_str() << "_" << m_num_checks << ".smt2";
        }
        else {
            buffer << "query." << m_num_checks << ".smts";
        }
        std::ofstream out(buffer.str().c_str());
        if (!out.fail() && !out.bad()) {
            pp.display_smt2(out, m_manager.mk_true());
        }
        m_num_checks++;
        out.close();
    }

}


bool z3_solver::parse_get_implied_equalities() 
{
    expr_ref_vector args(m_manager);    
    unsigned_vector cls;
    CHECK(parse_asts<expr>(args, expr_coerce()));
    CHECK(parse_eol());
    cls.resize(args.size());

    if (!m_context) {
        return true;
    }
    

    TRACE("get_implied_equalities", tout << "checking assumptions...\n" << Z3_context_to_string(m_context) << "\n";);
    Z3_lbool result = Z3_get_implied_equalities(m_context, args.size(), reinterpret_cast<Z3_ast*>(args.c_ptr()), cls.c_ptr());
    TRACE("get_implied_equalities", tout << "after checking assumptions...\n" << Z3_context_to_string(m_context) << "\n";);
    m_last_check_result = result;
    
    m_out << ";Implied Equality Classes: ";
    for (unsigned i = 0; i < cls.size(); ++i) {
        m_out << cls[i] << " ";
    }
    m_out << "\n";

    m_out.flush();
    
    return true;    
}


bool z3_solver::parse_check_assumptions()
{
    expr_ref_vector args(m_manager);    
    CHECK(parse_asts<expr>(args, expr_coerce()));
    CHECK(parse_eol());

    if (!m_context) {
        return true;
    }

    Z3_model m = 0;
    
    Z3_ast pr  = 0;

    TRACE("check_assumptions", tout << "checking assumptions...\n" << Z3_context_to_string(m_context) << "\n";);
    Z3_lbool result = Z3_check_assumptions(m_context, args.size(), reinterpret_cast<Z3_ast*>(args.c_ptr()), &m, &pr, 0, 0);
    TRACE("check_assumptions", tout << "after checking assumptions...\n" << Z3_context_to_string(m_context) << "\n";);
    m_last_check_result = result;
    
    // display the model.

    if (m && m_params.m_model) {
        char const* md = Z3_model_to_string(m_context, m);
        if (md) {
            m_out << md;
        }
    }
    if (m) {
        Z3_del_model(m_context, m);
    }

    if (result == Z3_L_FALSE && pr != 0 && m_params.m_display_proof) {
        m_out << mk_ll_pp(reinterpret_cast<ast*>(pr), m_manager, true, false);
    }

    switch(result) {
    case l_false: m_out << "unsat\n"; break;
    case l_true: m_out << "sat\n"; break;
    case l_undef: m_out << "unknown\n"; break;
    }
    m_out.flush();

    dump_smtlib_benchmark(args.size(), args.c_ptr(), result);
    
    return true;
}

bool z3_solver::parse_dbg(bool expected_sat) {
    CHECK(parse_eol());
    if (m_last_check_result == Z3_L_FALSE && expected_sat) {
        m_out << "!!!!!!!!BUG FOUND!!!!!!!!!\n";
        throw z3_error(ERR_UNSOUNDNESS);
    }
    if (m_last_check_result == Z3_L_TRUE && !expected_sat) {
        m_out << "!!!!!!!!BUG FOUND!!!!!!!!!\n";
        throw z3_error(ERR_INCOMPLETENESS);
    } 
    if (m_last_check_result == Z3_L_UNDEF) {
        throw z3_error(ERR_UNKNOWN_RESULT);
    }
    return true;
}

bool z3_solver::parse_push()
{
    CHECK(parse_eol());
    if (m_context) {
        Z3_push(m_context);
    }
    m_pinned_lim.push_back(m_pinned.size());
    m_assumptions_lim.push_back(m_assumptions.size());
    return true;
}


bool z3_solver::parse_pop()
{
    CHECK(parse_eol());
    if (m_context) {
        Z3_pop(m_context, 1);
    }
    m_pinned.resize(m_pinned_lim.back());
    m_pinned_lim.pop_back();
    m_assumptions.resize(m_assumptions_lim.back());
    m_assumptions_lim.pop_back();
    return true;
}


bool z3_solver::parse_reset()
{
    CHECK(parse_eol());
    if (m_context) {
        Z3_del_context(m_context);
        Z3_config m_config = 0; // TBD.
        m_context = Z3_mk_context(m_config);
    }
    return true;
}

bool z3_solver::parse_echo()
{
    CHECK(parse_eol());
    // TBD
    return true;
}

bool z3_solver::parse_version()
{
    unsigned major, minor;
    CHECK(parse_unsigned(major));
    CHECK(parse_unsigned(minor));
    CHECK(next_token()); // build date
    CHECK(next_token()); // revision
    CHECK(parse_eol());
    if (major != Z3_MAJOR_VERSION) {
        warning_msg("Parser is incompatible. Major version %d has changed to %d", major, Z3_MAJOR_VERSION);
        return false;
    }
    if (minor > Z3_MINOR_VERSION) {
        warning_msg("Parser is incompatible. Minor version %d of parser is younger than %d", Z3_MINOR_VERSION, minor);
        return false;
    }
    return true;
}


bool z3_solver::parse_solver()
{
    std::string s;
    const char * str;
    s = m_string;
    CHECK(next_token());
    CHECK(parse_eol());
    str = s.c_str();
#if 0
    if (!m_solver) {

    }
    else if (strcmp(str,"LIA") == 0) {
        m_solver->register_arith(unmanaged_wrapper::LIA);
    }
    else if (strcmp(str,"LRA") == 0) {
        m_solver->register_arith(unmanaged_wrapper::MIA);
    }
    else if (strcmp(str,"BV") == 0) {
        m_solver->register_bv();
    }
#endif 
    return true;
}

bool z3_solver::parse() 
{
    next_token();
    bool ok = true;
    while (ok) {
        switch(parse_kind()) {
        case T_NUM:
            ok = parse_numeral();
            break;
        case T_VAR:
            ok = parse_var();
            break;
        case T_DEC:
            ok = parse_func_decl();
            break;
        case T_FUNCTION_CONST:
            ok = parse_const();
            break;
        case T_GET_IMPLIED_EQUALITIES:
            ok = parse_get_implied_equalities();
            break;
        case T_NULLARY_CONST:
            ok = parse_nullary_const();
            break;
        case T_BUILTIN_CONST:
            ok = parse_builtin_const();
            break;
        case T_TY:
            ok = parse_type();
            break;
        case T_TYPE:
            ok = parse_type_new();
            break;
        case T_QUA:
            ok = parse_quantifier();
            break;
        case T_LAB:
            ok = parse_label();
            break;
        case T_PAT:
            ok = parse_pattern();
            break;
        case T_ASSERT:
            ok = parse_assert();
            break;
        case T_SOLVER:
            ok = parse_solver();
            break;
        case T_SIMPLIFY:
            ok = parse_simplify();
            break;
        case T_PUSH:
            ok = parse_push();
            break;
        case T_CHECK:
            ok = parse_check();
            break;
        case T_CHECK_ASSUMPTIONS:
            ok = parse_check_assumptions();
            break;
        case T_DBG_SAT:
            ok = parse_dbg(true);
            break;
        case T_DBG_UNSAT:
            ok = parse_dbg(false);
            break;
        case T_POP:
            ok = parse_pop();
            break;
        case T_RESET:
            ok = parse_reset();
            break;
        case T_COMMENT:
            ok = parse_comment();
            break;
        case T_ECHO:
            ok = parse_echo();
            break;
        case T_VERSION:
            ok = parse_version();
            break;
        case T_EOF:
            return true;
        case T_ERR:
            return false;
        case T_CTX:
            // [Leo]: this case is not handled.
            break;
        }
    }
    if (!ok) {
        warning_msg("line %d. error encountered", m_line);
    }
    return ok;
}

void z3_solver::display_statistics(std::ostream& out, bool istats)
{
    if (m_context) {
        if (istats) {
            Z3_display_istatistics(m_context, out);
        }
        else {
            Z3_display_statistics(m_context, out);
        }
    }
}

void z3_solver::add_id(symbol const& id, ast* n) {
    m_table.insert(id, n);
    m_pinned.push_back(n);
}

