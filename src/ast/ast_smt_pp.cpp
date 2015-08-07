/*++
Copyright (c) 2008 Microsoft Corporation

Module Name:

    ast_smt_pp.cpp

Abstract:

    Pretty printer of AST formulas as SMT benchmarks.

Author:

    Michal Moskal (micmo) 2008-04-09.
    Nikolaj Bjorner (nbjorner)

Revision History:


--*/

#include<sstream>
#include<iostream>
#include"ast_smt_pp.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"array_decl_plugin.h"
#include"datatype_decl_plugin.h"
#include"vector.h"
#include"for_each_ast.h"
#include"decl_collector.h"
#include"smt2_util.h"

// ---------------------------------------
// smt_renaming

static const char m_predef_names[][8] = {
    "=", ">=", "<=", "+", "-", "*", ">", "<", "!=", "or", "and", "implies", "not", "iff", "xor",
    "true", "false", "forall", "exists", "let", "flet"
};

symbol smt_renaming::fix_symbol(symbol s, int k) {
    std::ostringstream buffer;
    char const * data = s.is_numerical() ? "" : s.bare_str();
    
    if (data[0] && !data[1]) {
        switch (data[0]) {
        case '/': data = "op_div"; break;
        case '%': data = "op_mod"; break;
        default: break;
        }
    }
    
    if (k == 0 && *data) {
        if (s.is_numerical()) {
            return s;
        }
        if (is_special(data)) {
            return s;
        }
        if (all_is_legal(data)) {
            return s;
        }
    }
    
    if (s.is_numerical()) {
        buffer << s << k;
        return symbol(buffer.str().c_str());            
    }

    if (is_smt2_quoted_symbol(s)) {
        buffer << mk_smt2_quoted_symbol(s);
    }
    else {
        buffer << s;
    }
    if (k > 0) {
        buffer << k;
    }
    
    return symbol(buffer.str().c_str());
}

bool smt_renaming::is_legal(char c) {
    return c == '.' || c == '_' || c == '\'' 
        || c == '?' || c == '!' || isalnum(c);
}

bool smt_renaming::is_special(char const* s) {
    if (!s) return false;
    if (s[0] != '|') return false;
    ++s;
    while (*s) {
        if (s[0] == '|') {
            return (0 == s[1]);
        }
        ++s;
    }
    return false;
}

bool smt_renaming::is_numerical(char const* s) {
    while (*s) {
        if (!isdigit(*s)) {
            return false;
        }
        ++s;
    }
    return true;
}

bool smt_renaming::all_is_legal(char const* s) {
    if (!s) return false;
    if (is_numerical(s)) return false;
    while (*s) {
        if (!is_legal(*s)) return false;
        ++s;
    }
    return true;
}

smt_renaming::smt_renaming() {
    for (unsigned i = 0; i < ARRAYSIZE(m_predef_names); ++i) {
        symbol s(m_predef_names[i]);
        m_translate.insert(s, s);
        m_rev_translate.insert(s, s);
    }
}


symbol smt_renaming::get_symbol(symbol s0) {
    symbol s;
    if (m_translate.find(s0, s)) {
        return s;
    }
    
    int k = 0;
    do {
        s = fix_symbol(s0, k++);
    } 
    while (m_rev_translate.contains(s));
    m_translate.insert(s0, s);
    m_rev_translate.insert(s, s0);
    return s;
}

// ---------------------------------------
// smt_printer

class smt_printer {
    std::ostream&    m_out;
    ast_manager&     m_manager;
    ptr_vector<quantifier>& m_qlists;
    smt_renaming&    m_renaming;
    unsigned         m_indent;
    unsigned         m_num_var_names;
    char const* const* m_var_names;
    ptr_vector<expr> m_todo;
    ast_mark         m_mark;
    unsigned         m_num_lets;
    arith_util       m_autil;
    bv_util          m_bvutil;
    family_id        m_basic_fid;
    family_id        m_bv_fid;
    family_id        m_arith_fid;
    family_id        m_array_fid;
    family_id        m_dt_fid;
    family_id        m_label_fid;
    symbol           m_logic;
    symbol           m_AUFLIRA;
    bool             m_no_lets;
    bool             m_is_smt2;
    bool             m_simplify_implies;
    expr*            m_top;

    bool is_bool(sort* s) {
        return 
            m_basic_fid == s->get_family_id() &&
            s->get_decl_kind() == BOOL_SORT;
    }

    bool is_bool(expr* e) {
        return is_bool(m_manager.get_sort(e));
    }

    bool is_proof(sort* s) {
        return 
            m_basic_fid == s->get_family_id() &&
            s->get_decl_kind() == PROOF_SORT;        
    }

    bool is_proof(expr* e) { 
        return is_proof(m_manager.get_sort(e)); 
    }

    void pp_id(expr* n) {
         if (m_is_smt2) {
             m_out << (is_bool(n)?"$x":(is_proof(n)?"@x":"?x")) << n->get_id();
         }
         else {
             m_out << (is_bool(n)?"$x":"?x") << n->get_id();
         }
    }

    void pp_decl(func_decl* d) {
        symbol sym = m_renaming.get_symbol(d->get_name());
        if (d->get_family_id() == m_dt_fid) {
            m_out << sym;
        }
        else if (m_manager.is_ite(d)) {
            if (!m_is_smt2 && is_bool(d->get_range())) {
                m_out << "if_then_else";
            }
            else {
                m_out << "ite";
            }
        }
        else if (!m_is_smt2 && m_manager.is_implies(d)) {
            m_out << "implies";
        }
        else if (m_is_smt2 && m_manager.is_iff(d)) {
            m_out << "=";
        }
        else if (m_is_smt2 && m_manager.is_implies(d)) {
            m_out << "=>";
        }
        else if (m_is_smt2 && is_decl_of(d, m_arith_fid, OP_UMINUS)) {
            m_out << "-";
        }
        else {
            visit_params(false, sym, d->get_num_parameters(), d->get_parameters());
        }
        m_out << " ";
    }

    bool is_sort_param(unsigned num_params, parameter const* params) {
        return 
            num_params == 1 && 
            params[0].is_ast() &&
            is_sort(params[0].get_ast());
    }

    void visit_params(bool is_sort_symbol, symbol const& sym, unsigned num_params, parameter const* params) {
        if (0 == num_params) {
            m_out << sym;
            return;
        }

        if (m_is_smt2) {
            if (is_sort_symbol && sym != symbol("BitVec")) {
                m_out << "(" << sym << " ";                
            }
            else if (!is_sort_symbol && is_sort_param(num_params, params)) {
                m_out << "(as " << sym << " ";
            }
            else {
                m_out << "(_ " << sym << " ";                
            }
        }
        else {
            m_out << sym << "[";
        }

        for (unsigned i = 0; i < num_params; ++i) {
            parameter const& p = params[i];
            if (p.is_ast()) {
                if (is_sort(p.get_ast())) {
                    visit_sort(to_sort(p.get_ast()));
                }
                else if (is_expr(p.get_ast())) {
                    pp_expr(to_expr(p.get_ast()));
                }
                else if (is_func_decl(p.get_ast())) {
                    pp_decl(to_func_decl(p.get_ast()));
                }
                else {
                    m_out << "#" << p.get_ast()->get_id();
                }
            }
            else {
                m_out << p;
            }
            if (i + 1 < num_params) {
                if (m_is_smt2) {
                    m_out << " ";
                }
                else {
                    m_out << ": ";
                }
            }
        }
        if (m_is_smt2) {
            m_out << ")";
        }
        else {
            m_out << "]";
        }
    }
    
    bool is_auflira() const {
        return m_logic == m_AUFLIRA;
    }

    void visit_sort(sort* s, bool bool2int = false) {
        symbol sym;  
        if (bool2int && is_bool(s) && !m_is_smt2) {
            sym = symbol("Int");
        } else if (s->is_sort_of(m_bv_fid, BV_SORT)) {
            sym = symbol("BitVec");
        }
        else if (s->is_sort_of(m_arith_fid, REAL_SORT)) {
            sym = s->get_name();
        }
        else if (m_manager.is_bool(s)) {
            sym = symbol("Bool");
        }
        else if (s->is_sort_of(m_arith_fid, INT_SORT)) {
            sym = s->get_name();
        }
        else if (s->is_sort_of(m_array_fid, ARRAY_SORT) && m_is_smt2) {
            sym = "Array";
        }
        else if (s->is_sort_of(m_array_fid, ARRAY_SORT) && !m_is_smt2) {            
            unsigned num_params = s->get_num_parameters();
            SASSERT(num_params >= 2);
            if (is_auflira()) {
                sort* rng = to_sort(s->get_parameter(1).get_ast());
                if (rng->get_family_id() == m_array_fid) {
                    m_out << "Array2";
                }
                else {
                    m_out << "Array1";
                }
                return;
            }
            sort* s1 = to_sort(s->get_parameter(0).get_ast());
            sort* s2 = to_sort(s->get_parameter(1).get_ast());
            if (num_params == 2 && 
                s1->is_sort_of(m_bv_fid, BV_SORT) &&
                s2->is_sort_of(m_bv_fid, BV_SORT)) {
                m_out << "Array";
                m_out << "[" << s1->get_parameter(0).get_int();
                m_out << ":" << s2->get_parameter(0).get_int() << "]";                
                return;
            }
            m_out << "(Array ";
            for (unsigned i = 0; i < num_params; ++i) {
                visit_sort(to_sort(s->get_parameter(i).get_ast()));
                if (i + 1 < num_params) {
                    m_out << " ";
                }
            }
            m_out << ")";
            return;
        }
        else if (s->is_sort_of(m_dt_fid, DATATYPE_SORT)) {
            m_out << m_renaming.get_symbol(s->get_name());
            return;
        }
        else {
            sym = m_renaming.get_symbol(s->get_name());
        }
        visit_params(true, sym, s->get_num_parameters(), s->get_parameters());
    }

    void display_rational(rational const & r, bool is_int) {
        bool d = !is_int;
        if (r.is_int()) {
            m_out << r << (d ? ".0" : "");
        }
        else {
            m_out << "(/ " << numerator(r) << (d ? ".0" : "") << " " << denominator(r) << (d ? ".0" : "") << ")";
        }
    }

    
    void pp_arg(expr *arg, app *parent)
    {
        if (!m_is_smt2 && is_bool(arg) && is_var(arg) && parent->get_family_id() == m_basic_fid) {
            m_out << "(not (= ";
            pp_marked_expr(arg);
            m_out << " 0))";
        } else if (!m_is_smt2 && is_bool(arg) && !is_var(arg) &&
            parent->get_family_id() != m_basic_fid && 
            parent->get_family_id() != m_dt_fid) {

            m_out << "(ite ";
            pp_marked_expr(arg);
            m_out << " 1 0)";
        } else {
            pp_marked_expr(arg);
        }
    }

    void visit_app(app* n) {
        rational val;
        bool is_int, pos;
        buffer<symbol> names;
        unsigned bv_size;
        unsigned num_args = n->get_num_args();
        func_decl* decl = n->get_decl();
        if (m_autil.is_numeral(n, val, is_int)) {
            if (val.is_neg()) {
                val.neg();
                if (m_is_smt2) {
                    m_out << "(- ";
                }
                else {
                    m_out << "(~ ";
                }
                display_rational(val, is_int);
                m_out << ")";
            }
            else {
                display_rational(val, is_int);
            }
        }
        else if (m_bvutil.is_numeral(n, val, bv_size)) {
            if (m_is_smt2) {
                m_out << "(_ bv" << val << " " << bv_size << ")";
            }
            else {
                m_out << "bv" << val << "[" << bv_size << "]";
            }
        }
        else if (m_bvutil.is_bit2bool(n)) {            
            unsigned bit = n->get_decl()->get_parameter(0).get_int();
            if (m_is_smt2) {
                m_out << "(= ((_ extract " << bit << " " << bit << ") ";
                pp_marked_expr(n->get_arg(0));
                m_out << ") (_ bv1 1))";
            }
            else {
                m_out << "(= (extract[" << bit << ":" << bit << "] ";
                pp_marked_expr(n->get_arg(0));
                m_out << ") bv1[1])";
            }
        }
        else if (m_manager.is_label(n, pos, names) && names.size() >= 1) {
            if (m_is_smt2) {
                m_out << "(! "; 
                pp_marked_expr(n->get_arg(0));
                m_out << (pos?":lblpos":":lblneg") << " " << m_renaming.get_symbol(names[0]) << ")";
            }
            else {
                m_out << "(" << (pos?"lblpos":"lblneg") << " " << m_renaming.get_symbol(names[0]) << " ";
                expr* ch = n->get_arg(0);
                pp_marked_expr(ch);            
                m_out << ")";
            }
        }
        else if (m_manager.is_label_lit(n, names) && names.size() >= 1) {
            if (m_is_smt2) {
                m_out << "(! true :lblpos " << m_renaming.get_symbol(names[0]) << ")";
            }
            else {
                m_out << "(lblpos " << m_renaming.get_symbol(names[0]) << " true )";
            }
        }
        else if (num_args == 0) {
            if (decl->private_parameters()) {
                m_out << m_renaming.get_symbol(decl->get_name());
            }
            else {
                symbol sym = m_renaming.get_symbol(decl->get_name());
                visit_params(false, sym, decl->get_num_parameters(), decl->get_parameters());
            }
        }
        else if (num_args == 1 && n->get_family_id() == m_label_fid) {
            expr* ch = n->get_arg(0);
            pp_marked_expr(ch);
        }
        else if (m_simplify_implies && m_manager.is_implies(decl) && m_manager.is_implies(n->get_arg(1))) {
            expr *curr = n;
            expr *arg;
            m_out << "(implies (and";
            while (m_manager.is_implies(curr)) {
                arg = to_app(curr)->get_arg(0);

                m_out << " ";
                pp_arg(arg, n);
                curr = to_app(curr)->get_arg(1);
            }
            m_out << ") ";
            pp_arg(curr, n);
            m_out << ")";

        } else if (m_manager.is_distinct(decl)) {
            ptr_vector<expr> args(num_args, n->get_args());
            unsigned         idx = 0;
            m_out << "(and";
            while (true) {
                while (idx < args.size() && !args[idx])
                    idx++;
                if (idx >= args.size()) break;
                sort *   s = m_manager.get_sort(args[idx]);
                unsigned next = idx + 1;

                // check if there is only a single one
                while (next < args.size() && (!args[next] || m_manager.get_sort(args[next]) != s))
                    next++;
                if (next >= args.size()) {
                    args[idx] = 0;
                    // if so, skip it
                    continue;
                }

                // otherwise print all of the relevant sort
                m_out << " (distinct";
                for (unsigned i = idx; i < args.size(); ++i) {
                    if (args[i] && s == m_manager.get_sort(args[i])) {
                        m_out << " ";
                        pp_marked_expr(args[i]);
                        args[i] = 0;
                    }
                }
                m_out << ")";
            }
            m_out << " true)";
        }
        else {
            m_out << "(";
            pp_decl(decl);
            for (unsigned i = 0; i < num_args; ++i) {
                pp_arg(n->get_arg(i), n);
                if (i + 1 < num_args) {
                    m_out << " ";
                }
            }
            m_out << ")";                
        }
    }

    void print_no_lets(expr *e)
    {
        smt_printer p(m_out, m_manager, m_qlists, m_renaming, m_logic, true, m_simplify_implies, m_is_smt2, m_indent, m_num_var_names, m_var_names); 
        p(e);
    }

    void print_bound(symbol const& name) {
        if (!m_is_smt2 && (name.is_numerical() || '?' != name.bare_str()[0])) {
            m_out << "?";
        }
        m_out << name;
    }

    void visit_quantifier(quantifier* q) {
        m_qlists.push_back(q);        

        m_out << "(";
        if (q->is_forall()) {
            m_out << "forall ";
        }
        else {
            m_out << "exists ";
        }
        if (m_is_smt2) {
            m_out << "(";
        }
        for (unsigned i = 0; i < q->get_num_decls(); ++i) {
            sort* s = q->get_decl_sort(i);
            m_out << "(";
            print_bound(m_renaming.get_symbol(q->get_decl_name(i)));
            m_out << " ";
            visit_sort(s, true);
            m_out << ") ";
        }
        if (m_is_smt2) {
            m_out << ")";
        }
        
        if (m_is_smt2 && (q->get_num_patterns() > 0 || q->get_qid() != symbol::null)) {
            m_out << "(! ";
        }
        {
            smt_printer p(m_out, m_manager, m_qlists, m_renaming, m_logic, false, m_is_smt2, m_simplify_implies, m_indent, m_num_var_names, m_var_names);        
            p(q->get_expr());
        }

        for (unsigned i = 0; i < q->get_num_patterns(); ++i) {
            app *pat = reinterpret_cast<app*> (q->get_pattern(i));

            if (pat->get_num_args() == 1 && is_app(pat->get_arg(0))) {
                app *app = to_app(pat->get_arg(0));
                if (app->get_num_args() == 1 && app->get_decl()->get_name().str() == "sk_hack") {
                    /*
                    m_out << " :ex_act { ";
                    print_no_lets(app->get_arg(0));
                    m_out << "}";
                    */
                    continue;
                }
            }

            if (m_is_smt2) {
                m_out << " :pattern ( ";
            }
            else {
                m_out << " :pat { ";
            }
            for (unsigned j = 0; j < pat->get_num_args(); ++j) {
                print_no_lets(pat->get_arg(j));
                m_out << " ";
            }
            if (m_is_smt2) {
                m_out << ")";
            }
            else {
                m_out << "}";
            }
        }

        if (q->get_qid() != symbol::null)
            m_out << " :qid " << q->get_qid();

        if (m_is_smt2 && (q->get_num_patterns() > 0 || q->get_qid() != symbol::null)) {
            m_out << ")";
        }
        m_out << ")";
        newline();
        m_qlists.pop_back();
    }

    void newline() {
        unsigned i = m_indent;
        m_out << "\n";
        while (i > 0) { m_out << " "; --i; }       
    }

    void visit_var(var* v) {
        unsigned idx = v->get_idx();
        for (unsigned i = m_qlists.size(); ; --i) {
            if (i == 0) {
                break;
            }
            quantifier* q = m_qlists[i-1];
            unsigned num_decls = q->get_num_decls();
            if (idx < num_decls) {
                unsigned offs = num_decls-idx-1;
                symbol name = m_renaming.get_symbol(q->get_decl_name(offs));
                print_bound(name);
                return;
            }
            idx -= num_decls;
        }
        if (idx < m_num_var_names) {
            m_out << m_var_names[m_num_var_names - idx - 1];
        }
        else {
            m_out << "?" << idx;
        }
    }

    void pp_marked_expr(expr* n) {
        if (m_mark.is_marked(n)) {
            pp_id(n);
        }
        else {
            pp_expr(n);
        }
    }

    void pp_expr(expr* n) {
        switch(n->get_kind()) {
        case AST_QUANTIFIER:
            visit_quantifier(to_quantifier(n));
            break;
        case AST_APP: 
            visit_app(to_app(n));
            break;
        case AST_VAR: 
            visit_var(to_var(n));
            break;
        default:
            UNREACHABLE();
        }        
    }

    void visit_expr(expr* n) {
        if (m_is_smt2) {
            m_out << "(let ((";
        }
        else if (is_bool(n)) {
            m_out << "(flet (";
        }
        else {
            m_out << "(let (";
        }
        pp_id(n);
        m_out << " ";
        pp_expr(n);
        if (m_is_smt2) {
            m_out << ")";
        }
        m_out << ")";
        newline();
    }  

    bool is_unit(expr* n) {
        if (n->get_ref_count() <= 2 && is_small(n)) {
            return true;
        }
        if (n == m_top) {
            return true;
        }
        switch(n->get_kind()) {
        case AST_VAR: 
            return true;
        case AST_APP: 
            return to_app(n)->get_num_args() == 0;
        default:
            return false;
        }
    }

    static const unsigned m_line_length = 80;

    bool is_small(expr* n) {
        unsigned sz = 0;
        return is_small(n, sz);
    }

    bool is_small(expr* n, unsigned& sz) {
        if (sz > m_line_length) {
            return false;
        }
        if (m_mark.is_marked(n)) {
            sz += 5;
            return sz <= m_line_length;
        }
        switch(n->get_kind()) {
        case AST_QUANTIFIER: 
            return false;
        case AST_VAR: 
            sz += 5;
            return sz <= m_line_length;
        case AST_APP: {
            app* a = to_app(n);
            func_decl* d = a->get_decl();
            symbol const& s = d->get_name();
            if (s.is_numerical()) {
                sz += 4;
            }
            if (s.is_numerical()) {
                sz += 7;
            }
            else {
                sz += 3 + static_cast<unsigned>(strlen(s.bare_str()));
            }
            for (unsigned i = 0; i < a->get_num_args() && sz <= m_line_length; ++i) {
                sz += 1;
                if (!is_small(a->get_arg(i), sz)) {
                    return false;
                }
            }
            return sz <= m_line_length;
        }
        default:
            return false;
        }        
    }        

    bool visit_children(expr* n) {
        unsigned todo_size = m_todo.size();
        switch(n->get_kind()) {
        case AST_QUANTIFIER: 
        case AST_VAR: 
            break;
        case AST_APP: {
            app* a = to_app(n);
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                expr* ch = a->get_arg(i);
                if (!is_unit(ch) && !m_mark.is_marked(ch)) {
                    m_todo.push_back(ch);
                }
            }
            break;
        }
        default:
            UNREACHABLE();
            break;
        }
        bool all_visited = todo_size == m_todo.size();
        return all_visited;
    }

public:
    smt_printer(std::ostream& out, ast_manager& m, ptr_vector<quantifier>& ql, smt_renaming& rn, 
                symbol logic, bool no_lets, bool is_smt2, bool simplify_implies, unsigned indent, unsigned num_var_names = 0, char const* const* var_names = 0) :
        m_out(out), 
        m_manager(m),
        m_qlists(ql),
        m_renaming(rn),
        m_indent(indent),
        m_num_var_names(num_var_names),
        m_var_names(var_names),
        m_num_lets(0),
        m_autil(m),
        m_bvutil(m),
        m_logic(logic),
        m_AUFLIRA("AUFLIRA"),
        // It's much easier to read those testcases with that.
        m_no_lets(no_lets),
        m_is_smt2(is_smt2),
        m_simplify_implies(simplify_implies)
    {
        m_basic_fid = m.get_basic_family_id();
        m_label_fid = m.mk_family_id("label");
        m_bv_fid    = m.mk_family_id("bv");
        m_arith_fid = m.mk_family_id("arith");
        m_array_fid = m.mk_family_id("array");
        m_dt_fid    = m.mk_family_id("datatype");
    }
    
    void operator()(expr* n) {
        m_top = n;
        if (!m_no_lets) {
            switch(n->get_kind()) {
            case AST_APP:
                for (unsigned i = 0; i < to_app(n)->get_num_args(); ++i) {
                    m_todo.push_back(to_app(n)->get_arg(i));
                }
                break;
            // Don't do this for quantifiers -- they need to have the body be 
            // visited when the m_qlist contains the relevant quantifier.
            default:
                break;
            }
        }

        while (!m_todo.empty()) {
            expr* m = m_todo.back();
            if (m_mark.is_marked(m)) {
                m_todo.pop_back();
            }
            else if (is_unit(m)) {
                m_todo.pop_back();
            }
            else if (visit_children(m)) {
                m_todo.pop_back();
                m_mark.mark(m, true);
                visit_expr(m);
                ++m_num_lets;
            }
        }

        pp_marked_expr(n);
        for (unsigned i = 0; i < m_num_lets; ++i) {
            m_out << ")";       
        }
        m_mark.reset();
        m_num_lets = 0;
        m_top = 0;
    }

    void pp_dt(ast_mark& mark, sort* s) {
        SASSERT(s->is_sort_of(m_dt_fid, DATATYPE_SORT));
        datatype_util util(m_manager);
        ptr_vector<func_decl> const* decls;
        ptr_vector<sort> rec_sorts;

        rec_sorts.push_back(s);        
        mark.mark(s, true);

        // collect siblings and sorts that have not already been printed.
        for (unsigned h = 0; h < rec_sorts.size(); ++h) {
            s = rec_sorts[h];
            decls = util.get_datatype_constructors(s);

            for (unsigned i = 0; i < decls->size(); ++i) {
                func_decl* f = (*decls)[i];
                for (unsigned j = 0; j < f->get_arity(); ++j) {
                    sort* s2 = f->get_domain(j);
                    if (!mark.is_marked(s2)) {
                        if (m_manager.is_uninterp(s2)) {
                            pp_sort_decl(mark, s2);
                        }
                        else if (!util.is_datatype(s2)) {
                            // skip
                        }
                        else if (util.are_siblings(s, s2)) {
                            rec_sorts.push_back(s2);
                            mark.mark(s2, true);
                        }
                        else {
                            pp_sort_decl(mark, s2);
                        }                        
                    }
                }
            }
        }

        if (m_is_smt2) {
            // TBD: datatypes may be declared parametrically. 
            // get access to parametric generalization, or print
            // monomorphic specialization with a tag that gets reused at use-point.
            m_out << "(declare-datatypes () (";
        }
        else {
            m_out << ":datatypes (";        
        }
        for (unsigned si = 0; si < rec_sorts.size(); ++si) {
            s = rec_sorts[si];
            m_out << "(";
            m_out << m_renaming.get_symbol(s->get_name());
            m_out << " ";
            decls = util.get_datatype_constructors(s);

            for (unsigned i = 0; i < decls->size(); ++i) {
                func_decl* f = (*decls)[i];            
                ptr_vector<func_decl> const& accs = *util.get_constructor_accessors(f);
                if (m_is_smt2 || accs.size() > 0) {
                    m_out << "(";
                }
                m_out << m_renaming.get_symbol(f->get_name());
                if (!accs.empty() || !m_is_smt2) {
                    m_out << " ";
                }
                for (unsigned j = 0; j < accs.size(); ++j) {                
                    func_decl* a = accs[j];
                    m_out << "(" << m_renaming.get_symbol(a->get_name()) << " ";
                    visit_sort(a->get_range());
                    m_out << ")";
                    if (j + 1 < accs.size()) m_out << " ";
                }
                if (m_is_smt2 || accs.size() > 0) {
                    m_out << ")";
                    if (i + 1 < decls->size()) {
                        m_out << " ";
                    }
                }
            }
            m_out << ")";
            if (si + 1 < rec_sorts.size()) {
                m_out << " ";
            }
        }
        if (m_is_smt2) {
            m_out << ")";
        }
        m_out << ")";
        newline();
    }


    void pp_sort_decl(ast_mark& mark, sort* s) {
        if (mark.is_marked(s)) {
            return;
        }
        if (s->is_sort_of(m_dt_fid, DATATYPE_SORT)) {
            pp_dt(mark, s);
        }
        else {
            if (m_is_smt2) {
                m_out << "(declare-sort ";
            }
            else {
                m_out << ":extrasorts (";
            }
            visit_sort(s);
            m_out << ")";
            newline();
        }
        mark.mark(s, true);
    }

    void operator()(sort* s) {
        ast_mark mark;
        pp_sort_decl(mark, s);
    }

    void operator()(func_decl* d) {
        if (m_is_smt2) {
            m_out << "(declare-fun ";
            pp_decl(d);
            m_out << "(";
            for (unsigned i = 0; i < d->get_arity(); ++i) {
                if (i > 0) m_out << " ";
                visit_sort(d->get_domain(i), true);
            }
            m_out << ") ";
            visit_sort(d->get_range());
            m_out << ")";
        }
        else {
            m_out << "(";
            pp_decl(d);
            for (unsigned i = 0; i < d->get_arity(); ++i) {
                m_out << " ";
                visit_sort(d->get_domain(i), true);
            }
            m_out << " ";
            visit_sort(d->get_range());
            m_out << ")";
        }
    }

    void visit_pred(func_decl* d) {
        m_out << "(";
        pp_decl(d);
        for (unsigned i = 0; i < d->get_arity(); ++i) {
            m_out << " ";
            visit_sort(d->get_domain(i), true);
        }
        m_out << ")";
    }
};


// ---------------------------------------
// ast_smt_pp:

ast_smt_pp::ast_smt_pp(ast_manager& m):
    m_manager(m),
    m_assumptions(m),
    m_assumptions_star(m),
    m_benchmark_name(),
    m_source_info(),
    m_status("unknown"),
    m_category(),
    m_logic(),
    m_dt_fid(m.mk_family_id("datatype")),
    m_is_declared(&m_is_declared_default),
    m_simplify_implies(true)
{}


void ast_smt_pp::display_expr(std::ostream& strm, expr* n) {
    ptr_vector<quantifier> ql;
    smt_renaming rn;
    smt_printer p(strm, m_manager, ql, rn, m_logic, false, false, m_simplify_implies, 0);
    p(n);
}

void ast_smt_pp::display_expr_smt2(std::ostream& strm, expr* n, unsigned indent, unsigned num_var_names, char const* const* var_names) {
    ptr_vector<quantifier> ql;
    smt_renaming rn;
    smt_printer p(strm, m_manager, ql, rn, m_logic, false, true, m_simplify_implies, indent, num_var_names, var_names);
    p(n);
}

void ast_smt_pp::display_ast_smt2(std::ostream& strm, ast* a, unsigned indent, unsigned num_var_names, char const* const* var_names) {
    ptr_vector<quantifier> ql;
    smt_renaming rn;
    smt_printer p(strm, m_manager, ql, rn, m_logic, false, true, m_simplify_implies, indent, num_var_names, var_names);
    if (is_expr(a)) {
        p(to_expr(a));
    }
    else if (is_func_decl(a)) {
        p(to_func_decl(a));
    }
    else {
        SASSERT(is_sort(a));
        p(to_sort(a));
    }
}


void ast_smt_pp::display_smt2(std::ostream& strm, expr* n) {
    ptr_vector<quantifier> ql;
    ast_manager& m = m_manager;
    decl_collector decls(m);
    smt_renaming rn;    

    for (unsigned i = 0; i < m_assumptions.size(); ++i) {
        decls.visit(m_assumptions[i].get());
    }
    for (unsigned i = 0; i < m_assumptions_star.size(); ++i) {
        decls.visit(m_assumptions_star[i].get());
    }
    decls.visit(n);    

    if (m.is_proof(n)) {
        strm << "(";
    }
    if (m_benchmark_name != symbol::null) {
        strm << "; " << m_benchmark_name << "\n";
    }
    if (m_source_info != symbol::null && m_source_info != symbol("")) {
        strm << "; :source { " << m_source_info << " }\n";
    }    
    if (m.is_bool(n)) {
        strm << "(set-info :status " << m_status << ")\n";
    }
    if (m_category != symbol::null && m_category != symbol("")) {
        strm << "; :category { " << m_category << " }\n";
    }
    if (m_logic != symbol::null && m_logic != symbol("")) {
        strm << "(set-logic " << m_logic << ")\n";
    }
    if (m_attributes.size() > 0) {
        strm << "; " << m_attributes.c_str();
    }

    ast_mark sort_mark;
    for (unsigned i = 0; i < decls.get_num_sorts(); ++i) {
        sort* s = decls.get_sorts()[i];
        if (!(*m_is_declared)(s)) {
            smt_printer p(strm, m, ql, rn, m_logic, true, true, m_simplify_implies, 0);
            p.pp_sort_decl(sort_mark, s);
        }        
    }

    for (unsigned i = 0; i < decls.get_num_decls(); ++i) {
        func_decl* d = decls.get_func_decls()[i];
        if (!(*m_is_declared)(d)) {
            smt_printer p(strm, m, ql, rn, m_logic, true, true, m_simplify_implies, 0);
            p(d);
            strm << "\n";
        }
    }

    for (unsigned i = 0; i < decls.get_num_preds(); ++i) {
        func_decl* d = decls.get_pred_decls()[i];
        if (!(*m_is_declared)(d)) {
            smt_printer p(strm, m, ql, rn, m_logic, true, true, m_simplify_implies, 0);
            p(d);
            strm << "\n";
        }
    }

    for (unsigned i = 0; i < m_assumptions.size(); ++i) {
        smt_printer p(strm, m, ql, rn, m_logic, false, true, m_simplify_implies, 1);
        strm << "(assert\n ";
        p(m_assumptions[i].get());
        strm << ")\n";
    }

    for (unsigned i = 0; i < m_assumptions_star.size(); ++i) {        
        smt_printer p(strm, m, ql, rn, m_logic, false, true, m_simplify_implies, 1);
        strm << "(assert\n ";
        p(m_assumptions_star[i].get());
        strm << ")\n";
    }

    smt_printer p(strm, m, ql, rn, m_logic, false, true, m_simplify_implies, 0);
    if (m.is_bool(n)) {
        if (!m.is_true(n)) {
            strm << "(assert\n ";
            p(n);
            strm << ")\n";
        }
        strm << "(check-sat)\n";
    }
    else if (m.is_proof(n)) {
        strm << "(proof\n";
        p(n);
        strm << "))\n";
    }
    else {
        p(n);
    }    
}

void ast_smt_pp::display(std::ostream& strm, expr* n) {
    ptr_vector<quantifier> ql;
    decl_collector decls(m_manager);
    smt_renaming rn;    

    for (unsigned i = 0; i < m_assumptions.size(); ++i) {
        decls.visit(m_assumptions[i].get());
    }
    for (unsigned i = 0; i < m_assumptions_star.size(); ++i) {
        decls.visit(m_assumptions_star[i].get());
    }
    decls.visit(n);
    
    strm << "(benchmark ";

    if (m_benchmark_name != symbol::null) {
        strm << m_benchmark_name << "\n";
    }
    else {
        strm << "unnamed\n";
    }
    if (m_source_info != symbol::null && m_source_info != symbol("")) {
        strm << ":source { " << m_source_info << " }\n";
    }
    strm << ":status " << m_status << "\n";
    if (m_category != symbol::null && m_category != symbol("")) {
        strm << ":category { " << m_category << " }\n";
    }
    if (m_logic != symbol::null && m_logic != symbol("")) {
        strm << ":logic " << m_logic << "\n";
    }

    if (m_attributes.size() > 0) {
        strm << m_attributes.c_str();
    }

    ast_mark sort_mark;
    for (unsigned i = 0; i < decls.get_num_sorts(); ++i) {
        sort* s = decls.get_sorts()[i];
        if (!(*m_is_declared)(s)) {
            smt_printer p(strm, m_manager, ql, rn, m_logic, true, false, m_simplify_implies, 0);
            p.pp_sort_decl(sort_mark, s); 
        }       
    }

    for (unsigned i = 0; i < decls.get_num_decls(); ++i) {
        func_decl* d = decls.get_func_decls()[i];
        if (!(*m_is_declared)(d)) {
            strm << ":extrafuns (";
            smt_printer p(strm, m_manager, ql, rn, m_logic, true, false, m_simplify_implies, 0);
            p(d);
            strm << ")\n";
        }
    }

    for (unsigned i = 0; i < decls.get_num_preds(); ++i) {
        func_decl* d = decls.get_pred_decls()[i];
        if (!(*m_is_declared)(d)) {
            strm << ":extrapreds (";
            smt_printer p(strm, m_manager, ql, rn, m_logic, true, false, m_simplify_implies, 0);
            p.visit_pred(d);
            strm << ")\n";
        }
    }

    for (unsigned i = 0; i < m_assumptions.size(); ++i) {
        expr *    e = m_assumptions[i].get();
        strm << ":assumption\n";
        smt_printer p(strm, m_manager, ql, rn, m_logic, false, false, m_simplify_implies, 0);
        p(e);   
        strm << "\n";     
    }

    for (unsigned i = 0; i < m_assumptions_star.size(); ++i) {
        strm << ":assumption-core\n";
        smt_printer p(strm, m_manager, ql, rn, m_logic, false, false, m_simplify_implies, 0);
        p(m_assumptions_star[i].get());        
        strm << "\n";
    }

    {
        strm << ":formula\n";
        smt_printer p(strm, m_manager, ql, rn, m_logic, false, false, m_simplify_implies, 0);
        p(n);
        strm << "\n";
    }
    strm << ")\n";
}
