/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ast_pp.cpp

Abstract:

    Expression DAG pretty printer

Author:

    Leonardo de Moura 2008-01-20.

Revision History:

--*/

#include"ast_pp.h"
#include"pp.h"
#include"obj_pair_hashtable.h"
#include"ast_ll_pp.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"datatype_decl_plugin.h"
#include"dl_decl_plugin.h"
#include"ast_list.h"
#include<sstream>

using namespace format_ns;

mk_pp::mk_pp(ast * a, ast_manager & m, pp_params const & p, unsigned indent, unsigned num_var_names, char const * const * var_names):
    m_ast(a),
    m_manager(m),
    m_params(p),
    m_indent(indent),
    m_num_var_names(num_var_names),
    m_var_names(var_names) {
}

mk_pp::mk_pp(ast * a, ast_manager & m, unsigned indent, unsigned num_var_names, char const * const * var_names):
    m_ast(a),
    m_manager(m),
    m_params(get_pp_default_params()),
    m_indent(indent),
    m_num_var_names(num_var_names),
    m_var_names(var_names) {
}

std::ostream & ast_pp(std::ostream & strm, ast * n, ast_manager & m) {
    return ast_pp(strm, n, m, get_pp_default_params());
}

struct pp_cache {
    typedef obj_pair_map<ast, quantifier_list, format *> cache;

    ast_manager &   m_manager;
    cache           m_cache;

    pp_cache(ast_manager & m):
        m_manager(m) {
    }

    ~pp_cache() {
        reset();
    }

    bool contains(ast * k1, quantifier_list * k2) const { return m_cache.contains(k1, k2); }

    void get(ast * k1, quantifier_list * k2, format * & r) const { m_cache.find(k1, k2, r); }

    void insert(ast * k1, quantifier_list * k2, format * f) { 
        SASSERT(!m_cache.contains(k1, k2));
        fm(m_manager).inc_ref(f);
        m_cache.insert(k1, k2, f);
    }
    
    void reset() {
        cache::iterator it  = m_cache.begin();
        cache::iterator end = m_cache.end();
        for (; it != end; ++it) {
            format * f = (*it).get_value();
            fm(m_manager).dec_ref(f);
        }
        m_cache.reset();
    }
};

class formatter {
    typedef quantifier_list_manager    qlist_manager;
    typedef quantifier_list_ref        qlist_ref;
    typedef quantifier_list_ref_vector qlist_ref_vector;
    pp_params const & m_params;
    ast_manager &     m_manager;
    qlist_manager     m_qlist_manager;
    pp_cache          m_cache;
    typedef std::pair<ast*, quantifier_list*> pp_entry;
    svector<pp_entry> m_todo;
    qlist_ref_vector  m_qlists;
    app_ref           m_nil;
    arith_util        m_autil;
    bv_util           m_bvutil;
    datatype_util     m_datatype_util;
    datalog::dl_decl_util m_dl_util;
    ptr_vector<sort>  m_datatypes;
    app_ref_vector    m_format_trail;
    ast_mark          m_visited_datatypes;
    unsigned          m_num_var_names;
    char const * const * m_var_names;

    struct symbol2format {
        ast_manager & m_manager;
        symbol2format(ast_manager & m):m_manager(m) {}
        format * operator()(symbol const & s) { 
            std::string str = s.str();
            return mk_string(m_manager, str.c_str());
        }
    };

    format * get_cached(ast * n, quantifier_list * qlist) {
        format * f = 0;
        if (is_sort(n)) {
            qlist = m_qlist_manager.mk_nil();
        }
        m_cache.get(n, qlist, f);
        SASSERT(f);
        return f;
    }

    void visit(ast * n, quantifier_list * qlist, bool & visited) {
        if (is_sort(n)) {
            qlist = m_qlist_manager.mk_nil();
        }
        if (!m_cache.contains(n, qlist)) {
            m_todo.push_back(pp_entry(n, qlist));
            visited = false;
        }
    }

    bool visit_children(ast * n, quantifier_list * qlist) {
        unsigned j;
        bool visited = true;
        switch (n->get_kind()) {
        case AST_FUNC_DECL: {
            func_decl* f = to_func_decl(n);
            j = f->get_arity();
            while (j > 0) {
                --j;
                visit(f->get_domain(j), qlist, visited);
            }
            visit(f->get_range(), qlist, visited);
            j = f->get_num_parameters();
            while (j > 0) {
                --j;
                parameter p(f->get_parameter(j));
                if (p.is_ast()) {
                    visit(p.get_ast(), qlist, visited);
                }
            }
            break;
        }
        case AST_SORT: {
            sort* s = to_sort(n);
            j = s->get_num_parameters();
            while (j > 0) {
                --j;
                parameter p(s->get_parameter(j));
                if (p.is_ast()) {
                    visit(p.get_ast(), qlist, visited);
                }
            }
            break;
        }
        case AST_APP: {
            app* a = to_app(n);
            j = a->get_num_args();
            while (j > 0) {
                --j;
                visit(a->get_arg(j), qlist, visited);
            }
            visit(a->get_decl(), qlist, visited);
            break;
        }
        case AST_QUANTIFIER:
            j = to_quantifier(n)->get_num_patterns();
            qlist = m_qlist_manager.mk_cons(to_quantifier(n), qlist);
            m_qlists.push_back(qlist);
            while (j > 0) {
                --j;
                visit(to_quantifier(n)->get_pattern(j), qlist, visited);
            }
            j = to_quantifier(n)->get_num_no_patterns();
            while (j > 0) {
                --j;
                visit(to_quantifier(n)->get_no_pattern(j), qlist, visited);
            }
            j = to_quantifier(n)->get_num_decls();
            while (j > 0) {
                --j;
                visit(to_quantifier(n)->get_decl_sort(j), qlist, visited);
                visit_sort(to_quantifier(n)->get_decl_sort(j));
            }
            visit(to_quantifier(n)->get_expr(), qlist, visited);
            break;
        default:
            break;
        }
        return visited;
    }

    void reduce1(ast * n, quantifier_list * qlist) {
        format * r;
        switch(n->get_kind()) {
        case AST_APP:
            r = reduce1_app(to_app(n), qlist);
            break;
        case AST_VAR:
            r = reduce1_var(to_var(n), qlist);
            break;
        case AST_QUANTIFIER:
            r = reduce1_quantifier(to_quantifier(n), qlist);
            break;
        case AST_SORT:
            r = reduce1_sort(to_sort(n), qlist);
            break;
        case AST_FUNC_DECL:
            r = reduce1_func_decl(to_func_decl(n), qlist);
            break;
        }
        m_cache.insert(n, qlist, r);
    }

    format * mk_parameter(parameter const & p, quantifier_list * qlist) {
        if (p.is_int()) {
            return mk_int(m_manager, p.get_int());
        }
        else if (p.is_symbol()) {
            return mk_string(m_manager, p.get_symbol().str().c_str());
        }
        else if (p.is_ast()) {
            ast * n = p.get_ast();
            if (is_func_decl(n)) {
                return mk_string(m_manager, to_func_decl(n)->get_name().str().c_str());
            }
            else {
                return get_cached(p.get_ast(), qlist);
            }
        }
        else if (p.is_rational()) {
            return mk_string(m_manager, p.get_rational().to_string().c_str());
        }
        else {
            return 0;
        }
    }

    void mk_parameters(unsigned num_params, parameter const * p, quantifier_list * qlist, ptr_buffer<format> & result, bool add_separator) {
        bool first = true;
        for (unsigned i = 0; i < num_params; i++) {
            if (!first && add_separator) { 
                result.push_back(mk_string(m_manager, ":"));
            }
            format * pp = mk_parameter(p[i], qlist);
            if (pp) {
                result.push_back(pp);
                first = false;
            }
        }
    }

    format * mk_parameters(unsigned num_params, parameter const * p, quantifier_list * qlist) {
        if (num_params == 0)
            return m_nil;
        ptr_buffer<format> buffer; 
        buffer.push_back(mk_string(m_manager, "["));
        mk_parameters(num_params, p, qlist, buffer, true);
        buffer.push_back(mk_string(m_manager, "]"));
        return mk_compose(m_manager, buffer.size(), buffer.c_ptr());
    }
    
    void visit_sort(sort* s) {
        if (m_datatype_util.is_datatype(s) &&
            !m_visited_datatypes.is_marked(s)) {
            m_datatypes.push_back(s);
            m_visited_datatypes.mark(s, true);
        }
    }

    format * reduce1_sort(sort * s, quantifier_list * qlist) {
        if (m_datatype_util.is_datatype(s)) {
            return mk_string(m_manager, s->get_name().str().c_str());
        }
        ptr_buffer<format> pps;
        mk_parameters(s->get_num_parameters(), s->get_parameters(), qlist, pps, false);
        std::string name = s->get_name().str();
        if (pps.empty())
            return mk_string(m_manager, name.c_str());
        return mk_seq1(m_manager, pps.c_ptr(), pps.c_ptr() + pps.size(),
                       f2f(), name.c_str());
    }

    format * reduce1_func_decl(func_decl * f, quantifier_list * qlist) {
        ptr_buffer<format> children;
        children.push_back(mk_compose(m_manager, 
                                      mk_string(m_manager, f->get_name().str().c_str()),
                                      mk_parameters(f->get_num_parameters(), f->get_parameters(), qlist)));
        for (unsigned i = 0; i < f->get_arity(); i++) 
            children.push_back(get_cached(f->get_domain(i), qlist));
        children.push_back(get_cached(f->get_range(), qlist));
        return mk_seq1(m_manager, children.begin(), children.end(), f2f(), "define");
    }

    void get_children(app * n, quantifier_list * qlist, ptr_buffer<format> & result) {
        for (unsigned i = 0; i < n->get_num_args(); i++)
            result.push_back(get_cached(n->get_arg(i), qlist));
    }

    format * reduce1_app(app * n, quantifier_list * qlist) {
        rational       val;
        bool           is_int;
        bool           pos;
        unsigned       bv_size;
        uint64         uval;
        buffer<symbol> names;   
        ptr_buffer<format> children;
        if (m_autil.is_numeral(n, val, is_int)) {
            std::string str;
            if (val.is_neg()) {
                str = "(- " + (-val).to_string() + ")";
            }
            else {
                str = val.to_string();
            }
            return mk_string(m_manager, str.c_str());
        }
        else if (m_bvutil.is_numeral(n, val, bv_size)) {
            std::string str = val.to_string();
            return mk_compose(m_manager, 
                              mk_string(m_manager, "bv"), 
                              mk_string(m_manager, str.c_str()), 
                              mk_compose(m_manager, mk_string(m_manager, "["), mk_unsigned(m_manager, bv_size), mk_string(m_manager, "]")));
        }
        else if (m_dl_util.is_finite_sort(n) &&
                 m_dl_util.is_numeral_ext(n, uval)) {
            return mk_string(m_manager, rational(uval,rational::ui64()).to_string().c_str());
        }
        else if (m_manager.is_label(n, pos, names)) {
            get_children(n, qlist, children);
            symbol2format f(m_manager);
            format * lbl = names.size() > 1 ? mk_seq5(m_manager, names.begin(), names.end(), f) : f(names[0]);            
            format * args[2] = { lbl, children[0] };
            format ** begin = args;
            return mk_seq1(m_manager, begin, begin+2, f2f(), pos ? "lblpos" : "lblneg"); 
        }
        else if (m_manager.is_pattern(n)) {
            get_children(n, qlist, children);
            return mk_seq5(m_manager, children.begin(), children.end(), f2f(), "{", "}");
        }
        else if (m_manager.is_proof(n)) {
            get_children(n, qlist, children);
            return mk_seq2(m_manager, children.begin(), children.end(), f2f(), n->get_decl()->get_name().str().c_str(),
                           FORMAT_DEFAULT_INDENT, "[", "]");
        }
        else if (m_params.m_pp_fixed_indent || (n->get_decl()->get_num_parameters() > 0 && !n->get_decl()->private_parameters())) {
            format * head = mk_compose(m_manager, 
                                       mk_string(m_manager, n->get_decl()->get_name().str().c_str()),
                                       mk_parameters(n->get_decl()->get_num_parameters(), n->get_decl()->get_parameters(), qlist));
            if (n->get_num_args() == 0) 
                return head;
            children.push_back(head);
            get_children(n, qlist, children);
            return mk_seq4(m_manager, children.begin(), children.end(), f2f());
        }
        else if (n->get_num_args() == 0)
            return mk_string(m_manager, n->get_decl()->get_name().str().c_str());
        else {
            get_children(n, qlist, children);
            return mk_seq1(m_manager, children.begin(), children.end(), f2f(), n->get_decl()->get_name().str().c_str());
        }
    }

    format * reduce1_var(var * v, quantifier_list * qlist) {
        unsigned idx = v->get_idx();
        unsigned i = idx;
        while (!is_nil(qlist)) {
            quantifier * q = head(qlist);
            if (i < q->get_num_decls())
                return mk_string(m_manager, q->get_decl_name(q->get_num_decls() - i - 1).str().c_str());
            i -= q->get_num_decls();
            qlist  = tail(qlist);
        }
        if (i < m_num_var_names) {
            return mk_string(m_manager, m_var_names[m_num_var_names - i - 1]);
        }
        else {
            return mk_compose(m_manager, mk_string(m_manager, "#"), mk_unsigned(m_manager, idx));
        }
    }

    format * reduce1_quantifier(quantifier * q, quantifier_list * qlist) {
        qlist = m_qlist_manager.mk_cons(q, qlist);
        
        ptr_buffer<format> buffer;
        unsigned num = q->get_num_decls();
        for (unsigned j = 0; j < num; j++) {
            format * d[2];
            d[0] = mk_string(m_manager, q->get_decl_name(j).str().c_str());
            d[1] = get_cached(q->get_decl_sort(j), qlist);
            format ** it = d;
            buffer.push_back(mk_seq5(m_manager, it, it+2, f2f()));
        }
        buffer.push_back(get_cached(q->get_expr(), qlist));
        num = q->get_num_patterns();
        char const * pat = ":pat ";
        unsigned pat_indent = static_cast<unsigned>(strlen(pat));
        for (unsigned i = 0; i < num; i++)
            buffer.push_back(mk_compose(m_manager, mk_string(m_manager, pat), mk_indent(m_manager, pat_indent, get_cached(q->get_pattern(i), qlist))));
        num = q->get_num_no_patterns();
        for (unsigned i = 0; i < num; i++)
            buffer.push_back(mk_compose(m_manager, mk_string(m_manager, ":nopat {"), get_cached(q->get_no_pattern(i), qlist), mk_string(m_manager, "}")));
        if (q->get_qid() != symbol::null)
            buffer.push_back(mk_compose(m_manager, mk_string(m_manager, ":qid {"), mk_string(m_manager, q->get_qid().str().c_str()), mk_string(m_manager, "}")));
        return mk_seq3(m_manager, buffer.begin(), buffer.end(), f2f(), q->is_forall() ? "forall" : "exists",
                       q->get_num_decls());
    }

public:
    formatter(ast_manager & m, pp_params const & p, unsigned num_var_names, char const * const * var_names):
        m_params(p),
        m_manager(m),
        m_qlist_manager(m),
        m_cache(m),
        m_qlists(m_qlist_manager),
        m_nil(mk_nil(m), fm(m)),
        m_autil(m),
        m_bvutil(m),
        m_datatype_util(m),
        m_dl_util(m),
        m_format_trail(fm(m)),
        m_num_var_names(num_var_names),
        m_var_names(var_names) {
    }
    
    ~formatter() {
    }

    format * operator()(ast * n) {
        m_todo.push_back(pp_entry(n, m_qlist_manager.mk_nil()));
        while (!m_todo.empty()) {
            pp_entry k = m_todo.back();
            if (m_cache.contains(k.first, k.second))
                m_todo.pop_back();
            else if (visit_children(k.first, k.second)) {
                m_todo.pop_back();
                reduce1(k.first, k.second);
            }
        }
        format* f1 = get_cached(n, m_qlist_manager.mk_nil());

        if (m_datatypes.empty()) {
            return f1;
        }
        ptr_buffer<format> formats;
        formats.push_back(f1);

        for (unsigned i = 0; i < m_datatypes.size(); ++i) {
            sort* s = m_datatypes[i];
            std::ostringstream buffer;
            m_datatype_util.display_datatype(s, buffer);
            format* f2 = mk_string(m_manager, buffer.str().c_str());           
            formats.push_back(mk_line_break(m_manager));
            formats.push_back(f2);
        }
        f1 = mk_compose(m_manager, formats.size(), formats.c_ptr());
        //
        // Ensure that reference count is live.
        //
        m_format_trail.push_back(f1);
        return f1;        
    }
};


std::ostream & ast_pp(std::ostream & out, ast * n, ast_manager & m, pp_params const & p, unsigned indent,
                      unsigned num_vars, char const * const * names) {
    formatter f(m, p, num_vars, names);
    app_ref fmt(fm(m));
    fmt = f(n);
    if (indent > 0) 
        fmt = format_ns::mk_indent(m, indent, fmt);
    pp(out, fmt, m, p);
    return out;
}

std::string & ast_pp(std::string & out, ast * n, ast_manager & m, pp_params const & p, unsigned indent) {
    std::ostringstream buffer;
    buffer << mk_pp(n, m, p, indent);
    out += buffer.str();
    return out;
}

std::string ast_pp(ast * n, ast_manager & m, pp_params const & p, unsigned indent) {
    std::string out;
    return ast_pp(out, n, m, p, indent);
}


std::string & ast_pp(std::string & out, ast * n, ast_manager & m) {
    return ast_pp(out, n, m, get_pp_default_params());
}

std::string ast_pp(ast * n, ast_manager & m) {
    return ast_pp(n, m, get_pp_default_params());
}

