/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    ast_dag_pp.cpp

Abstract:
 
    AST low level pretty printer.
    
Author:

    Leonardo de Moura (leonardo) 2006-10-19.
    Nikolaj Bjorner (nbjorner) 2007-07-17

Revision History:

--*/

#include<iostream>
#include"for_each_ast.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"ast_pp.h"

class dag_printer {
    ast_manager&    m_manager;
    std::ostream &  m_out;
    ast_mark&       m_mark;
    bool            m_initialized;
    svector<symbol> m_names;
    family_id       m_basic_fid;
    family_id       m_bv_fid;
    family_id       m_arith_fid;
    family_id       m_array_fid;
    arith_util      m_arith;
    bv_util         m_bv;
    bool            m_enable_shortcut;

    void process_ast(ast* a) {
        for_each_ast(*this, m_mark, a);
    }

    void process_info(decl_info* info) {
        if (!info) {
            return;
        }
        unsigned num_params = info->get_num_parameters();
        for (unsigned i = 0; i < num_params; ++i) {
            parameter const& p = info->get_parameter(i);
            
            if (p.is_ast() && !m_mark.is_marked(p.get_ast())) {
                process_ast(p.get_ast());
            }
        }
    }
        
    template<typename T>
    void display_children(unsigned num_children, T * const * children) {
        for (unsigned i = 0; i < num_children; i++) {
            display_node_id(children[i]);
        }
    }

    void display_node_id(ast* n) {
        unsigned id = n->get_id();
        switch(n->get_kind()) {
        case AST_FUNC_DECL:
        case AST_SORT:
            m_out << "$d" << (id - (1 << 31)) << " ";
            break;
        default:
            m_out << "$" << id << " ";
            break;
        }        
    }

    void display_parameter(parameter const& p) 
    {
        if (p.is_int()) {
            m_out << p.get_int() << " ";
        }
        else if (p.is_ast()) {
            SASSERT(p.is_ast());
            display_node_id(p.get_ast());
        }
        else if (p.is_rational()) {
            m_out << p.get_rational() << " ";
        }
        else if (p.is_symbol()) {
            display_symbol(p.get_symbol());
        }
        else {
            UNREACHABLE();
        }
    }

    // Display: 
    //   App name [ parameters] arguments
    //
    void display_builtin(app* n) {
        func_decl* d = n->get_decl();
        unsigned num_params = d->get_num_parameters();

        m_out << "App ";
        display_node_id(n);        
        display_symbol(d->get_name());
        if (num_params > 0) {
            m_out << "[ ";
            for (unsigned i = 0; i < num_params; ++i) {
                display_parameter(d->get_parameter(i));
            }
            m_out << "] ";
        }
        display_children(n->get_num_args(), n->get_args());
        m_out << "\n";
    }

    void display_info(func_decl_info* info) {
        if (!info) {
            return;
        }
        m_out << "BUILTIN " << get_family_name(info->get_family_id()) << " " << info->get_decl_kind() << " ";

        if (info->is_associative()) {
            m_out << ":assoc ";
        }
        if (info->is_commutative()) {
            m_out << ":comm ";
        }
        if (info->is_injective()) {
            m_out << ":inj ";
        }
        for (unsigned i = 0; i < info->get_num_parameters(); ++i) {
            display_parameter(info->get_parameter(i));
        }
    }

    void display_info(sort_info* info) {
        if (!info) {
            return;
        }
        m_out << "BUILTIN " << get_family_name(info->get_family_id()) << " " << info->get_decl_kind() << " ";
        // TODO: remove this if... it doesn't make sense...
        if (!info->is_infinite() && !info->is_very_big()) {
            m_out << "Size " << info->get_num_elements().size() << " ";
        }
        for (unsigned i = 0; i < info->get_num_parameters(); ++i) {
            display_parameter(info->get_parameter(i));
        }
    }

    symbol get_family_name(family_id id) {
        if (id == null_family_id) {
            return symbol("null");
        }
        if (!m_initialized) {
            svector<symbol> names;
            svector<family_id> range;
            m_manager.get_dom(names);
            m_manager.get_range(range);
            m_names.resize(range.size());
            for (unsigned i = 0; i < range.size(); ++i) {
                SASSERT(range[i] < static_cast<family_id>(range.size()));
                m_names[range[i]] = names[i];
            }
            m_initialized = true;
        }
        SASSERT(id < static_cast<family_id>(m_names.size()));
        return m_names[id];
    }

    bool has_special_char(char const* s) {
        while (s && *s) {
            if (*s == ' ') {
                return true;
            }
            ++s;
        }
        return false;
    }

    void display_symbol(symbol const& s) {
         if (s.is_numerical()) {
             m_out << s << " ";
         }
         else if (!(s.bare_str()[0])) {
              m_out << "\"null\" ";
         }
         else if (!has_special_char(s.bare_str())) {
             m_out << s << " ";
         }
         else {
             char const* r = s.bare_str();
             m_out << "\"";
             while (*r) {
                 if (*r == ' ' || *r == '\n' ||
                     *r == '\t' || *r == '\r') {
                     m_out << "\\" << ((unsigned)(*r));
                 }
                 else {
                     m_out << *r;
                 }
                 ++r;
             }
             m_out << "\" ";
         }        
    }

public:

    dag_printer(ast_manager& mgr, std::ostream & out, ast_mark& mark):
        m_manager(mgr),
        m_out(out),
        m_mark(mark),
        m_initialized(false),
        m_basic_fid(mgr.get_basic_family_id()),
        m_bv_fid(mgr.get_family_id("bv")),
        m_arith_fid(mgr.get_family_id("arith")),
        m_array_fid(mgr.get_family_id("array")),
        m_arith(mgr),
        m_bv(mgr),
        m_enable_shortcut(true)
    {
    }

    void operator()(sort * n) {
        process_info(n->get_info());
        m_out << "Ty ";
        display_node_id(n);        
        display_symbol(n->get_name());
        display_info(n->get_info());
        m_out << "\n";
    }
     
    void pp_num(app* n, rational const& r) {
        m_out << "Num ";
        display_node_id(n);
        m_out << r << " ";
        display_node_id(m_manager.get_sort(n));
        m_out << "\n";
    }

    void operator()(var * n) {
        process_ast(n->get_sort());
        m_out << "Var ";
        display_node_id(n);        
        m_out << n->get_idx() << " ";
        display_node_id(n->get_sort());
        m_out << "\n";
    }

    void operator()(func_decl * n) {

        process_info(n->get_info());

        family_id fid = n->get_family_id();
        if (m_arith_fid == fid &&
            n->get_info()->get_decl_kind() == OP_NUM) {
            return;
        }

        if (m_bv_fid == fid &&
            n->get_info()->get_decl_kind() == OP_BV_NUM) {
            return;
        }

        m_out << "Dec ";
        display_node_id(n);
        display_symbol(n->get_name());
        unsigned dom_size = n->get_arity();
        for (unsigned i = 0; i < dom_size; ++i) {
            display_node_id(n->get_domain(i));
        }
        display_node_id(n->get_range());
        display_info(n->get_info());
        m_out << "\n";
    }

    void operator()(app * n) {   
        process_ast(n->get_decl());
        family_id fid = n->get_family_id();
        unsigned bv_size;
        rational val;
        if (m_arith.is_numeral(n, val)) {
            pp_num(n, val);
        }
        else if (m_bv.is_numeral(n, val, bv_size)) {
            pp_num(n, val);
        }
        else if (m_enable_shortcut &&
            fid != null_family_id && 
            (fid == m_basic_fid || fid == m_bv_fid || fid == m_array_fid || fid == m_arith_fid)) {
            display_builtin(n);
        }
        else if (n->get_num_args() == 0 && fid == null_family_id) {
            func_decl* d = n->get_decl();
            m_out << "Const ";
            display_node_id(n);
            display_symbol(d->get_name());
            display_node_id(d->get_range());
            m_out << "\n";
        }
        else {
            m_out << "Fun ";
            display_node_id(n);
            display_node_id(n->get_decl());
            display_children(n->get_num_args(), n->get_args());
            m_out << "\n";
        }
    }

    void operator()(quantifier * n) {
        m_out << "Qua ";
        display_node_id(n);
        m_out << (n->is_forall() ? "FORALL" : "EXISTS") << " ";
        m_out << n->get_weight() << " ";
        if (symbol::null != n->get_skid()) {            
            m_out << "\"" << n->get_skid()   << "\" ";
        }
        else {
            m_out << "\"null\" ";
        }
        if (symbol::null != n->get_qid()) {
            m_out << "\"" << n->get_qid()    << "\" ";
        }
        else {
            m_out << "\"null\" ";
        }
        unsigned num_decls = n->get_num_decls();
        m_out << num_decls << " ";
        for (unsigned i = 0; i < num_decls; i++) {
            m_out << n->get_decl_name(i) << " ";
            display_node_id(n->get_decl_sort(i));
        }
        m_out << n->get_num_patterns() << " ";
        display_children(n->get_num_patterns(), n->get_patterns());
        display_node_id(n->get_expr());
        m_out << "\n";
    }
};

void ast_dag_pp(std::ostream & out, ast_manager& mgr, ast_mark& mark, ast * n) {    
    dag_printer p(mgr, out, mark);
    for_each_ast(p, mark, n, true);
}

void ast_dag_pp(std::ostream & out, ast_manager& mgr, ast * n) {
    ast_mark mark;
    ast_dag_pp(out, mgr, mark, n);
}

