
#include"smtlib.h"
#include"ast_pp.h"
#include"ast_smt2_pp.h"

#ifdef _WINDOWS
#ifdef ARRAYSIZE
#undef ARRAYSIZE
#endif 
#include <windows.h>
#include <strsafe.h>
#endif

#include <iostream>


using namespace smtlib;

// --------------------------------------------------------------------------
//  symtable

symtable::~symtable() {
    reset();
}

void symtable::reset() {
    svector<ptr_vector<func_decl>*> range;
    m_ids.get_range(range);
    for (unsigned i = 0; i < range.size(); ++i) {
        ptr_vector<func_decl> const & v = *range[i];
        for (unsigned j = 0; j < v.size(); ++j) {
            m_manager.dec_ref(v[j]);
        }
        dealloc(range[i]);
    }
    m_ids.reset();
    ptr_vector<sort> sorts;
    m_sorts1.get_range(sorts);
    for (unsigned i = 0; i < sorts.size(); ++i) {
        m_manager.dec_ref(sorts[i]);
    }
    m_sorts1.reset();
    ptr_vector<sort_builder> sort_builders;
    m_sorts.get_range(sort_builders);
    for (unsigned i = 0; i < sort_builders.size(); ++i) {
        dealloc(sort_builders[i]);
    }
    m_sorts.reset();
}


void symtable::insert(symbol s, func_decl * d) {
    ptr_vector<func_decl>* decls = 0;
    m_manager.inc_ref(d);
    if (!m_ids.find(s, decls)) {
        SASSERT(!decls);
        decls = alloc(ptr_vector<func_decl>);
        decls->push_back(d);
        m_ids.insert(s, decls);
    }
    else {
        SASSERT(decls);
        if ((*decls)[0] != d) {
            decls->push_back(d);
        }
        else {
            m_manager.dec_ref(d);
        }
    }
}

bool symtable::find1(symbol s, func_decl*& d) {
    ptr_vector<func_decl>* decls = 0;
    
    if (!m_ids.find(s, decls)) {
        SASSERT(!decls);
        return false;
    }
    SASSERT(decls && !decls->empty());
    d = (*decls)[0];
    return true;
}

bool symtable::find_overload(symbol s, ptr_vector<sort> const & dom, func_decl * & d) {
    ptr_vector<func_decl>* decls = 0;
    d = 0;
    if (!m_ids.find(s, decls)) {
        SASSERT(!decls);
        return false;
    }
    SASSERT(decls);
    for (unsigned i = 0; i < decls->size(); ++i) {
        func_decl* decl = (*decls)[i];
        if (decl->is_associative() && decl->get_arity() > 0) {
            for (unsigned j = 0; j < dom.size(); ++j) {
                if (dom[j] != decl->get_domain(0)) {
                    goto try_next;
                }
            }
            d = decl;
            return true;
        }

        if (decl->get_arity() != dom.size()) {
            goto try_next;
        }
        for (unsigned j = 0; j < decl->get_arity(); ++j) {            
            if (decl->get_domain(j) != dom[j]) {
                goto try_next;
            }
        }
        d = decl;
        return true;

    try_next:
        if (decl->get_family_id() == m_manager.get_basic_family_id() && decl->get_decl_kind() == OP_DISTINCT) {
            // we skip type checking for 'distinct'
            d = decl;
            return true;
        }
    }
    return false;
}

// Store in result the func_decl that are not attached to any family id. 
// That is, the uninterpreted constants and function declarations.
void symtable::get_func_decls(ptr_vector<func_decl> & result) const {
    svector<ptr_vector<func_decl>*> tmp;
    m_ids.get_range(tmp);
    svector<ptr_vector<func_decl>*>::const_iterator it  = tmp.begin();
    svector<ptr_vector<func_decl>*>::const_iterator end = tmp.end();
    for (; it != end; ++it) {
        ptr_vector<func_decl> * curr = *it;
        if (curr) {
            ptr_vector<func_decl>::const_iterator it2  = curr->begin();
            ptr_vector<func_decl>::const_iterator end2 = curr->end();
            for (; it2 != end2; ++it2) {
                func_decl * d = *it2;
                if (d && d->get_family_id() == null_family_id) {
                    result.push_back(d);
                }
            }
        }
    }
}

void symtable::insert(symbol s, sort_builder* sb) {
    m_sorts.insert(s, sb);
}

bool symtable::lookup(symbol s, sort_builder*& sb) {
    return m_sorts.find(s, sb);
}

void symtable::push_sort(symbol name, sort* srt) {
    m_sorts.begin_scope();
    sort_builder* sb = alloc(basic_sort_builder,srt);
    m_sorts.insert(name, sb);
    m_sorts_trail.push_back(sb);
}

void symtable::pop_sorts(unsigned num_sorts) {
    while (num_sorts > 0) {
        dealloc(m_sorts_trail.back());
        m_sorts_trail.pop_back();
        m_sorts.end_scope();
    }
}

void symtable::get_sorts(ptr_vector<sort>& result) const {
    vector<sort*,false> tmp;
    m_sorts1.get_range(tmp);
    for (unsigned i = 0; i < tmp.size(); ++i) {
        if (tmp[i]->get_family_id() == null_family_id) {
            result.push_back(tmp[i]);
        }
    }
}


// --------------------------------------------------------------------------
//  theory

func_decl * theory::declare_func(symbol const & id, sort_ref_buffer & domain, sort * range,
                                 bool  is_assoc, bool  is_comm, bool  is_inj) {
    func_decl * decl = m_ast_manager.mk_func_decl(id, domain.size(), domain.c_ptr(), range,
                                                  is_assoc, is_comm, is_inj);

    m_symtable.insert(id, decl);
    m_asts.push_back(decl);
    return decl;
}


sort * theory::declare_sort(symbol const & id) {
    sort * decl = m_ast_manager.mk_uninterpreted_sort(id);
    m_symtable.insert(id, decl);
    m_asts.push_back(decl);
    return decl;
}


bool theory::get_func_decl(symbol id, func_decl * & decl) {
    return m_symtable.find1(id, decl);
}

bool theory::get_sort(symbol id, sort* & s) {
    return m_symtable.find(id, s);
}

bool theory::get_const(symbol id, expr * & term) {
    func_decl* decl = 0;
    if (!get_func_decl(id,decl)) {
        return false;
    }
    if (decl->get_arity() != 0) {
        return false;
    }
    term = m_ast_manager.mk_const(decl);
    m_asts.push_back(term);
    return true;
}

void benchmark::display_as_smt2(std::ostream & out) const {
    if (m_logic != symbol::null) 
        out << "(set-logic " << m_logic << ")\n";
    out << "(set-info :smt-lib-version 2.0)\n";
    out << "(set-info :status ";
    switch (m_status) {
    case SAT: out << "sat"; break;
    case UNSAT: out << "unsat"; break;
    default: out << "unknown"; break;
    }
    out << ")\n";
#if 0
    ast_manager & m = m_ast_manager;
    ptr_vector<func_decl> decls;
    m_symtable.get_func_decls(decls);
    ptr_vector<func_decl>::const_iterator it  = decls.begin();
    ptr_vector<func_decl>::const_iterator end = decls.end();
    for (; it != end; ++it) {
        func_decl * f = *it;
        out << "(declare-fun " << f->get_name() << " (";
        for (unsigned i = 0; i < f->get_arity(); i++) {
            if (i > 0) out << " ";
            out << mk_ismt2_pp(f->get_domain(i), m);
        }
        out << ") " << mk_ismt2_pp(f->get_range(), m);
        out << ")\n";
    }
#endif
}
