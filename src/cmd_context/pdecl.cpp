/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    pdecl.cpp

Abstract:

    Parametric declarations for SMT-LIB 2.0 + inductive data-types.

Author:

    Leonardo de Moura (leonardo) 2011-03-02.

Revision History:

--*/
#include"pdecl.h"
#include"datatype_decl_plugin.h"
using namespace format_ns;

class psort_inst_cache {
    unsigned              m_num_params;
    sort *                m_const;
    obj_map<sort, void *> m_map; // if m_num_params == 1 value is a sort, otherwise it is a reference to another inst_cache
public:
    psort_inst_cache(unsigned num_params):m_num_params(num_params), m_const(0) { 
    }

    ~psort_inst_cache() { SASSERT(m_map.empty()); SASSERT(m_const == 0); }
    
    void finalize(pdecl_manager & m) {
        if (m_num_params == 0) {
            SASSERT(m_map.empty());
            if (m_const)
                m.m().dec_ref(m_const);
            m_const = 0;
        }
        else {
            SASSERT(m_const == 0);
            obj_map<sort, void *>::iterator it  = m_map.begin();
            obj_map<sort, void *>::iterator end = m_map.end();
            for (; it != end; ++it) {
                m.m().dec_ref((*it).m_key);
                if (m_num_params == 1) {
                    m.m().dec_ref(static_cast<sort*>((*it).m_value));
                }
                else {
                    psort_inst_cache * child = static_cast<psort_inst_cache*>((*it).m_value);
                    child->finalize(m);
                    child->~psort_inst_cache();
                    m.a().deallocate(sizeof(psort_inst_cache), child);
                }
            }
            m_map.reset();
        }
    }

    void insert(pdecl_manager & m, sort * const * s, sort * r) {
        if (m_num_params == 0) {
            SASSERT(m_const == 0);
            m.m().inc_ref(r);
            m_const = r;
            return;
        }
        psort_inst_cache * curr = this;
        while (true) {
            if (curr->m_num_params == 1) {
                SASSERT(!curr->m_map.contains(*s));
                curr->m_map.insert(*s, r);
                m.m().inc_ref(*s);
                m.m().inc_ref(r);
                return;
            }
            void * next = 0;
            if (!curr->m_map.find(*s, next)) {
                next = new (m.a().allocate(sizeof(psort_inst_cache))) psort_inst_cache(curr->m_num_params-1);
                curr->m_map.insert(*s, next);
                m.m().inc_ref(*s);
            }
            SASSERT(next != 0);
            SASSERT(curr->m_num_params == static_cast<psort_inst_cache*>(next)->m_num_params + 1);
            s++;
            curr = static_cast<psort_inst_cache*>(next);
        }
    }
    
    sort * find(sort * const * s) const {
        if (m_num_params == 0)
            return m_const;
        psort_inst_cache const * curr = this;
        while (true) {
            if (curr->m_num_params == 1) {
                void * r = 0;
                curr->m_map.find(*s, r);
                return static_cast<sort*>(r);
            }
            else {
                void * next = 0;
                curr->m_map.find(*s, next);
                if (next == 0)
                    return 0;
                s++;
                curr = static_cast<psort_inst_cache*>(next);
            }
        }
    }

    bool empty() const { return m_num_params == 0 ? m_const == 0 : m_map.empty(); }
};

void psort::cache(pdecl_manager & m, sort * const * s, sort * r) {
    if (!m_inst_cache)
        m_inst_cache = m.mk_inst_cache(m_num_params);
    m_inst_cache->insert(m, s, r);
}

sort * psort::find(sort * const * s) const {
    if (!m_inst_cache)
        return 0;
    return m_inst_cache->find(s);
}

void psort::finalize(pdecl_manager & m) {
    m.del_inst_cache(m_inst_cache);
    m_inst_cache = 0;
}

/**
   \brief wrapper for sorts.
*/
class psort_sort : public psort {
    friend class pdecl_manager;
    sort * m_sort;
    psort_sort(unsigned id, pdecl_manager & m, sort * s):psort(id, 0), m_sort(s) { m.m().inc_ref(m_sort); }
    virtual void finalize(pdecl_manager & m) { 
        m.m().dec_ref(m_sort); 
        psort::finalize(m);
    }
    virtual bool check_num_params(pdecl * other) const { return true; }
    virtual size_t obj_size() const { return sizeof(psort_sort); }
    sort * get_sort() const { return m_sort; }
    virtual sort * instantiate(pdecl_manager & m, sort * const * s) { return m_sort; }
public:
    virtual ~psort_sort() {}
    virtual bool is_sort_wrapper() const { return true; }
    virtual char const * hcons_kind() const { return "psort_sort"; }
    virtual unsigned hcons_hash() const { return m_sort->get_id(); }
    virtual bool hcons_eq(psort const * other) const {
        if (other->hcons_kind() != hcons_kind()) 
            return false;
        return m_sort == static_cast<psort_sort const *>(other)->m_sort;
    }
    virtual void display(std::ostream & out) const {
        out << m_sort->get_name();
    }
};

class psort_var : public psort {
    friend class pdecl_manager;
    unsigned m_idx;
    psort_var(unsigned id, unsigned num_params, unsigned idx):psort(id, num_params), m_idx(idx) { SASSERT(idx < num_params); }
    virtual sort * instantiate(pdecl_manager & m, sort * const * s) { return s[m_idx]; }
    virtual size_t obj_size() const { return sizeof(psort_var); }
public:
    virtual ~psort_var() {}
    virtual char const * hcons_kind() const { return "psort_var"; }
    virtual unsigned hcons_hash() const { return hash_u_u(m_num_params, m_idx); }
    virtual bool hcons_eq(psort const * other) const {
        if (other->hcons_kind() != hcons_kind()) 
            return false;
        return get_num_params() == other->get_num_params() && m_idx == static_cast<psort_var const *>(other)->m_idx;
    }
    virtual void display(std::ostream & out) const {
        out << "s_" << m_idx;
    }
};

class psort_app : public psort {
    friend class pdecl_manager;
    psort_decl *  m_decl;
    ptr_vector<psort> m_args;

    psort_app(unsigned id, unsigned num_params, pdecl_manager & m, psort_decl * d, unsigned num_args, psort * const * args):
        psort(id, num_params),
        m_decl(d),
        m_args(num_args, args) {
        m.inc_ref(d);
        m.inc_ref(num_args, args);
        SASSERT(num_args == m_decl->get_num_params() || m_decl->has_var_params());
        DEBUG_CODE(if (num_args == num_params) { for (unsigned i = 0; i < num_params; i++) args[i]->check_num_params(this); });
    }

    virtual void finalize(pdecl_manager & m) { 
        m.lazy_dec_ref(m_decl);
        m.lazy_dec_ref(m_args.size(), m_args.c_ptr());
        psort::finalize(m);
    }

    virtual size_t obj_size() const { return sizeof(psort_app); }

    struct khasher {
        unsigned operator()(psort_app const * d) const { return d->m_decl->hash(); }
    };
    
    struct chasher {
        unsigned operator()(psort_app const * d, unsigned idx) const { return d->m_args[idx]->hash(); }
    };

    virtual sort * instantiate(pdecl_manager & m, sort * const * s) { 
        sort * r = find(s);
        if (r) 
            return r;
        sort_ref_buffer args_i(m.m());
        unsigned sz = m_args.size();
        for (unsigned i = 0; i < sz; i++) {
            sort * a = m_args[i]->instantiate(m, s);
            args_i.push_back(a);
        }
        r = m_decl->instantiate(m, args_i.size(), args_i.c_ptr());
        cache(m, s, r);
        return r;
    }

public:
    virtual ~psort_app() {}
    virtual char const * hcons_kind() const { return "psort_app"; }
    virtual unsigned hcons_hash() const { 
        return get_composite_hash<psort_app*, khasher, chasher>(const_cast<psort_app*>(this), m_args.size());
    }
    virtual bool hcons_eq(psort const * other) const {
        if (other->hcons_kind() != hcons_kind()) 
            return false;
        if (get_num_params() != other->get_num_params())
            return false;
        psort_app const * _other = static_cast<psort_app const *>(other);
        if (m_decl != _other->m_decl)
            return false;
        SASSERT(m_args.size() == _other->m_args.size());
        unsigned sz = m_args.size();
        for (unsigned i = 0; i < sz; i++) {
            if (m_args[i] != _other->m_args[i])
                return false;
        }
        return true;
    }
    virtual void display(std::ostream & out) const {
        if (m_args.empty()) {
            out << m_decl->get_name();
        }
        else {
            out << "(" << m_decl->get_name();
            unsigned sz = m_args.size();
            for (unsigned i = 0; i < sz; i++) {
                out << " ";
                m_args[i]->display(out);
            }
            out << ")";
        }
    }
};

psort_decl::psort_decl(unsigned id, unsigned num_params, pdecl_manager & m, symbol const & n):
    pdecl(id, num_params),
    m_name(n),
    m_inst_cache(0) {
}

void psort_decl::finalize(pdecl_manager & m) {
    m.del_inst_cache(m_inst_cache);
    m_inst_cache = 0;
}

void psort_decl::cache(pdecl_manager & m, sort * const * s, sort * r) {
    if (!m_inst_cache)
        m_inst_cache = m.mk_inst_cache(m_num_params);
    m_inst_cache->insert(m, s, r);
}

sort * psort_decl::find(sort * const * s) {
    if (!m_inst_cache)
        return 0;
    return m_inst_cache->find(s);
}

psort_user_decl::psort_user_decl(unsigned id, unsigned num_params, pdecl_manager & m, symbol const & n, psort * p):
    psort_decl(id, num_params, m, n),
    m_def(p) {
    m.inc_ref(p);
    SASSERT(p == 0 || num_params == p->get_num_params());
}

void psort_user_decl::finalize(pdecl_manager & m) {
    m.dec_ref(m_def);
    m_def = 0;
    psort_decl::finalize(m);
}

sort * psort_user_decl::instantiate(pdecl_manager & m, unsigned n, sort * const * s) {
    SASSERT(n == m_num_params);
    sort * r = find(s);
    if (r)
        return r;
    if (m_def == 0) {
        buffer<parameter> ps;
        for (unsigned i = 0; i < n; i++)
            ps.push_back(parameter(s[i]));
        r  = m.m().mk_uninterpreted_sort(m_name, ps.size(), ps.c_ptr());
    }
    else {
        r = m_def->instantiate(m, s);
    }
    cache(m, s, r);
    m.save_info(r, this, n, s);
    return r;
}

void display_sort_args(std::ostream & out, unsigned num_params) {
    if (num_params > 0)
        out << " (";
    for (unsigned i = 0; i < num_params; i++) {
        if (i > 0) out << " ";
        out << "s_" << i;
    }
    if (num_params > 0)
        out << ") ";
}

void psort_user_decl::display(std::ostream & out) const {
    out << "(declare-sort " << m_name;
    display_sort_args(out, m_num_params);
    if (m_def)
        m_def->display(out);
    out << ")";
}

psort_builtin_decl::psort_builtin_decl(unsigned id, pdecl_manager & m, symbol const & n, family_id fid, decl_kind k):
    psort_decl(id, PSORT_DECL_VAR_PARAMS, m, n),
    m_fid(fid),
    m_kind(k) {
}

sort * psort_builtin_decl::instantiate(pdecl_manager & m, unsigned n, sort * const * s) {
    if (n == 0) {
        sort * r = m.m().mk_sort(m_fid, m_kind);
        m.save_info(r, this, 0, s);
        return r;
    }
    else {
        buffer<parameter> params;
        for (unsigned i = 0; i < n; i++)
            params.push_back(parameter(s[i]));
        sort * r = m.m().mk_sort(m_fid, m_kind, n, params.c_ptr());
        m.save_info(r, this, n, s);
        return r;
    }
}

sort * psort_builtin_decl::instantiate(pdecl_manager & m, unsigned n, unsigned const * s) {
    if (n == 0) {
        sort * r = m.m().mk_sort(m_fid, m_kind);
        m.save_info(r, this, 0, s);
        return r;
    }
    else {
        buffer<parameter> params;
        for (unsigned i = 0; i < n; i++)
            params.push_back(parameter(s[i]));
        sort * r = m.m().mk_sort(m_fid, m_kind, n, params.c_ptr());
        m.save_info(r, this, n, s);
        return r;
    }
}

void psort_builtin_decl::display(std::ostream & out) const {
    out << "(declare-builtin-sort " << m_name << ")";
}

void ptype::display(std::ostream & out, pdatatype_decl const * const * dts) const {
    switch (kind()) {
    case PTR_PSORT:        get_psort()->display(out); break;
    case PTR_REC_REF:      out << dts[get_idx()]->get_name(); break;
    case PTR_MISSING_REF:  out << get_missing_ref(); break;
    }
}

paccessor_decl::paccessor_decl(unsigned id, unsigned num_params, pdecl_manager & m, symbol const & n, ptype const & r):
    pdecl(id, num_params),
    m_name(n), 
    m_type(r) {
    if (m_type.kind() == PTR_PSORT) 
        m.inc_ref(r.get_psort());
}

void paccessor_decl::finalize(pdecl_manager & m) { 
    if (m_type.kind() == PTR_PSORT) 
        m.lazy_dec_ref(m_type.get_psort()); 
}

bool paccessor_decl::has_missing_refs(symbol & missing) const {
    if (m_type.kind() == PTR_MISSING_REF) {
        missing = m_type.get_missing_ref();
        return true;
    }
    return false;
}

bool paccessor_decl::fix_missing_refs(dictionary<int> const & symbol2idx, symbol & missing) {
    TRACE("fix_missing_refs", tout << "m_type.kind(): " << m_type.kind() << "\n"; 
          if (m_type.kind() == PTR_MISSING_REF) tout << m_type.get_missing_ref() << "\n";);
    if (m_type.kind() != PTR_MISSING_REF)
        return true;
    int idx;
    if (symbol2idx.find(m_type.get_missing_ref(), idx)) {
        m_type = ptype(idx);
        SASSERT(m_type.kind() == PTR_REC_REF);
        return true;
    }
    missing = m_type.get_missing_ref();
    return false;
}

accessor_decl * paccessor_decl::instantiate_decl(pdecl_manager & m, sort * const * s) {
    switch (m_type.kind()) {
    case PTR_REC_REF: return mk_accessor_decl(m_name, type_ref(m_type.get_idx()));
    case PTR_PSORT:   return mk_accessor_decl(m_name, type_ref(m_type.get_psort()->instantiate(m, s)));
    default:
        // missing refs must have been eliminated.
        UNREACHABLE();
        return 0;
    }
}

void paccessor_decl::display(std::ostream & out, pdatatype_decl const * const * dts) const {
    out << "(" << m_name << " ";
    m_type.display(out, dts);
    out << ")";
}

pconstructor_decl::pconstructor_decl(unsigned id, unsigned num_params, pdecl_manager & m, 
                                     symbol const & n, symbol const & r, unsigned num_accessors, paccessor_decl * const * accessors):
    pdecl(id, num_params),
    m_name(n),
    m_recogniser_name(r),
    m_accessors(num_accessors, accessors) {
    m.inc_ref(num_accessors, accessors);
    TRACE("pconstructor_decl", tout << "name: " << n << ", recognizer: " << r << "\n";);
}

void pconstructor_decl::finalize(pdecl_manager & m) {
    m.lazy_dec_ref(m_accessors.size(), m_accessors.c_ptr());
}

bool pconstructor_decl::has_missing_refs(symbol & missing) const {
    ptr_vector<paccessor_decl>::const_iterator it  = m_accessors.begin();
    ptr_vector<paccessor_decl>::const_iterator end = m_accessors.end();
    for (; it != end; ++it) {
        if ((*it)->has_missing_refs(missing))
            return true;
    }
    return false;
}

bool pconstructor_decl::fix_missing_refs(dictionary<int> const & symbol2idx, symbol & missing) {
    ptr_vector<paccessor_decl>::iterator it  = m_accessors.begin();
    ptr_vector<paccessor_decl>::iterator end = m_accessors.end();
    for (; it != end; ++it) {
        if (!(*it)->fix_missing_refs(symbol2idx, missing))
            return false;
    }
    return true;
}

constructor_decl * pconstructor_decl::instantiate_decl(pdecl_manager & m, sort * const * s) {
    ptr_buffer<accessor_decl> as;
    ptr_vector<paccessor_decl>::iterator it  = m_accessors.begin();
    ptr_vector<paccessor_decl>::iterator end = m_accessors.end();
    for (; it != end; ++it) 
        as.push_back((*it)->instantiate_decl(m, s));
    return mk_constructor_decl(m_name, m_recogniser_name, as.size(), as.c_ptr());
}

void pconstructor_decl::display(std::ostream & out, pdatatype_decl const * const * dts) const {
    out << "(" << m_name;
    ptr_vector<paccessor_decl>::const_iterator it  = m_accessors.begin();
    ptr_vector<paccessor_decl>::const_iterator end = m_accessors.end();
    for (; it != end; ++it) {
        out << " ";
        (*it)->display(out, dts);
    }
    out << ")";
}

pdatatype_decl::pdatatype_decl(unsigned id, unsigned num_params, pdecl_manager & m, 
                               symbol const & n, unsigned num_constructors, pconstructor_decl * const * constructors):
    psort_decl(id, num_params, m, n),
    m_constructors(num_constructors, constructors),
    m_parent(0) {
    m.inc_ref(num_constructors, constructors);
}

void pdatatype_decl::finalize(pdecl_manager & m) {
    m.lazy_dec_ref(m_constructors.size(), m_constructors.c_ptr());
    psort_decl::finalize(m);
}

bool pdatatype_decl::has_missing_refs(symbol & missing) const {
    ptr_vector<pconstructor_decl>::const_iterator it  = m_constructors.begin();
    ptr_vector<pconstructor_decl>::const_iterator end = m_constructors.end();
    for (; it != end; ++it) {
        if ((*it)->has_missing_refs(missing))
            return true;
    }
    return false;
}

bool pdatatype_decl::has_duplicate_accessors(symbol & duplicated) const {
    hashtable<symbol, symbol_hash_proc, symbol_eq_proc> names;
    ptr_vector<pconstructor_decl>::const_iterator it  = m_constructors.begin();
    ptr_vector<pconstructor_decl>::const_iterator end = m_constructors.end();
    for (; it != end; ++it) {
        ptr_vector<paccessor_decl> const& acc = (*it)->m_accessors;
        for (unsigned i = 0; i < acc.size(); ++i) {
            symbol const& name = acc[i]->get_name();
            if (names.contains(name)) {
                duplicated = name;
                return true;
            }
            names.insert(name);
        }
    }
    return false;
}


bool pdatatype_decl::fix_missing_refs(dictionary<int> const & symbol2idx, symbol & missing) {
    ptr_vector<pconstructor_decl>::iterator it  = m_constructors.begin();
    ptr_vector<pconstructor_decl>::iterator end = m_constructors.end();
    for (; it != end; ++it) {
        if (!(*it)->fix_missing_refs(symbol2idx, missing))
            return false;
    }
    return true;
}

datatype_decl * pdatatype_decl::instantiate_decl(pdecl_manager & m, sort * const * s) {
    ptr_buffer<constructor_decl> cs;
    ptr_vector<pconstructor_decl>::iterator it  = m_constructors.begin();
    ptr_vector<pconstructor_decl>::iterator end = m_constructors.end();
    for (; it != end; ++it) {
        cs.push_back((*it)->instantiate_decl(m, s));
    }
    return mk_datatype_decl(m_name, cs.size(), cs.c_ptr());
}

struct datatype_decl_buffer {
    ptr_buffer<datatype_decl> m_buffer;
    ~datatype_decl_buffer() { del_datatype_decls(m_buffer.size(), m_buffer.c_ptr()); }
};

sort * pdatatype_decl::instantiate(pdecl_manager & m, unsigned n, sort * const * s) {
    SASSERT(m_num_params == n);
    sort * r = find(s);
    if (r)
        return r;
    if (m_parent != 0) {
        if (m_parent->instantiate(m, s)) {
            r = find(s);
            SASSERT(r);
            return r;
        }
    }
    else {
        datatype_decl_buffer dts;
        dts.m_buffer.push_back(instantiate_decl(m, s));
        datatype_decl * d_ptr = dts.m_buffer[0];
        sort_ref_vector sorts(m.m());
        bool is_ok = m.get_dt_plugin()->mk_datatypes(1, &d_ptr, sorts);
        TRACE("pdatatype_decl", tout << "instantiating " << m_name << " is_ok: " << is_ok << "\n";);
        if (is_ok) {
            r = sorts.get(0);
            cache(m, s, r);
            m.save_info(r, this, n, s);
            m.notify_new_dt(r);
            return r;
        }
    }
    return 0;
}

void pdatatype_decl::display(std::ostream & out) const {
    out << "(declare-datatype " << m_name;
    display_sort_args(out, m_num_params);
    ptr_vector<pconstructor_decl>::const_iterator it  = m_constructors.begin();
    ptr_vector<pconstructor_decl>::const_iterator end = m_constructors.end();
    for (bool first = true; it != end; ++it) {
        if (!first)
            out << " ";
        if (m_parent) {
            (*it)->display(out, m_parent->children());
        }
        else {
            pdatatype_decl const * dts[1] = { this };
            (*it)->display(out, dts);
        }
        first = false;
    }
    out << ")";
}

pdatatypes_decl::pdatatypes_decl(unsigned id, unsigned num_params, pdecl_manager & m, 
                                 unsigned num_datatypes, pdatatype_decl * const * dts):
    pdecl(id, num_params),
    m_datatypes(num_datatypes, dts) {
    m.inc_ref(num_datatypes, dts);

    ptr_vector<pdatatype_decl>::iterator it  = m_datatypes.begin();
    ptr_vector<pdatatype_decl>::iterator end = m_datatypes.end();
    for (; it != end; ++it) {
        SASSERT((*it)->m_parent == 0);
        (*it)->m_parent = this;
    }
}

void pdatatypes_decl::finalize(pdecl_manager & m) {
    m.lazy_dec_ref(m_datatypes.size(), m_datatypes.c_ptr());
}

bool pdatatypes_decl::fix_missing_refs(symbol & missing) {
    TRACE("fix_missing_refs", tout << "pdatatypes_decl::fix_missing_refs\n";);
    dictionary<int> symbol2idx;
    ptr_vector<pdatatype_decl>::iterator it  = m_datatypes.begin();
    ptr_vector<pdatatype_decl>::iterator end = m_datatypes.end();
    for (unsigned idx = 0; it != end; ++it, ++idx)
        symbol2idx.insert((*it)->get_name(), idx);

    it  = m_datatypes.begin();
    for (unsigned idx = 0; it != end; ++it, ++idx) {
        if (!(*it)->fix_missing_refs(symbol2idx, missing))
            return false;
    }
    return true;
}

bool pdatatypes_decl::instantiate(pdecl_manager & m, sort * const * s) {
    datatype_decl_buffer dts;
    ptr_vector<pdatatype_decl>::iterator it  = m_datatypes.begin();
    ptr_vector<pdatatype_decl>::iterator end = m_datatypes.end();
    for (; it != end; ++it) {
        dts.m_buffer.push_back((*it)->instantiate_decl(m, s));
    }
    sort_ref_vector sorts(m.m());
    bool is_ok = m.get_dt_plugin()->mk_datatypes(dts.m_buffer.size(), dts.m_buffer.c_ptr(), sorts);
    if (!is_ok)
        return false;
    it  = m_datatypes.begin();
    for (unsigned i = 0; it != end; ++it, ++i) {
        sort * new_dt = sorts.get(i);
        (*it)->cache(m, s, new_dt);
        m.save_info(new_dt, *it, m_num_params, s);
        m.notify_new_dt(new_dt);
    }
    return true;
}

struct pdecl_manager::sort_info {
    psort_decl * m_decl;

    sort_info(pdecl_manager & m, psort_decl * d):
        m_decl(d) {
        m.inc_ref(d);
    }
    virtual ~sort_info() {}
    virtual unsigned obj_size() const { return sizeof(sort_info); }
    virtual void finalize(pdecl_manager & m) {
        m.dec_ref(m_decl);
    }
    virtual void display(std::ostream & out, pdecl_manager const & m) const = 0;
    virtual format * pp(pdecl_manager const & m) const = 0;
};

struct pdecl_manager::app_sort_info : public pdecl_manager::sort_info {
    ptr_vector<sort> m_args;
    
    app_sort_info(pdecl_manager & m, psort_decl * d, unsigned n, sort * const * s):
        sort_info(m, d),
        m_args(n, s) {
        m.m().inc_array_ref(n, s);
    }
    
    virtual ~app_sort_info() {}
    
    virtual unsigned obj_size() const { return sizeof(app_sort_info); }
    
    virtual void finalize(pdecl_manager & m) {
        sort_info::finalize(m);
        m.m().dec_array_ref(m_args.size(), m_args.c_ptr());
    }
    
    virtual void display(std::ostream & out, pdecl_manager const & m) const {
        if (m_args.empty()) {
            out << m_decl->get_name();
        }
        else {
            out << "(" << m_decl->get_name();
            for (unsigned i = 0; i < m_args.size(); i++) {
                out << " ";
                m.display(out, m_args[i]);
            }
            out << ")";
        }
    }
    
    virtual format * pp(pdecl_manager const & m) const {
        if (m_args.empty()) {
            return mk_string(m.m(), m_decl->get_name().str().c_str());
        }
        else {
            ptr_buffer<format> b;
            for (unsigned i = 0; i < m_args.size(); i++)
                b.push_back(m.pp(m_args[i]));
            return mk_seq1(m.m(), b.begin(), b.end(), f2f(), m_decl->get_name().str().c_str());
        }
    }
}; 

struct pdecl_manager::indexed_sort_info : public pdecl_manager::sort_info {
    svector<unsigned> m_indices;

    indexed_sort_info(pdecl_manager & m, psort_decl * d, unsigned n, unsigned const * s):
        sort_info(m, d),
        m_indices(n, s) {
    }

    virtual ~indexed_sort_info() {}

    virtual unsigned obj_size() const { return sizeof(indexed_sort_info); }

    virtual void display(std::ostream & out, pdecl_manager const & m) const {
        if (m_indices.empty()) {
            out << m_decl->get_name();
        }
        else {
            out << "(_ " << m_decl->get_name();
            for (unsigned i = 0; i < m_indices.size(); i++) {
                out << " " << m_indices[i];
            }
            out << ")";
        }
    }
    
    virtual format * pp(pdecl_manager const & m) const {
        if (m_indices.empty()) {
            return mk_string(m.m(), m_decl->get_name().str().c_str());
        }
        else {
            ptr_buffer<format> b;
            b.push_back(mk_string(m.m(), m_decl->get_name().str().c_str()));
            for (unsigned i = 0; i < m_indices.size(); i++)
                b.push_back(mk_unsigned(m.m(), m_indices[i]));
            return mk_seq1(m.m(), b.begin(), b.end(), f2f(), "_");
        }
    }
};

void pdecl_manager::init_list() {
    SASSERT(m_list == 0);
    psort * v   = mk_psort_var(1, 0);
    ptype T(v);
    ptype ListT(0);
    paccessor_decl * as[2]    = { mk_paccessor_decl(1, symbol("head"), T), 
                                  mk_paccessor_decl(1, symbol("tail"), ListT) };
    pconstructor_decl * cs[2] = { mk_pconstructor_decl(1, symbol("nil"), symbol("is-nil"), 0, 0),
                                  mk_pconstructor_decl(1, symbol("insert"), symbol("is-insert"), 2, as) };
    m_list = mk_pdatatype_decl(1, symbol("List"), 2, cs);
    inc_ref(m_list);
}

pdecl_manager::pdecl_manager(ast_manager & m):
    m_manager(m),
    m_allocator(m.get_allocator()),
    m_new_dt_eh(0) {
    m_list = 0;
    m_datatype_fid = m.mk_family_id("datatype");
}

pdecl_manager::~pdecl_manager() {
    dec_ref(m_list);
    reset_sort_info();
    SASSERT(m_sort2psort.empty());
    SASSERT(m_table.empty());
}

psort * pdecl_manager::mk_psort_cnst(sort * s) {
    psort * r = 0;
    if (m_sort2psort.find(s, r))
        return r;
    r = new (a().allocate(sizeof(psort_sort))) psort_sort(m_id_gen.mk(), *this, s);
    m_sort2psort.insert(s, r);
    return r;
}

psort * pdecl_manager::register_psort(psort * n) {
    TRACE("register_psort", tout << "registering psort...\n"; n->display(tout); tout << "\n";);
    psort * r = m_table.insert_if_not_there(n);
    if (r != n) {
        del_decl_core(n);
        return r;
    }
    return n;
}

psort * pdecl_manager::mk_psort_var(unsigned num_params, unsigned vidx) {
    psort_var * n = new (a().allocate(sizeof(psort_var))) psort_var(m_id_gen.mk(), num_params, vidx);
    return register_psort(n);
}

paccessor_decl * pdecl_manager::mk_paccessor_decl(unsigned num_params, symbol const & s, ptype const & p) {
    return new (a().allocate(sizeof(paccessor_decl))) paccessor_decl(m_id_gen.mk(), num_params, *this, s, p);
}
 
pconstructor_decl * pdecl_manager::mk_pconstructor_decl(unsigned num_params, 
                                                        symbol const & s, symbol const & r, unsigned num, paccessor_decl * const * as) {
    return new (a().allocate(sizeof(pconstructor_decl))) pconstructor_decl(m_id_gen.mk(), num_params, *this,
                                                                           s, r, num, as);
}

pdatatype_decl * pdecl_manager::mk_pdatatype_decl(unsigned num_params, symbol const & s, unsigned num, pconstructor_decl * const * cs) {
    return new (a().allocate(sizeof(pdatatype_decl))) pdatatype_decl(m_id_gen.mk(), num_params, *this,
                                                                     s, num, cs);
}

pdatatypes_decl * pdecl_manager::mk_pdatatypes_decl(unsigned num_params, unsigned num, pdatatype_decl * const * dts) {
    return new (a().allocate(sizeof(pdatatypes_decl))) pdatatypes_decl(m_id_gen.mk(), num_params, *this,
                                                                       num, dts);
}

psort * pdecl_manager::mk_psort_app(unsigned num_params, psort_decl * d, unsigned num_args, psort * const * args) {
    psort * n = new (a().allocate(sizeof(psort_app))) psort_app(m_id_gen.mk(), num_params, *this, d, num_args, args);
    return register_psort(n);
}

psort * pdecl_manager::mk_psort_app(psort_decl * d) {
    SASSERT(d->get_num_params() == 0 || d->get_num_params() == PSORT_DECL_VAR_PARAMS);
    sort * s = d->instantiate(*this, 0, static_cast<sort*const*>(0));
    if (s == 0)
        return 0;
    return mk_psort_cnst(s);
}

psort_decl * pdecl_manager::mk_psort_user_decl(unsigned num_params, symbol const & n, psort * def) {
    return new (a().allocate(sizeof(psort_user_decl))) psort_user_decl(m_id_gen.mk(), num_params, *this, n, def);
}

psort_decl * pdecl_manager::mk_psort_builtin_decl(symbol const & n, family_id fid, decl_kind k) {
    return new (a().allocate(sizeof(psort_builtin_decl))) psort_builtin_decl(m_id_gen.mk(), *this, n, fid, k);
}

sort * pdecl_manager::instantiate(psort * p, unsigned num, sort * const * args) {
    // ignoring stack overflows... sorts are not deeply nested
    return p->instantiate(*this, args);
}

void pdecl_manager::del_decl_core(pdecl * p) {
    TRACE("pdecl_manager", 
          tout << "del_decl_core:\n";
          if (p->is_psort()) static_cast<psort*>(p)->display(tout); 
          else static_cast<psort_decl*>(p)->display(tout);
          tout << "\n";);
    size_t sz = p->obj_size();
    m_id_gen.recycle(p->get_id());
    p->finalize(*this);
    p->~pdecl();
    m_allocator.deallocate(sz, p);
}

void pdecl_manager::del_decl(pdecl * p) {
    if (p->is_psort()) {
        psort * _p = static_cast<psort*>(p);
        if (_p->is_sort_wrapper())
            m_sort2psort.erase(static_cast<psort_sort*>(_p)->get_sort());
        else
            m_table.erase(_p);
    }
    del_decl_core(p); 
}

void pdecl_manager::del_decls() {
    while (!m_to_delete.empty()) {
        pdecl * p = m_to_delete.back();
        m_to_delete.pop_back();
        del_decl(p);
    }
}

psort_inst_cache * pdecl_manager::mk_inst_cache(unsigned num_params) {
    return new (a().allocate(sizeof(psort_inst_cache))) psort_inst_cache(num_params);
}

void pdecl_manager::del_inst_cache(psort_inst_cache * c) {
    if (c) {
        c->finalize(*this);
        c->~psort_inst_cache();
        a().deallocate(sizeof(psort_inst_cache), c);
    }
}

datatype_decl_plugin * pdecl_manager::get_dt_plugin() const {
    return static_cast<datatype_decl_plugin*>(m().get_plugin(m_datatype_fid));
}

void pdecl_manager::save_info(sort * s, psort_decl * d, unsigned num_args, sort * const * args) {
    if (m_sort2info.contains(s))
        return;
    sort_info * info = new (a().allocate(sizeof(app_sort_info))) app_sort_info(*this, d, num_args, args);
    m().inc_ref(s);
    m_sort2info.insert(s, info);
}

void pdecl_manager::save_info(sort * s, psort_decl * d, unsigned num_indices, unsigned const * indices) {
    if (m_sort2info.contains(s))
        return;
    sort_info * info = new (a().allocate(sizeof(indexed_sort_info))) indexed_sort_info(*this, d, num_indices, indices);
    m().inc_ref(s);
    m_sort2info.insert(s, info);
}

void pdecl_manager::reset_sort_info() {
    obj_map<sort, sort_info *>::iterator it  = m_sort2info.begin();
    obj_map<sort, sort_info *>::iterator end = m_sort2info.end();
    for (; it != end; ++it) {
        sort * s         = (*it).m_key;
        sort_info * info = (*it).m_value;
        m().dec_ref(s);
        unsigned sz = info->obj_size();
        info->finalize(*this);
        info->~sort_info();
        m_allocator.deallocate(sz, info);
    }
    m_sort2info.reset();
}

void pdecl_manager::display(std::ostream & out, sort * s) const {
    sort_info * info = 0;
    if (m_sort2info.find(s, info)) {
        info->display(out, *this);
        return;
    }
    out << s->get_name();
}

format * pdecl_manager::pp(sort * s) const {
    sort_info * info = 0;
    if (m_sort2info.find(s, info)) {
        return info->pp(*this);
    }
    unsigned num_params = s->get_num_parameters();
    if (s->get_family_id() != null_family_id && num_params > 0) {
        // Small hack to display FP and BitVec sorts that were not explicitly referenced by the user.
        unsigned i = 0;
        for (i = 0; i < num_params; i++) {
            if (!s->get_parameter(i).is_int())
                break;
        }
        if (i == num_params) {
            // all parameters are integer
            ptr_buffer<format> b;
            b.push_back(mk_string(m(), s->get_name().str().c_str()));
            for (unsigned i = 0; i < num_params; i++)
                b.push_back(mk_unsigned(m(), s->get_parameter(i).get_int()));
            return mk_seq1(m(), b.begin(), b.end(), f2f(), "_");
        }
    }
    return mk_string(m(), s->get_name().str().c_str());
}
