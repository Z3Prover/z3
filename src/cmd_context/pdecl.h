/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    pdecl.h

Abstract:

    Parametric declarations for SMT-LIB 2.0 + inductive data-types.

Author:

    Leonardo de Moura (leonardo) 2011-03-02.

Revision History:

--*/
#ifndef PDECL_H_
#define PDECL_H_

#include "ast/ast.h"
#include "util/obj_hashtable.h"
#include "util/dictionary.h"
#include "ast/format.h"
#include "ast/datatype_decl_plugin.h"

class pdecl_manager;

class pdecl {
protected:
    friend class pdecl_manager;
    unsigned m_id;
    unsigned m_num_params;
    unsigned m_ref_count;
    void inc_ref() { m_ref_count++; }
    void dec_ref() { SASSERT(m_ref_count > 0); --m_ref_count; }
    virtual bool is_psort() const { return false; }
    virtual size_t obj_size() const { UNREACHABLE(); return sizeof(*this); }
    pdecl(unsigned id, unsigned num_params):m_id(id), m_num_params(num_params), m_ref_count(0) {}
    virtual void finalize(pdecl_manager & m) {}
    virtual ~pdecl() {}
public:
    virtual bool check_num_params(pdecl * other) const { return m_num_params == other->m_num_params; }
    unsigned get_num_params() const { return m_num_params; }
    unsigned get_id() const { return m_id; }
    unsigned get_ref_count() const { return m_ref_count; }
    unsigned hash() const { return m_id; }
    virtual void display(std::ostream & out) const {}
    virtual void reset_cache(pdecl_manager& m) {}
};

class psort_inst_cache;

#if defined(__APPLE__) && defined(__MACH__)
// CMW: for some unknown reason, llvm on macOS does not like the name `psort'
#define psort Z3_psort
#endif

/**
   \brief Parametric sorts.
*/
class psort : public pdecl {
protected:
    psort_inst_cache * m_inst_cache;
    friend class pdecl_manager;
    psort(unsigned id, unsigned num_params):pdecl(id, num_params), m_inst_cache(nullptr) {}
    bool is_psort() const override { return true; }
    void finalize(pdecl_manager & m) override;
    ~psort() override {}
    virtual void cache(pdecl_manager & m, sort * const * s, sort * r);
    virtual sort * find(sort * const * s) const;
public:
    virtual bool is_sort_wrapper() const { return false; }
    virtual sort * instantiate(pdecl_manager & m, sort * const * s) { return nullptr; }
    // we use hash-consing for psorts.
    virtual char const * hcons_kind() const { UNREACHABLE(); return nullptr; }
    virtual unsigned hcons_hash() const { UNREACHABLE(); return 0; }
    virtual bool hcons_eq(psort const * other) const { UNREACHABLE(); return false; }
    void reset_cache(pdecl_manager& m) override;
};

// for hash consing
struct psort_hash_proc { unsigned operator()(psort * p) const { return p->hcons_hash(); } };
struct psort_eq_proc { bool operator()(psort * p1, psort * p2) const { return p1->hcons_eq(p2); } };
typedef ptr_hashtable<psort, psort_hash_proc, psort_eq_proc> psort_table;

#define PSORT_DECL_VAR_PARAMS UINT_MAX

typedef enum { PSORT_BASE = 0, PSORT_USER, PSORT_BUILTIN, PSORT_DT } psort_decl_kind;

class psort_decl : public pdecl {
protected:
    friend class pdecl_manager;
    symbol                        m_name;
    psort_decl_kind               m_psort_kind;
    psort_inst_cache *            m_inst_cache;
    void cache(pdecl_manager & m, sort * const * s, sort * r);
    sort * find(sort * const * s);
    psort_decl(unsigned id, unsigned num_params, pdecl_manager & m, symbol const & n);
    void finalize(pdecl_manager & m) override;
    ~psort_decl() override {}
public:
    virtual sort * instantiate(pdecl_manager & m, unsigned n, sort * const * s) = 0;
    virtual sort * instantiate(pdecl_manager & m, unsigned n, unsigned const * s) { return nullptr; }
    virtual sort * instantiate(pdecl_manager & m) { return instantiate(m, 0, static_cast<sort*const*>(nullptr)); }
    // return true if the declaration accepts a variable number of parameters.
    // Only builtin declarations can have a variable number of parameters.
    bool has_var_params() const { return m_num_params == PSORT_DECL_VAR_PARAMS; }
    symbol const & get_name() const { return m_name; }
    void reset_cache(pdecl_manager& m) override;
    bool is_user_decl() const { return m_psort_kind == PSORT_USER; }
    bool is_builtin_decl() const { return m_psort_kind == PSORT_BUILTIN; }
    bool is_dt_decl() const { return m_psort_kind == PSORT_DT; }
};

class psort_user_decl : public psort_decl {
protected:
    friend class pdecl_manager;
    psort * m_def;
    psort_user_decl(unsigned id, unsigned num_params, pdecl_manager & m, symbol const & n, psort * p);
    size_t obj_size() const override { return sizeof(psort_user_decl); }
    void finalize(pdecl_manager & m) override;
    ~psort_user_decl() override {}
public:
    sort * instantiate(pdecl_manager & m, unsigned n, sort * const * s) override;
    void display(std::ostream & out) const override;
};
 
class psort_builtin_decl : public psort_decl {
protected:
    friend class pdecl_manager;
    family_id m_fid;
    decl_kind m_kind;
    psort_builtin_decl(unsigned id, pdecl_manager & m, symbol const & n, family_id fid, decl_kind k);
    size_t obj_size() const override { return sizeof(psort_builtin_decl); }
    ~psort_builtin_decl() override {}
public:
    sort * instantiate(pdecl_manager & m, unsigned n, sort * const * s) override;
    sort * instantiate(pdecl_manager & m, unsigned n, unsigned const * s) override;
    void display(std::ostream & out) const override;
};

class psort_dt_decl : public psort_decl {
protected:
    friend class pdecl_manager;
    psort_dt_decl(unsigned id, unsigned num_params, pdecl_manager & m, symbol const & n);
    size_t obj_size() const override { return sizeof(psort_dt_decl); }
    ~psort_dt_decl() override {}
public:
    sort * instantiate(pdecl_manager & m, unsigned n, sort * const * s) override;
    void display(std::ostream & out) const override;
};


class pdatatypes_decl;
class pdatatype_decl;
class pconstructor_decl;
class paccessor_decl;

enum ptype_kind {
    PTR_PSORT,       // psort
    PTR_REC_REF,     // recursive reference
    PTR_MISSING_REF  // a symbol, it is useful for building parsers.
};

class ptype {
    ptype_kind m_kind;
    union {
        psort * m_sort;
        int    m_idx;
    };
    symbol     m_missing_ref;
public:
    ptype():m_kind(PTR_PSORT), m_sort(nullptr) {}
    ptype(int idx):m_kind(PTR_REC_REF), m_idx(idx) {}
    ptype(psort * s):m_kind(PTR_PSORT), m_sort(s) {}
    ptype(symbol const & s):m_kind(PTR_MISSING_REF), m_missing_ref(s) {}
    ptype_kind kind() const { return m_kind; }
    psort * get_psort() const { SASSERT(kind() == PTR_PSORT); return m_sort; }
    int get_idx() const { SASSERT(kind() == PTR_REC_REF); return m_idx; }
    symbol const & get_missing_ref() const { SASSERT(kind() == PTR_MISSING_REF); return m_missing_ref; }
    void display(std::ostream & out, pdatatype_decl const * const * dts) const;
};

class paccessor_decl : public pdecl {
    friend class pdecl_manager;
    friend class pconstructor_decl;
    friend class pdatatype_decl;
    symbol   m_name;
    ptype    m_type;
    paccessor_decl(unsigned id, unsigned num_params, pdecl_manager & m, symbol const & n, ptype const & r);
    void finalize(pdecl_manager & m) override;
    size_t obj_size() const override { return sizeof(paccessor_decl); }
    bool has_missing_refs(symbol & missing) const;
    bool fix_missing_refs(dictionary<int> const & symbol2idx, symbol & missing);
    accessor_decl * instantiate_decl(pdecl_manager & m, sort * const * s);
    symbol const & get_name() const { return m_name; }
    ptype const & get_type() const { return m_type; }
    ~paccessor_decl() override {}
public:
    void display(std::ostream & out) const override { pdecl::display(out); }
    void display(std::ostream & out, pdatatype_decl const * const * dts) const;
};

class pconstructor_decl : public pdecl {
    friend class pdecl_manager;
    friend class pdatatype_decl;
    symbol                     m_name;
    symbol                     m_recogniser_name;
    ptr_vector<paccessor_decl> m_accessors;
    pconstructor_decl(unsigned id, unsigned num_params, pdecl_manager & m,
                      symbol const & n, symbol const & r, unsigned num_accessors, paccessor_decl * const * accessors);
    void finalize(pdecl_manager & m) override;
    size_t obj_size() const override { return sizeof(pconstructor_decl); }
    bool has_missing_refs(symbol & missing) const;
    bool fix_missing_refs(dictionary<int> const & symbol2idx, symbol & missing);
    symbol const & get_name() const { return m_name; }
    symbol const & get_recognizer_name() const { return m_recogniser_name; }
    constructor_decl * instantiate_decl(pdecl_manager & m, sort * const * s);
    ~pconstructor_decl() override {}
public:
    void display(std::ostream & out) const override { pdecl::display(out); }
    void display(std::ostream & out, pdatatype_decl const * const * dts) const;
};

class pdatatype_decl : public psort_decl {
    friend class pdecl_manager;
    friend class pdatatypes_decl;
    ptr_vector<pconstructor_decl> m_constructors;
    pdatatypes_decl *             m_parent;
    pdatatype_decl(unsigned id, unsigned num_params, pdecl_manager & m, symbol const & n,
                   unsigned num_constructors, pconstructor_decl * const * constructors);
    void finalize(pdecl_manager & m) override;
    size_t obj_size() const override { return sizeof(pdatatype_decl); }
    bool fix_missing_refs(dictionary<int> const & symbol2idx, symbol & missing);
    datatype_decl * instantiate_decl(pdecl_manager & m, sort * const * s);
    ~pdatatype_decl() override {}
public:
    sort * instantiate(pdecl_manager & m, unsigned n, sort * const * s) override;
    void display(std::ostream & out) const override;
    bool has_missing_refs(symbol & missing) const;
    bool has_duplicate_accessors(symbol & repeated) const;
    bool commit(pdecl_manager& m);
};

/**
   \brief Represents a set of parametric mutually recursive inductive data-types.
*/
class pdatatypes_decl : public pdecl {
    friend class pdecl_manager;
    friend class pdatatype_decl;
    ptr_vector<pdatatype_decl> m_datatypes;
    pdatatypes_decl(unsigned id, unsigned num_params, pdecl_manager & m, unsigned num_datatypes, pdatatype_decl * const * dts);
    void finalize(pdecl_manager & m) override;
    size_t obj_size() const override { return sizeof(pdatatypes_decl); }
    bool fix_missing_refs(symbol & missing);
    bool instantiate(pdecl_manager & m, sort * const * s);
    ~pdatatypes_decl() override {}
public:
    pdatatype_decl const * const * children() const { return m_datatypes.c_ptr(); }
    pdatatype_decl * const * begin() const { return m_datatypes.begin(); }
    pdatatype_decl * const * end() const { return m_datatypes.end(); }
    // commit declaration 
    bool commit(pdecl_manager& m);
};

class new_datatype_eh {
public:
    virtual ~new_datatype_eh() {}
    virtual void operator()(sort * dt, pdecl* pd) = 0;
};

class pdecl_manager {
    ast_manager &                m_manager;
    small_object_allocator &     m_allocator;
    id_gen                       m_id_gen;
    obj_map<sort, psort *>       m_sort2psort;
    psort_table                  m_table;
    ptr_vector<pdecl>            m_to_delete;
    pdatatype_decl *             m_list;
    family_id                    m_datatype_fid;
    new_datatype_eh *            m_new_dt_eh;

    struct sort_info;
    struct app_sort_info;
    struct indexed_sort_info;

    obj_map<sort, sort_info *>   m_sort2info; // for pretty printing sorts

    void init_list();
    void del_decl_core(pdecl * p);
    void del_decl(pdecl * p);
    void del_decls();
    psort * register_psort(psort * n);
    void reset_sort_info();
public:
    pdecl_manager(ast_manager & m);
    ~pdecl_manager();
    ast_manager & m() const { return m_manager; }
    small_object_allocator & a() const { return m_allocator; }
    family_id get_datatype_fid() const { return m_datatype_fid; }
    void set_new_datatype_eh(new_datatype_eh * eh) { m_new_dt_eh = eh; }
    psort * mk_psort_cnst(sort * s);
    psort * mk_psort_var(unsigned num_params, unsigned vidx);
    psort * mk_psort_app(unsigned num_params, psort_decl * d, unsigned num_args, psort * const * args);
    psort * mk_psort_app(psort_decl * d);
    psort_decl * mk_psort_dt_decl(unsigned num_params, symbol const & n);
    psort_decl * mk_psort_user_decl(unsigned num_params, symbol const & n, psort * def);
    psort_decl * mk_psort_builtin_decl(symbol const & n, family_id fid, decl_kind k);
    paccessor_decl * mk_paccessor_decl(unsigned num_params, symbol const & s, ptype const & p);
    pconstructor_decl * mk_pconstructor_decl(unsigned num_params, symbol const & s, symbol const & r, unsigned num, paccessor_decl * const * as);
    pdatatype_decl * mk_pdatatype_decl(unsigned num_params, symbol const & s, unsigned num, pconstructor_decl * const * cs);
    pdatatypes_decl * mk_pdatatypes_decl(unsigned num_params, unsigned num, pdatatype_decl * const * dts);
    pdatatype_decl * mk_plist_decl() { if (!m_list) init_list(); return m_list; }
    bool fix_missing_refs(pdatatypes_decl * s, symbol & missing) { return s->fix_missing_refs(missing); }
    sort * instantiate_datatype(psort_decl* p, symbol const& name, unsigned n, sort * const* s);
    sort * instantiate(psort * s, unsigned num, sort * const * args);

    void lazy_dec_ref(pdecl * p) { p->dec_ref(); if (p->get_ref_count() == 0) m_to_delete.push_back(p); }
    template<typename T>
    void lazy_dec_ref(unsigned num, T * const * ps) { for (unsigned i = 0; i < num; i++) lazy_dec_ref(ps[i]); }
    void inc_ref(pdecl * p) { if (p) { p->inc_ref(); } }
    void dec_ref(pdecl * p) { if (p) { lazy_dec_ref(p); del_decls(); } }
    template<typename T>
    void inc_ref(unsigned num, T * const * ps) { for (unsigned i = 0; i < num; i++) inc_ref(ps[i]); }
    template<typename T>
    void dec_ref(unsigned num, T * const * ps) { lazy_dec_ref(num, ps); del_decls(); }
    psort_inst_cache * mk_inst_cache(unsigned num_params);
    void del_inst_cache(psort_inst_cache * c);
    void notify_new_dt(sort * dt, pdecl* pd) { if (m_new_dt_eh) (*m_new_dt_eh)(dt, pd); }
    datatype_decl_plugin * get_dt_plugin() const;

    void save_info(sort * s, psort_decl * d, unsigned num_args, sort * const * args);
    void save_info(sort * s, psort_decl * d, unsigned num_indices, unsigned const * indices);
    void display(std::ostream & out, sort * s) const;
    format_ns::format * pp(sort * s) const;
};


typedef obj_ref<pdecl, pdecl_manager>             pdecl_ref;
typedef obj_ref<psort, pdecl_manager>             psort_ref;
typedef obj_ref<paccessor_decl, pdecl_manager>    paccessor_decl_ref;
typedef obj_ref<pconstructor_decl, pdecl_manager> pconstructor_decl_ref;
typedef obj_ref<pdatatype_decl, pdecl_manager>    pdatatype_decl_ref;
typedef obj_ref<pdatatypes_decl, pdecl_manager>   pdatatypes_decl_ref;

typedef ref_vector<pdecl, pdecl_manager>          pdecl_ref_vector;
typedef ref_vector<psort_decl, pdecl_manager>     psort_decl_ref_vector;
typedef ref_vector<psort, pdecl_manager>          psort_ref_vector;

typedef ref_buffer<paccessor_decl, pdecl_manager>    paccessor_decl_ref_buffer;
typedef ref_buffer<pconstructor_decl, pdecl_manager> pconstructor_decl_ref_buffer;
typedef ref_buffer<pdatatype_decl, pdecl_manager>    pdatatype_decl_ref_buffer;
typedef ref_buffer<pdatatypes_decl, pdecl_manager>   pdatatypes_decl_ref_buffer;

#endif
