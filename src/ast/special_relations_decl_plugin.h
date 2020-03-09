/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    special_relations_decl_plugin.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2015-15-9.
    Ashutosh Gupta 2016

Revision History:

--*/
#ifndef SPECIAL_RELATIONS_DECL_PLUGIN_H_
#define SPECIAL_RELATIONS_DECL_PLUGIN_H_

#include "ast/ast.h"


enum special_relations_op_kind {
    OP_SPECIAL_RELATION_LO,
    OP_SPECIAL_RELATION_PO,
    OP_SPECIAL_RELATION_PLO,
    OP_SPECIAL_RELATION_TO,
    OP_SPECIAL_RELATION_TC,
    LAST_SPECIAL_RELATIONS_OP
};

class special_relations_decl_plugin : public decl_plugin {
    symbol m_lo;
    symbol m_po;
    symbol m_plo;
    symbol m_to;
    symbol m_tc;
public:
    special_relations_decl_plugin();

    ~special_relations_decl_plugin() override {}

    decl_plugin * mk_fresh() override {
        return alloc(special_relations_decl_plugin);
    }
    
    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                             unsigned arity, sort * const * domain, sort * range) override;

    void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;
    
    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override { return nullptr; }
};

enum sr_property {
    sr_none          = 0x00,
    sr_transitive    = 0x01,                              // Rxy & Ryz -> Rxz
    sr_reflexive     = 0x02,                              // Rxx
    sr_antisymmetric = 0x04,                              // Rxy & Ryx -> x = y
    sr_lefttree      = 0x08,                              // Ryx & Rzx -> Ryz | Rzy
    sr_righttree     = 0x10,                              // Rxy & Rxz -> Ryx | Rzy
    sr_total         = 0x20,                              // Rxy | Ryx
    sr_po            = 0x01 | 0x02 | 0x04,                // partial order
    sr_to            = 0x01 | 0x02 | 0x04 | 0x10,         // right-tree
    sr_plo           = 0x01 | 0x02 | 0x04 | 0x08 | 0x10,  // piecewise linear order
    sr_lo            = 0x01 | 0x02 | 0x04 | 0x20,         // linear order
    sr_tc            = 0x40,                              // transitive closure of relation
};

class special_relations_util {
    ast_manager& m;
    mutable family_id    m_fid;
    func_decl* mk_rel_decl(func_decl* f, decl_kind k) {
        parameter p(f); SASSERT(f->get_arity() == 2); 
        return m.mk_func_decl(fid(), k, 1, &p, 2, f->get_domain(), f->get_range()); 
    }    
    family_id fid() const {        
        if (null_family_id == m_fid) m_fid = m.get_family_id("specrels");
        return m_fid;
    }
public:
    special_relations_util(ast_manager& m) : m(m), m_fid(null_family_id) { }
    
    bool is_special_relation(func_decl* f) const { return f->get_family_id() == fid(); }
    bool is_special_relation(app* e) const { return is_special_relation(e->get_decl()); }
    sr_property get_property(func_decl* f) const;
    sr_property get_property(app* e) const { return get_property(e->get_decl()); }

    func_decl* mk_to_decl(func_decl* f) { return mk_rel_decl(f, OP_SPECIAL_RELATION_TO); }
    func_decl* mk_po_decl(func_decl* f) { return mk_rel_decl(f, OP_SPECIAL_RELATION_PO); }
    func_decl* mk_plo_decl(func_decl* f) { return mk_rel_decl(f, OP_SPECIAL_RELATION_PLO); }
    func_decl* mk_lo_decl(func_decl* f) { return mk_rel_decl(f, OP_SPECIAL_RELATION_LO); }
    func_decl* mk_tc_decl(func_decl* f) { return mk_rel_decl(f, OP_SPECIAL_RELATION_TC); }

    bool is_lo(expr const * e) const { return is_app_of(e, fid(), OP_SPECIAL_RELATION_LO); }
    bool is_po(expr const * e) const { return is_app_of(e, fid(), OP_SPECIAL_RELATION_PO); }
    bool is_plo(expr const * e) const { return is_app_of(e, fid(), OP_SPECIAL_RELATION_PLO); }
    bool is_to(expr const * e) const { return is_app_of(e, fid(), OP_SPECIAL_RELATION_TO); }
    bool is_tc(expr const * e) const { return is_app_of(e, fid(), OP_SPECIAL_RELATION_TC); }
    
    app * mk_lo (expr * arg1, expr * arg2) { return m.mk_app( fid(), OP_SPECIAL_RELATION_LO,  arg1, arg2); }
    app * mk_po (expr * arg1, expr * arg2) { return m.mk_app( fid(), OP_SPECIAL_RELATION_PO,  arg1, arg2); }
    app * mk_plo(expr * arg1, expr * arg2) { return m.mk_app( fid(), OP_SPECIAL_RELATION_PLO, arg1, arg2); }
    app * mk_to (expr * arg1, expr * arg2) { return m.mk_app( fid(), OP_SPECIAL_RELATION_TO,  arg1, arg2); }

};


#endif /* SPECIAL_RELATIONS_DECL_PLUGIN_H_ */
