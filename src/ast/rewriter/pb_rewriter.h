/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    pb_rewriter.h

Abstract:

    Basic rewriting rules for PB constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2013-14-12

Notes:

--*/
#ifndef PB_REWRITER_H_
#define PB_REWRITER_H_

#include "ast/pb_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"
#include "util/params.h"
#include "util/lbool.h"


template<typename PBU>
class pb_rewriter_util {    
    PBU& m_util;
    void display(std::ostream& out, typename PBU::args_t& args, typename PBU::numeral& k, bool is_eq);
public:
    pb_rewriter_util(PBU& u) : m_util(u) {}
    void unique(typename PBU::args_t& args, typename PBU::numeral& k, bool is_eq);
    lbool normalize(typename PBU::args_t& args, typename PBU::numeral& k, bool is_eq);
    void prune(typename PBU::args_t& args, typename PBU::numeral& k, bool is_eq);
};

/**
   \brief Cheap rewrite rules for PB constraints
*/
class pb_rewriter {
    pb_util       m_util;
    vector<rational> m_coeffs;
    ptr_vector<expr> m_args;

    void validate_rewrite(func_decl* f, unsigned sz, expr*const* args, expr_ref& fml);
public:    
    pb_rewriter(ast_manager & m, params_ref const & p = params_ref()):
        m_util(m) {
    }
    ast_manager & m() const { return m_util.get_manager(); }
    family_id get_fid() const { return m_util.get_family_id(); }

    void updt_params(params_ref const & p) {}
    static void get_param_descrs(param_descrs & r) {}

    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);

    expr_ref translate_pb2lia(obj_map<expr,expr*>& vars, expr* fml);
    expr_ref mk_validate_rewrite(app_ref& e1, app_ref& e2);
    void dump_pb_rewrite(expr* fml);
};

#endif
