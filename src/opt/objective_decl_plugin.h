/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    objective_decl_plugin.h

Abstract:
    Abstract data-type for compound objectives.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-21

Notes:

--*/
#ifndef __OBJECTIVE_DECL_PLUGIN_H_
#define __OBJECTIVE_DECL_PLUGIN_H_

#include"ast.h"

namespace opt {

    enum obj_kind {
        OP_MINIMIZE, 
        OP_MAXIMIZE,
        OP_LEX,
        OP_BOX,
        OP_PARETO,
        LAST_OBJ_OP
    };

    enum objective_sort_kind {
        OBJECTIVE_SORT
    };
    
    class objective_decl_plugin : public decl_plugin {
    public:
        objective_decl_plugin();
        virtual ~objective_decl_plugin();
        
        virtual sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters);

        virtual decl_plugin * mk_fresh() { return alloc(objective_decl_plugin); }
        
        virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                         unsigned arity, sort * const * domain, sort * range);

        virtual void get_op_names(svector<builtin_name> & op_names, symbol const & logic);        

    private:
        symbol objective_decl_plugin::get_name(obj_kind k) const;
    };

    class objective_util {
        ast_manager& m;
        family_id m_fid;
    public:
        objective_util(ast_manager& m);
        family_id get_family_id() const { return m_fid; }
        app* mk_max(expr_ref& e);
        app* mk_min(expr_ref& e);
        app* mk_maxsat(symbol id);
        app* mk_lex(unsigned sz, expr * const * children);
        app* mk_box(unsigned sz, expr * const * children);
        app* mk_pareto(unsigned sz, expr * const * children);
    };
};

#endif
