/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    value_compiler_extension.h

Abstract:

    Compiler extension for creating values (i.e., "interpreted" constants that
    are different any other constant).

Author:

    Leonardo de Moura (leonardo) 2006-10-31.

Revision History:

--*/
#ifndef _VALUE_COMPILER_EXTENSION_H_
#define _VALUE_COMPILER_EXTENSION_H_

#include"ast_compiler.h"

class value_compiler_extension : public ast_compiler_plugin {
    context & m_context;
public:
    value_compiler_extension(ast_manager & m, context & ctx):
        ast_compiler_plugin(m.get_family_id(symbol("interpreted_value"))),
        m_context(ctx) {
        ctx.register_plugin(this);
    }

    virtual ~value_compiler_extension() {
    }

    virtual bool compile_term(ast_compiler & c, const_ast * a, enode * & r) {
        SASSERT(a->get_decl()->get_family_id() == m_fid);
        const_decl_ast * d = a->get_decl();
        r = m_context.mk_interpreted_const(d);
        return true;
    }
};

#endif /* _VALUE_COMPILER_EXTENSION_H_ */

