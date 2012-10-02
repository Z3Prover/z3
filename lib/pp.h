/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    pp.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-20.

Revision History:

--*/
#ifndef _PP_H_
#define _PP_H_

#include"format.h"
#include"pp_params.h"

void set_pp_default_params(pp_params const & p);
void register_pp_params(ini_params & p);

pp_params const & get_pp_default_params();

void pp(std::ostream & out, format_ns::format * f, ast_manager & m, pp_params const & p);
void pp(std::ostream & out, format_ns::format * f, ast_manager & m);

#endif /* _PP_H_ */

