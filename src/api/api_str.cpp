/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    api_str.cpp

Abstract:

    API for strings and regular expressions (Z3str2 implementation).

Author:

    Murphy Berzish (mtrberzi) 2016-10-03.

Revision History:

--*/
#include<iostream>
#include"z3.h"
#include"api_log_macros.h"
#include"api_context.h"
#include"api_util.h"
#include"ast_pp.h"

extern "C" {

	Z3_sort Z3_API Z3_mk_str_sort(Z3_context c) {
		Z3_TRY;
		LOG_Z3_mk_str_sort(c);
		RESET_ERROR_CODE();
		sort * ty = mk_c(c)->strutil().mk_string_sort();
		mk_c(c)->save_ast_trail(ty);
		RETURN_Z3(of_sort(ty));
		Z3_CATCH_RETURN(0);
	}

	Z3_bool Z3_API Z3_is_str_sort(Z3_context c, Z3_sort s) {
		Z3_TRY;
		LOG_Z3_is_str_sort(c, s);
		RESET_ERROR_CODE();
		bool result = mk_c(c)->strutil().is_str_sort(to_sort(s));
		return result?Z3_TRUE:Z3_FALSE;
		Z3_CATCH_RETURN(Z3_FALSE);
	}

	Z3_bool Z3_API Z3_is_str(Z3_context c, Z3_ast s) {
		Z3_TRY;
		LOG_Z3_is_str(c, s);
		RESET_ERROR_CODE();
		bool result = mk_c(c)->strutil().is_string(to_expr(s));
		return result ? Z3_TRUE : Z3_FALSE;
		Z3_CATCH_RETURN(Z3_FALSE);
	}

	Z3_string Z3_API Z3_get_str(Z3_context c, Z3_ast s) {
		Z3_TRY;
		LOG_Z3_get_str(c, s);
		RESET_ERROR_CODE();
		if (!mk_c(c)->strutil().is_string(to_expr(s))) {
			SET_ERROR_CODE(Z3_INVALID_ARG);
			return "";
		}
		std::string result = mk_c(c)->strutil().get_string_constant_value(to_expr(s));
		return mk_c(c)->mk_external_string(result);
		Z3_CATCH_RETURN("");
	}

	Z3_ast Z3_API Z3_mk_str(Z3_context c, Z3_string str) {
		Z3_TRY;
		LOG_Z3_mk_str(c, str);
		RESET_ERROR_CODE();
		std::string s(str);
		app * a = mk_c(c)->strutil().mk_string(str);
		mk_c(c)->save_ast_trail(a);
		RETURN_Z3(of_ast(a));
		Z3_CATCH_RETURN(0);
	}

};
