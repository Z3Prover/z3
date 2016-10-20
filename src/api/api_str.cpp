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

	MK_BINARY(Z3_mk_str_concat, mk_c(c)->get_str_fid(), OP_STRCAT, SKIP);
	MK_UNARY(Z3_mk_str_length, mk_c(c)->get_str_fid(), OP_STRLEN, SKIP);
	MK_BINARY(Z3_mk_str_at, mk_c(c)->get_str_fid(), OP_STR_CHARAT, SKIP);
	// translate prefixof/suffixof to StartsWith/EndsWith
	// TODO string standardization might just remove StartsWith/EndsWith in future
	Z3_ast Z3_API Z3_mk_str_prefixof(Z3_context c, Z3_ast pre, Z3_ast full) {
		LOG_Z3_mk_str_prefixof(c, pre, full);
		Z3_TRY;
		RESET_ERROR_CODE();
		expr * args[2] = { to_expr(full), to_expr(pre) }; // reverse args
		ast * a = mk_c(c)->m().mk_app(mk_c(c)->get_str_fid(), OP_STR_STARTSWITH, 0, 0, 2, args);
		mk_c(c)->save_ast_trail(a);
		check_sorts(c, a);
		RETURN_Z3(of_ast(a));
		Z3_CATCH_RETURN(0);
	}
	Z3_ast Z3_API Z3_mk_str_suffixof(Z3_context c, Z3_ast suf, Z3_ast full) {
		LOG_Z3_mk_str_suffixof(c, suf, full);
		Z3_TRY;
		RESET_ERROR_CODE();
		expr * args[2] = { to_expr(full), to_expr(suf) }; // reverse args
		ast * a = mk_c(c)->m().mk_app(mk_c(c)->get_str_fid(), OP_STR_ENDSWITH, 0, 0, 2, args);
		mk_c(c)->save_ast_trail(a);
		check_sorts(c, a);
		RETURN_Z3(of_ast(a));
		Z3_CATCH_RETURN(0);
	}

	MK_BINARY(Z3_mk_str_contains, mk_c(c)->get_str_fid(), OP_STR_CONTAINS, SKIP);
	MK_TERNARY(Z3_mk_str_indexof, mk_c(c)->get_str_fid(), OP_STR_INDEXOF, SKIP);
	MK_TERNARY(Z3_mk_str_substr, mk_c(c)->get_str_fid(), OP_STR_SUBSTR, SKIP);
	MK_TERNARY(Z3_mk_str_replace, mk_c(c)->get_str_fid(), OP_STR_REPLACE, SKIP);

	Z3_ast Z3_API Z3_mk_str_to_regex(Z3_context c, Z3_string str) {
		LOG_Z3_mk_str_to_regex(c, str);
		Z3_TRY;
		RESET_ERROR_CODE();
		std::string s(str);
		app * a = mk_c(c)->strutil().mk_string(str);
		mk_c(c)->save_ast_trail(a);

		expr * args[1] = { to_expr(a) };
		ast * re = mk_c(c)->m().mk_app(mk_c(c)->get_str_fid(), OP_RE_STR2REGEX, 0, 0, 1, args);
		mk_c(c)->save_ast_trail(re);
		check_sorts(c, re);
		RETURN_Z3(of_ast(re));
		Z3_CATCH_RETURN(0);
	}

	MK_BINARY(Z3_mk_str_in_regex, mk_c(c)->get_str_fid(), OP_RE_REGEXIN, SKIP);
	MK_BINARY(Z3_mk_regex_concat, mk_c(c)->get_str_fid(), OP_RE_REGEXCONCAT, SKIP);
	MK_BINARY(Z3_mk_regex_union, mk_c(c)->get_str_fid(), OP_RE_REGEXUNION, SKIP);
	MK_UNARY(Z3_mk_regex_star, mk_c(c)->get_str_fid(), OP_RE_REGEXSTAR, SKIP);
	MK_UNARY(Z3_mk_regex_plus, mk_c(c)->get_str_fid(), OP_RE_REGEXPLUS, SKIP);

	Z3_ast Z3_API Z3_mk_regex_range(Z3_context c, Z3_string start, Z3_string end) {
		LOG_Z3_mk_regex_range(c, start, end);
		Z3_TRY;
		RESET_ERROR_CODE();

		std::string cStart(start);
		std::string cEnd(end);
		if(cStart.length() != 1 || cEnd.length() != 1) {
			SET_ERROR_CODE(Z3_INVALID_ARG);
			return 0;
		}

		app * a1 = mk_c(c)->strutil().mk_string(cStart);
		mk_c(c)->save_ast_trail(a1);
		app * a2 = mk_c(c)->strutil().mk_string(cEnd);
		mk_c(c)->save_ast_trail(a2);

		expr * args[2] = { to_expr(a1), to_expr(a2) };
		ast * range = mk_c(c)->m().mk_app(mk_c(c)->get_str_fid(), OP_RE_REGEXCHARRANGE, 0, 0, 2, args);
		mk_c(c)->save_ast_trail(range);
		check_sorts(c, range);
		RETURN_Z3(of_ast(range));

		Z3_CATCH_RETURN(0);
	}

};
