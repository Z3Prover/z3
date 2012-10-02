// Automatically generated file, generator: api.py
using System;
using System.Collections.Generic;
using System.Text;
using System.Runtime.InteropServices;

#pragma warning disable 1591

namespace Microsoft.Z3
{
    using Z3_config = System.IntPtr;
    using Z3_context = System.IntPtr;
    using Z3_ast = System.IntPtr;
    using Z3_app = System.IntPtr;
    using Z3_sort = System.IntPtr;
    using Z3_func_decl = System.IntPtr;
    using Z3_pattern = System.IntPtr;
    using Z3_model = System.IntPtr;
    using Z3_literals = System.IntPtr;
    using Z3_constructor = System.IntPtr;
    using Z3_constructor_list = System.IntPtr;
    using Z3_theory = System.IntPtr;
    using Z3_theory_data = System.IntPtr;
    using Z3_solver = System.IntPtr;
    using Z3_goal = System.IntPtr;
    using Z3_tactic = System.IntPtr;
    using Z3_params = System.IntPtr;
    using Z3_probe = System.IntPtr;
    using Z3_stats = System.IntPtr;
    using Z3_ast_vector = System.IntPtr;
    using Z3_ast_map = System.IntPtr;
    using Z3_apply_result = System.IntPtr;
    using Z3_func_interp = System.IntPtr;
    using Z3_func_entry = System.IntPtr;
    using Z3_fixedpoint = System.IntPtr;
    using Z3_param_descrs = System.IntPtr;

    public class Native
    {

        [UnmanagedFunctionPointer(CallingConvention.Cdecl)]
        public delegate void Z3_error_handler(Z3_context c, Z3_error_code e);

        public unsafe class LIB
        {
            #if DEBUG
            const string Z3_DLL_NAME = "z3_dbg.dll";
            #else
            const string Z3_DLL_NAME = "z3.dll";
            #endif

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_set_error_handler(Z3_context a0, Z3_error_handler a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_config Z3_mk_config();

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_del_config(Z3_config a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_set_param_value(Z3_config a0, string a1, string a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_context Z3_mk_context(Z3_config a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_context Z3_mk_context_rc(Z3_config a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_set_logic(Z3_context a0, string a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_del_context(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_inc_ref(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_dec_ref(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_toggle_warning_messages(int a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_update_param_value(Z3_context a0, string a1, string a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_get_param_value(Z3_context a0, string a1, out IntPtr a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_mk_int_symbol(Z3_context a0, int a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_mk_string_symbol(Z3_context a0, string a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_is_eq_sort(Z3_context a0, Z3_sort a1, Z3_sort a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_mk_uninterpreted_sort(Z3_context a0, IntPtr a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_mk_bool_sort(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_mk_int_sort(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_mk_real_sort(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_mk_bv_sort(Z3_context a0, uint a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_mk_array_sort(Z3_context a0, Z3_sort a1, Z3_sort a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_mk_tuple_sort(Z3_context a0, IntPtr a1, uint a2, [In] IntPtr[] a3, [In] Z3_sort[] a4, [In, Out] ref Z3_func_decl a5, [Out] Z3_func_decl[] a6);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_mk_enumeration_sort(Z3_context a0, IntPtr a1, uint a2, [In] IntPtr[] a3, [Out] Z3_func_decl[] a4, [Out] Z3_func_decl[] a5);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_mk_list_sort(Z3_context a0, IntPtr a1, Z3_sort a2, [In, Out] ref Z3_func_decl a3, [In, Out] ref Z3_func_decl a4, [In, Out] ref Z3_func_decl a5, [In, Out] ref Z3_func_decl a6, [In, Out] ref Z3_func_decl a7, [In, Out] ref Z3_func_decl a8);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_constructor Z3_mk_constructor(Z3_context a0, IntPtr a1, IntPtr a2, uint a3, [In] IntPtr[] a4, [In] Z3_sort[] a5, [In] uint[] a6);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_query_constructor(Z3_context a0, Z3_constructor a1, uint a2, [In, Out] ref Z3_func_decl a3, [In, Out] ref Z3_func_decl a4, [Out] Z3_func_decl[] a5);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_del_constructor(Z3_context a0, Z3_constructor a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_mk_datatype(Z3_context a0, IntPtr a1, uint a2, [In, Out] Z3_constructor[] a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_constructor_list Z3_mk_constructor_list(Z3_context a0, uint a1, [In] Z3_constructor[] a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_del_constructor_list(Z3_context a0, Z3_constructor_list a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_mk_datatypes(Z3_context a0, uint a1, [In] IntPtr[] a2, [Out] Z3_sort[] a3, [In, Out] Z3_constructor_list[] a4);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_is_eq_ast(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_is_eq_func_decl(Z3_context a0, Z3_func_decl a1, Z3_func_decl a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_func_decl Z3_mk_func_decl(Z3_context a0, IntPtr a1, uint a2, [In] Z3_sort[] a3, Z3_sort a4);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_app(Z3_context a0, Z3_func_decl a1, uint a2, [In] Z3_ast[] a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_const(Z3_context a0, IntPtr a1, Z3_sort a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_label(Z3_context a0, IntPtr a1, int a2, Z3_ast a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_func_decl Z3_mk_fresh_func_decl(Z3_context a0, string a1, uint a2, [In] Z3_sort[] a3, Z3_sort a4);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_fresh_const(Z3_context a0, string a1, Z3_sort a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_true(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_false(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_eq(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_distinct(Z3_context a0, uint a1, [In] Z3_ast[] a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_not(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_ite(Z3_context a0, Z3_ast a1, Z3_ast a2, Z3_ast a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_iff(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_implies(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_xor(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_and(Z3_context a0, uint a1, [In] Z3_ast[] a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_or(Z3_context a0, uint a1, [In] Z3_ast[] a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_add(Z3_context a0, uint a1, [In] Z3_ast[] a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_mul(Z3_context a0, uint a1, [In] Z3_ast[] a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_sub(Z3_context a0, uint a1, [In] Z3_ast[] a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_unary_minus(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_div(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_mod(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_rem(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_power(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_is_algebraic_number(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_get_algebraic_number_lower(Z3_context a0, Z3_ast a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_get_algebraic_number_upper(Z3_context a0, Z3_ast a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_lt(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_le(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_gt(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_ge(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_int2real(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_real2int(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_is_int(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvnot(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvredand(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvredor(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvand(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvor(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvxor(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvnand(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvnor(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvxnor(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvneg(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvadd(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvsub(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvmul(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvudiv(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvsdiv(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvurem(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvsrem(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvsmod(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvult(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvslt(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvule(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvsle(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvuge(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvsge(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvugt(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvsgt(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_concat(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_extract(Z3_context a0, uint a1, uint a2, Z3_ast a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_sign_ext(Z3_context a0, uint a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_zero_ext(Z3_context a0, uint a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_repeat(Z3_context a0, uint a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvshl(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvlshr(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvashr(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_rotate_left(Z3_context a0, uint a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_rotate_right(Z3_context a0, uint a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_ext_rotate_left(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_ext_rotate_right(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_int2bv(Z3_context a0, uint a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bv2int(Z3_context a0, Z3_ast a1, int a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvadd_no_overflow(Z3_context a0, Z3_ast a1, Z3_ast a2, int a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvadd_no_underflow(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvsub_no_overflow(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvsub_no_underflow(Z3_context a0, Z3_ast a1, Z3_ast a2, int a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvsdiv_no_overflow(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvneg_no_overflow(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvmul_no_overflow(Z3_context a0, Z3_ast a1, Z3_ast a2, int a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bvmul_no_underflow(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_select(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_store(Z3_context a0, Z3_ast a1, Z3_ast a2, Z3_ast a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_const_array(Z3_context a0, Z3_sort a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_map(Z3_context a0, Z3_func_decl a1, uint a2, [In] Z3_ast[] a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_array_default(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_mk_set_sort(Z3_context a0, Z3_sort a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_empty_set(Z3_context a0, Z3_sort a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_full_set(Z3_context a0, Z3_sort a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_set_add(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_set_del(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_set_union(Z3_context a0, uint a1, [In] Z3_ast[] a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_set_intersect(Z3_context a0, uint a1, [In] Z3_ast[] a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_set_difference(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_set_complement(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_set_member(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_set_subset(Z3_context a0, Z3_ast a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_numeral(Z3_context a0, string a1, Z3_sort a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_real(Z3_context a0, int a1, int a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_int(Z3_context a0, int a1, Z3_sort a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_unsigned_int(Z3_context a0, uint a1, Z3_sort a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_int64(Z3_context a0, Int64 a1, Z3_sort a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_unsigned_int64(Z3_context a0, UInt64 a1, Z3_sort a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_pattern Z3_mk_pattern(Z3_context a0, uint a1, [In] Z3_ast[] a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_bound(Z3_context a0, uint a1, Z3_sort a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_forall(Z3_context a0, uint a1, uint a2, [In] Z3_pattern[] a3, uint a4, [In] Z3_sort[] a5, [In] IntPtr[] a6, Z3_ast a7);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_exists(Z3_context a0, uint a1, uint a2, [In] Z3_pattern[] a3, uint a4, [In] Z3_sort[] a5, [In] IntPtr[] a6, Z3_ast a7);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_quantifier(Z3_context a0, int a1, uint a2, uint a3, [In] Z3_pattern[] a4, uint a5, [In] Z3_sort[] a6, [In] IntPtr[] a7, Z3_ast a8);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_quantifier_ex(Z3_context a0, int a1, uint a2, IntPtr a3, IntPtr a4, uint a5, [In] Z3_pattern[] a6, uint a7, [In] Z3_ast[] a8, uint a9, [In] Z3_sort[] a10, [In] IntPtr[] a11, Z3_ast a12);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_forall_const(Z3_context a0, uint a1, uint a2, [In] Z3_app[] a3, uint a4, [In] Z3_pattern[] a5, Z3_ast a6);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_exists_const(Z3_context a0, uint a1, uint a2, [In] Z3_app[] a3, uint a4, [In] Z3_pattern[] a5, Z3_ast a6);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_quantifier_const(Z3_context a0, int a1, uint a2, uint a3, [In] Z3_app[] a4, uint a5, [In] Z3_pattern[] a6, Z3_ast a7);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_mk_quantifier_const_ex(Z3_context a0, int a1, uint a2, IntPtr a3, IntPtr a4, uint a5, [In] Z3_app[] a6, uint a7, [In] Z3_pattern[] a8, uint a9, [In] Z3_ast[] a10, Z3_ast a11);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_ast_id(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_func_decl_id(Z3_context a0, Z3_func_decl a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_sort_id(Z3_context a0, Z3_sort a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_is_well_sorted(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_symbol_kind(Z3_context a0, IntPtr a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_get_symbol_int(Z3_context a0, IntPtr a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_get_symbol_string(Z3_context a0, IntPtr a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_ast_kind(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_ast_hash(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_get_numeral_string(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_get_numeral_decimal_string(Z3_context a0, Z3_ast a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_get_numerator(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_get_denominator(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_get_numeral_small(Z3_context a0, Z3_ast a1, [In, Out] ref Int64 a2, [In, Out] ref Int64 a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_get_numeral_int(Z3_context a0, Z3_ast a1, [In, Out] ref int a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_get_numeral_uint(Z3_context a0, Z3_ast a1, [In, Out] ref uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_get_numeral_uint64(Z3_context a0, Z3_ast a1, [In, Out] ref UInt64 a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_get_numeral_int64(Z3_context a0, Z3_ast a1, [In, Out] ref Int64 a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_get_numeral_rational_int64(Z3_context a0, Z3_ast a1, [In, Out] ref Int64 a2, [In, Out] ref Int64 a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_bool_value(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_func_decl Z3_get_app_decl(Z3_context a0, Z3_app a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_app_num_args(Z3_context a0, Z3_app a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_get_app_arg(Z3_context a0, Z3_app a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_index_value(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_is_quantifier_forall(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_quantifier_weight(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_quantifier_num_patterns(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_pattern Z3_get_quantifier_pattern_ast(Z3_context a0, Z3_ast a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_quantifier_num_no_patterns(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_get_quantifier_no_pattern_ast(Z3_context a0, Z3_ast a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_get_quantifier_bound_name(Z3_context a0, Z3_ast a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_get_quantifier_bound_sort(Z3_context a0, Z3_ast a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_get_quantifier_body(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_quantifier_num_bound(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_get_decl_name(Z3_context a0, Z3_func_decl a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_decl_num_parameters(Z3_context a0, Z3_func_decl a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_decl_parameter_kind(Z3_context a0, Z3_func_decl a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_get_decl_int_parameter(Z3_context a0, Z3_func_decl a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static double Z3_get_decl_double_parameter(Z3_context a0, Z3_func_decl a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_get_decl_symbol_parameter(Z3_context a0, Z3_func_decl a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_get_decl_sort_parameter(Z3_context a0, Z3_func_decl a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_get_decl_ast_parameter(Z3_context a0, Z3_func_decl a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_func_decl Z3_get_decl_func_decl_parameter(Z3_context a0, Z3_func_decl a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_get_decl_rational_parameter(Z3_context a0, Z3_func_decl a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_get_sort_name(Z3_context a0, Z3_sort a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_get_sort(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_domain_size(Z3_context a0, Z3_func_decl a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_get_domain(Z3_context a0, Z3_func_decl a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_get_range(Z3_context a0, Z3_func_decl a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_sort_kind(Z3_context a0, Z3_sort a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_bv_sort_size(Z3_context a0, Z3_sort a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_get_array_sort_domain(Z3_context a0, Z3_sort a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_get_array_sort_range(Z3_context a0, Z3_sort a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_func_decl Z3_get_tuple_sort_mk_decl(Z3_context a0, Z3_sort a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_decl_kind(Z3_context a0, Z3_func_decl a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_tuple_sort_num_fields(Z3_context a0, Z3_sort a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_func_decl Z3_get_tuple_sort_field_decl(Z3_context a0, Z3_sort a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_datatype_sort_num_constructors(Z3_context a0, Z3_sort a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_func_decl Z3_get_datatype_sort_constructor(Z3_context a0, Z3_sort a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_func_decl Z3_get_datatype_sort_recognizer(Z3_context a0, Z3_sort a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_func_decl Z3_get_datatype_sort_constructor_accessor(Z3_context a0, Z3_sort a1, uint a2, uint a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_relation_arity(Z3_context a0, Z3_sort a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_get_relation_column(Z3_context a0, Z3_sort a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_get_finite_domain_sort_size(Z3_context a0, Z3_sort a1, [In, Out] ref UInt64 a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_mk_finite_domain_sort(Z3_context a0, IntPtr a1, UInt64 a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_pattern_num_terms(Z3_context a0, Z3_pattern a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_get_pattern(Z3_context a0, Z3_pattern a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_simplify(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_simplify_ex(Z3_context a0, Z3_ast a1, Z3_params a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_simplify_get_help(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_param_descrs Z3_simplify_get_param_descrs(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_update_term(Z3_context a0, Z3_ast a1, uint a2, [In] Z3_ast[] a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_substitute(Z3_context a0, Z3_ast a1, uint a2, [In] Z3_ast[] a3, [In] Z3_ast[] a4);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_substitute_vars(Z3_context a0, Z3_ast a1, uint a2, [In] Z3_ast[] a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_sort_to_ast(Z3_context a0, Z3_sort a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_func_decl_to_ast(Z3_context a0, Z3_func_decl a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_pattern_to_ast(Z3_context a0, Z3_pattern a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_app_to_ast(Z3_context a0, Z3_app a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_app Z3_to_app(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_func_decl Z3_to_func_decl(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_push(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_pop(Z3_context a0, uint a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_num_scopes(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_persist_ast(Z3_context a0, Z3_ast a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_assert_cnstr(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_check_and_get_model(Z3_context a0, [In, Out] ref Z3_model a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_check(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_check_assumptions(Z3_context a0, uint a1, [In] Z3_ast[] a2, [In, Out] ref Z3_model a3, [In, Out] ref Z3_ast a4, [In, Out] ref uint a5, [Out] Z3_ast[] a6);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_implied_equalities(Z3_context a0, uint a1, [In] Z3_ast[] a2, [Out] uint[] a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_del_model(Z3_context a0, Z3_model a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_soft_check_cancel(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_search_failure(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_literals Z3_get_relevant_labels(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_literals Z3_get_relevant_literals(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_literals Z3_get_guessed_literals(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_del_literals(Z3_context a0, Z3_literals a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_num_literals(Z3_context a0, Z3_literals a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_get_label_symbol(Z3_context a0, Z3_literals a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_get_literal(Z3_context a0, Z3_literals a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_disable_literal(Z3_context a0, Z3_literals a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_block_literals(Z3_context a0, Z3_literals a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_model_inc_ref(Z3_context a0, Z3_model a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_model_dec_ref(Z3_context a0, Z3_model a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_model_get_const_interp(Z3_context a0, Z3_model a1, Z3_func_decl a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_func_interp Z3_model_get_func_interp(Z3_context a0, Z3_model a1, Z3_func_decl a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_model_get_num_consts(Z3_context a0, Z3_model a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_func_decl Z3_model_get_const_decl(Z3_context a0, Z3_model a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_model_get_num_funcs(Z3_context a0, Z3_model a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_func_decl Z3_model_get_func_decl(Z3_context a0, Z3_model a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_model_eval(Z3_context a0, Z3_model a1, Z3_ast a2, int a3, [In, Out] ref Z3_ast a4);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_model_get_num_sorts(Z3_context a0, Z3_model a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_model_get_sort(Z3_context a0, Z3_model a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast_vector Z3_model_get_sort_universe(Z3_context a0, Z3_model a1, Z3_sort a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_is_as_array(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_func_decl Z3_get_as_array_func_decl(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_func_interp_inc_ref(Z3_context a0, Z3_func_interp a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_func_interp_dec_ref(Z3_context a0, Z3_func_interp a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_func_interp_get_num_entries(Z3_context a0, Z3_func_interp a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_func_entry Z3_func_interp_get_entry(Z3_context a0, Z3_func_interp a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_func_interp_get_else(Z3_context a0, Z3_func_interp a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_func_interp_get_arity(Z3_context a0, Z3_func_interp a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_func_entry_inc_ref(Z3_context a0, Z3_func_entry a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_func_entry_dec_ref(Z3_context a0, Z3_func_entry a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_func_entry_get_value(Z3_context a0, Z3_func_entry a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_func_entry_get_num_args(Z3_context a0, Z3_func_entry a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_func_entry_get_arg(Z3_context a0, Z3_func_entry a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_model_num_constants(Z3_context a0, Z3_model a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_func_decl Z3_get_model_constant(Z3_context a0, Z3_model a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_eval_func_decl(Z3_context a0, Z3_model a1, Z3_func_decl a2, [In, Out] ref Z3_ast a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_is_array_value(Z3_context a0, Z3_model a1, Z3_ast a2, [In, Out] ref uint a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_get_array_value(Z3_context a0, Z3_model a1, Z3_ast a2, uint a3, [Out] Z3_ast[] a4, [Out] Z3_ast[] a5, [In, Out] ref Z3_ast a6);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_model_num_funcs(Z3_context a0, Z3_model a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_func_decl Z3_get_model_func_decl(Z3_context a0, Z3_model a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_get_model_func_else(Z3_context a0, Z3_model a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_model_func_num_entries(Z3_context a0, Z3_model a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_model_func_entry_num_args(Z3_context a0, Z3_model a1, uint a2, uint a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_get_model_func_entry_arg(Z3_context a0, Z3_model a1, uint a2, uint a3, uint a4);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_get_model_func_entry_value(Z3_context a0, Z3_model a1, uint a2, uint a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_eval(Z3_context a0, Z3_model a1, Z3_ast a2, [In, Out] ref Z3_ast a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_eval_decl(Z3_context a0, Z3_model a1, Z3_func_decl a2, uint a3, [In] Z3_ast[] a4, [In, Out] ref Z3_ast a5);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_set_ast_print_mode(Z3_context a0, uint a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_ast_to_string(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_pattern_to_string(Z3_context a0, Z3_pattern a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_sort_to_string(Z3_context a0, Z3_sort a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_func_decl_to_string(Z3_context a0, Z3_func_decl a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_model_to_string(Z3_context a0, Z3_model a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_benchmark_to_smtlib_string(Z3_context a0, string a1, string a2, string a3, string a4, uint a5, [In] Z3_ast[] a6, Z3_ast a7);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_context_to_string(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_statistics_to_string(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_get_context_assignment(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_parse_smtlib_string(Z3_context a0, string a1, uint a2, [In] IntPtr[] a3, [In] Z3_sort[] a4, uint a5, [In] IntPtr[] a6, [In] Z3_func_decl[] a7);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_parse_smtlib_file(Z3_context a0, string a1, uint a2, [In] IntPtr[] a3, [In] Z3_sort[] a4, uint a5, [In] IntPtr[] a6, [In] Z3_func_decl[] a7);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_smtlib_num_formulas(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_get_smtlib_formula(Z3_context a0, uint a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_smtlib_num_assumptions(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_get_smtlib_assumption(Z3_context a0, uint a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_smtlib_num_decls(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_func_decl Z3_get_smtlib_decl(Z3_context a0, uint a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_smtlib_num_sorts(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_sort Z3_get_smtlib_sort(Z3_context a0, uint a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_get_smtlib_error(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_parse_z3_string(Z3_context a0, string a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_parse_z3_file(Z3_context a0, string a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_parse_smtlib2_string(Z3_context a0, string a1, uint a2, [In] IntPtr[] a3, [In] Z3_sort[] a4, uint a5, [In] IntPtr[] a6, [In] Z3_func_decl[] a7);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_parse_smtlib2_file(Z3_context a0, string a1, uint a2, [In] IntPtr[] a3, [In] Z3_sort[] a4, uint a5, [In] IntPtr[] a6, [In] Z3_func_decl[] a7);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_error_code(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_set_error(Z3_context a0, uint a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_get_error_msg(uint a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_get_version([In, Out] ref uint a0, [In, Out] ref uint a1, [In, Out] ref uint a2, [In, Out] ref uint a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_reset_memory();

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_is_app(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_is_numeral_ast(Z3_context a0, Z3_ast a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_arity(Z3_context a0, Z3_func_decl a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_func_decl Z3_mk_injective_function(Z3_context a0, IntPtr a1, uint a2, [In] Z3_sort[] a3, Z3_sort a4);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_fixedpoint Z3_mk_fixedpoint(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_fixedpoint_inc_ref(Z3_context a0, Z3_fixedpoint a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_fixedpoint_dec_ref(Z3_context a0, Z3_fixedpoint a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_fixedpoint_push(Z3_context a0, Z3_fixedpoint a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_fixedpoint_pop(Z3_context a0, Z3_fixedpoint a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_fixedpoint_register_relation(Z3_context a0, Z3_fixedpoint a1, Z3_func_decl a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_fixedpoint_assert(Z3_context a0, Z3_fixedpoint a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_fixedpoint_add_rule(Z3_context a0, Z3_fixedpoint a1, Z3_ast a2, IntPtr a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_fixedpoint_add_fact(Z3_context a0, Z3_fixedpoint a1, Z3_func_decl a2, uint a3, [In] uint[] a4);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_fixedpoint_query(Z3_context a0, Z3_fixedpoint a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_fixedpoint_query_relations(Z3_context a0, Z3_fixedpoint a1, uint a2, [In] Z3_func_decl[] a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_fixedpoint_get_answer(Z3_context a0, Z3_fixedpoint a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_fixedpoint_update_rule(Z3_context a0, Z3_fixedpoint a1, Z3_ast a2, IntPtr a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_fixedpoint_get_num_levels(Z3_context a0, Z3_fixedpoint a1, Z3_func_decl a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_fixedpoint_get_cover_delta(Z3_context a0, Z3_fixedpoint a1, int a2, Z3_func_decl a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_fixedpoint_add_cover(Z3_context a0, Z3_fixedpoint a1, int a2, Z3_func_decl a3, Z3_ast a4);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_stats Z3_fixedpoint_get_statistics(Z3_context a0, Z3_fixedpoint a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_fixedpoint_get_help(Z3_context a0, Z3_fixedpoint a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_param_descrs Z3_fixedpoint_get_param_descrs(Z3_context a0, Z3_fixedpoint a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_fixedpoint_set_params(Z3_context a0, Z3_fixedpoint a1, Z3_params a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_fixedpoint_to_string(Z3_context a0, Z3_fixedpoint a1, uint a2, [In] Z3_ast[] a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_fixedpoint_get_reason_unknown(Z3_context a0, Z3_fixedpoint a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_fixedpoint_set_predicate_representation(Z3_context a0, Z3_fixedpoint a1, Z3_func_decl a2, uint a3, [In] IntPtr[] a4);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast_vector Z3_fixedpoint_simplify_rules(Z3_context a0, Z3_fixedpoint a1, uint a2, [In] Z3_ast[] a3, uint a4, [In] Z3_func_decl[] a5);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_params Z3_mk_params(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_params_inc_ref(Z3_context a0, Z3_params a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_params_dec_ref(Z3_context a0, Z3_params a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_params_set_bool(Z3_context a0, Z3_params a1, IntPtr a2, int a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_params_set_uint(Z3_context a0, Z3_params a1, IntPtr a2, uint a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_params_set_double(Z3_context a0, Z3_params a1, IntPtr a2, double a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_params_set_symbol(Z3_context a0, Z3_params a1, IntPtr a2, IntPtr a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_params_to_string(Z3_context a0, Z3_params a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_params_validate(Z3_context a0, Z3_params a1, Z3_param_descrs a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_param_descrs_inc_ref(Z3_context a0, Z3_param_descrs a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_param_descrs_dec_ref(Z3_context a0, Z3_param_descrs a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_param_descrs_get_kind(Z3_context a0, Z3_param_descrs a1, IntPtr a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_param_descrs_size(Z3_context a0, Z3_param_descrs a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_param_descrs_get_name(Z3_context a0, Z3_param_descrs a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_interrupt(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_get_error_msg_ex(Z3_context a0, uint a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_translate(Z3_context a0, Z3_ast a1, Z3_context a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_goal Z3_mk_goal(Z3_context a0, int a1, int a2, int a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_goal_inc_ref(Z3_context a0, Z3_goal a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_goal_dec_ref(Z3_context a0, Z3_goal a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_goal_precision(Z3_context a0, Z3_goal a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_goal_assert(Z3_context a0, Z3_goal a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_goal_inconsistent(Z3_context a0, Z3_goal a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_goal_depth(Z3_context a0, Z3_goal a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_goal_reset(Z3_context a0, Z3_goal a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_goal_size(Z3_context a0, Z3_goal a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_goal_formula(Z3_context a0, Z3_goal a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_goal_num_exprs(Z3_context a0, Z3_goal a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_goal_is_decided_sat(Z3_context a0, Z3_goal a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_goal_is_decided_unsat(Z3_context a0, Z3_goal a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_goal Z3_goal_translate(Z3_context a0, Z3_goal a1, Z3_context a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_goal_to_string(Z3_context a0, Z3_goal a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_tactic Z3_mk_tactic(Z3_context a0, string a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_probe Z3_mk_probe(Z3_context a0, string a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_tactic_inc_ref(Z3_context a0, Z3_tactic a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_tactic_dec_ref(Z3_context a0, Z3_tactic a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_probe_inc_ref(Z3_context a0, Z3_probe a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_probe_dec_ref(Z3_context a0, Z3_probe a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_tactic Z3_tactic_and_then(Z3_context a0, Z3_tactic a1, Z3_tactic a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_tactic Z3_tactic_or_else(Z3_context a0, Z3_tactic a1, Z3_tactic a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_tactic Z3_tactic_par_or(Z3_context a0, uint a1, [In] Z3_tactic[] a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_tactic Z3_tactic_par_and_then(Z3_context a0, Z3_tactic a1, Z3_tactic a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_tactic Z3_tactic_try_for(Z3_context a0, Z3_tactic a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_tactic Z3_tactic_when(Z3_context a0, Z3_probe a1, Z3_tactic a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_tactic Z3_tactic_cond(Z3_context a0, Z3_probe a1, Z3_tactic a2, Z3_tactic a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_tactic Z3_tactic_repeat(Z3_context a0, Z3_tactic a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_tactic Z3_tactic_skip(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_tactic Z3_tactic_fail(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_tactic Z3_tactic_fail_if(Z3_context a0, Z3_probe a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_tactic Z3_tactic_fail_if_not_decided(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_tactic Z3_tactic_using_params(Z3_context a0, Z3_tactic a1, Z3_params a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_probe Z3_probe_const(Z3_context a0, double a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_probe Z3_probe_lt(Z3_context a0, Z3_probe a1, Z3_probe a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_probe Z3_probe_le(Z3_context a0, Z3_probe a1, Z3_probe a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_probe Z3_probe_gt(Z3_context a0, Z3_probe a1, Z3_probe a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_probe Z3_probe_ge(Z3_context a0, Z3_probe a1, Z3_probe a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_probe Z3_probe_eq(Z3_context a0, Z3_probe a1, Z3_probe a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_probe Z3_probe_and(Z3_context a0, Z3_probe a1, Z3_probe a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_probe Z3_probe_or(Z3_context a0, Z3_probe a1, Z3_probe a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_probe Z3_probe_not(Z3_context a0, Z3_probe a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_num_tactics(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_get_tactic_name(Z3_context a0, uint a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_get_num_probes(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_get_probe_name(Z3_context a0, uint a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_tactic_get_help(Z3_context a0, Z3_tactic a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_param_descrs Z3_tactic_get_param_descrs(Z3_context a0, Z3_tactic a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_tactic_get_descr(Z3_context a0, string a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_probe_get_descr(Z3_context a0, string a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static double Z3_probe_apply(Z3_context a0, Z3_probe a1, Z3_goal a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_apply_result Z3_tactic_apply(Z3_context a0, Z3_tactic a1, Z3_goal a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_apply_result Z3_tactic_apply_ex(Z3_context a0, Z3_tactic a1, Z3_goal a2, Z3_params a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_apply_result_inc_ref(Z3_context a0, Z3_apply_result a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_apply_result_dec_ref(Z3_context a0, Z3_apply_result a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_apply_result_to_string(Z3_context a0, Z3_apply_result a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_apply_result_get_num_subgoals(Z3_context a0, Z3_apply_result a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_goal Z3_apply_result_get_subgoal(Z3_context a0, Z3_apply_result a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_model Z3_apply_result_convert_model(Z3_context a0, Z3_apply_result a1, uint a2, Z3_model a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_solver Z3_mk_solver(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_solver Z3_mk_simple_solver(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_solver Z3_mk_solver_for_logic(Z3_context a0, IntPtr a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_solver Z3_mk_solver_from_tactic(Z3_context a0, Z3_tactic a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_solver_get_help(Z3_context a0, Z3_solver a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_param_descrs Z3_solver_get_param_descrs(Z3_context a0, Z3_solver a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_solver_set_params(Z3_context a0, Z3_solver a1, Z3_params a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_solver_inc_ref(Z3_context a0, Z3_solver a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_solver_dec_ref(Z3_context a0, Z3_solver a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_solver_push(Z3_context a0, Z3_solver a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_solver_pop(Z3_context a0, Z3_solver a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_solver_reset(Z3_context a0, Z3_solver a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_solver_get_num_scopes(Z3_context a0, Z3_solver a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_solver_assert(Z3_context a0, Z3_solver a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast_vector Z3_solver_get_assertions(Z3_context a0, Z3_solver a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_solver_check(Z3_context a0, Z3_solver a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_solver_check_assumptions(Z3_context a0, Z3_solver a1, uint a2, [In] Z3_ast[] a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_model Z3_solver_get_model(Z3_context a0, Z3_solver a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_solver_get_proof(Z3_context a0, Z3_solver a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast_vector Z3_solver_get_unsat_core(Z3_context a0, Z3_solver a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_solver_get_reason_unknown(Z3_context a0, Z3_solver a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_stats Z3_solver_get_statistics(Z3_context a0, Z3_solver a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_solver_to_string(Z3_context a0, Z3_solver a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_stats_to_string(Z3_context a0, Z3_stats a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_stats_inc_ref(Z3_context a0, Z3_stats a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_stats_dec_ref(Z3_context a0, Z3_stats a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_stats_size(Z3_context a0, Z3_stats a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_stats_get_key(Z3_context a0, Z3_stats a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_stats_is_uint(Z3_context a0, Z3_stats a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_stats_is_double(Z3_context a0, Z3_stats a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_stats_get_uint_value(Z3_context a0, Z3_stats a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static double Z3_stats_get_double_value(Z3_context a0, Z3_stats a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast_vector Z3_mk_ast_vector(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_ast_vector_inc_ref(Z3_context a0, Z3_ast_vector a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_ast_vector_dec_ref(Z3_context a0, Z3_ast_vector a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_ast_vector_size(Z3_context a0, Z3_ast_vector a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_ast_vector_get(Z3_context a0, Z3_ast_vector a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_ast_vector_set(Z3_context a0, Z3_ast_vector a1, uint a2, Z3_ast a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_ast_vector_resize(Z3_context a0, Z3_ast_vector a1, uint a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_ast_vector_push(Z3_context a0, Z3_ast_vector a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast_vector Z3_ast_vector_translate(Z3_context a0, Z3_ast_vector a1, Z3_context a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_ast_vector_to_string(Z3_context a0, Z3_ast_vector a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast_map Z3_mk_ast_map(Z3_context a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_ast_map_inc_ref(Z3_context a0, Z3_ast_map a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_ast_map_dec_ref(Z3_context a0, Z3_ast_map a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_ast_map_contains(Z3_context a0, Z3_ast_map a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast Z3_ast_map_find(Z3_context a0, Z3_ast_map a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_ast_map_insert(Z3_context a0, Z3_ast_map a1, Z3_ast a2, Z3_ast a3);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_ast_map_erase(Z3_context a0, Z3_ast_map a1, Z3_ast a2);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static uint Z3_ast_map_size(Z3_context a0, Z3_ast_map a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_ast_map_reset(Z3_context a0, Z3_ast_map a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static Z3_ast_vector Z3_ast_map_keys(Z3_context a0, Z3_ast_map a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static IntPtr Z3_ast_map_to_string(Z3_context a0, Z3_ast_map a1);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static int Z3_open_log(string a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_append_log(string a0);

            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]
            public extern static void Z3_close_log();

        }

        public static void Z3_set_error_handler(Z3_context a0, Z3_error_handler a1) {
            LIB.Z3_set_error_handler(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static Z3_config Z3_mk_config() {
            Z3_config r = LIB.Z3_mk_config();
            return r;
        }

        public static void Z3_del_config(Z3_config a0) {
            LIB.Z3_del_config(a0);
        }

        public static void Z3_set_param_value(Z3_config a0, string a1, string a2) {
            LIB.Z3_set_param_value(a0, a1, a2);
        }

        public static Z3_context Z3_mk_context(Z3_config a0) {
            Z3_context r = LIB.Z3_mk_context(a0);
            return r;
        }

        public static Z3_context Z3_mk_context_rc(Z3_config a0) {
            Z3_context r = LIB.Z3_mk_context_rc(a0);
            return r;
        }

        public static void Z3_set_logic(Z3_context a0, string a1) {
            LIB.Z3_set_logic(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_del_context(Z3_context a0) {
            LIB.Z3_del_context(a0);
        }

        public static void Z3_inc_ref(Z3_context a0, Z3_ast a1) {
            LIB.Z3_inc_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_dec_ref(Z3_context a0, Z3_ast a1) {
            LIB.Z3_dec_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_toggle_warning_messages(int a0) {
            LIB.Z3_toggle_warning_messages(a0);
        }

        public static void Z3_update_param_value(Z3_context a0, string a1, string a2) {
            LIB.Z3_update_param_value(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static int Z3_get_param_value(Z3_context a0, string a1, out IntPtr a2) {
            int r = LIB.Z3_get_param_value(a0, a1, out a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static IntPtr Z3_mk_int_symbol(Z3_context a0, int a1) {
            IntPtr r = LIB.Z3_mk_int_symbol(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static IntPtr Z3_mk_string_symbol(Z3_context a0, string a1) {
            IntPtr r = LIB.Z3_mk_string_symbol(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_is_eq_sort(Z3_context a0, Z3_sort a1, Z3_sort a2) {
            int r = LIB.Z3_is_eq_sort(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_sort Z3_mk_uninterpreted_sort(Z3_context a0, IntPtr a1) {
            Z3_sort r = LIB.Z3_mk_uninterpreted_sort(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_sort Z3_mk_bool_sort(Z3_context a0) {
            Z3_sort r = LIB.Z3_mk_bool_sort(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_sort Z3_mk_int_sort(Z3_context a0) {
            Z3_sort r = LIB.Z3_mk_int_sort(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_sort Z3_mk_real_sort(Z3_context a0) {
            Z3_sort r = LIB.Z3_mk_real_sort(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_sort Z3_mk_bv_sort(Z3_context a0, uint a1) {
            Z3_sort r = LIB.Z3_mk_bv_sort(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_sort Z3_mk_array_sort(Z3_context a0, Z3_sort a1, Z3_sort a2) {
            Z3_sort r = LIB.Z3_mk_array_sort(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_sort Z3_mk_tuple_sort(Z3_context a0, IntPtr a1, uint a2, [In] IntPtr[] a3, [In] Z3_sort[] a4, [In, Out] ref Z3_func_decl a5, [Out] Z3_func_decl[] a6) {
            Z3_sort r = LIB.Z3_mk_tuple_sort(a0, a1, a2, a3, a4, ref a5, a6);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_sort Z3_mk_enumeration_sort(Z3_context a0, IntPtr a1, uint a2, [In] IntPtr[] a3, [Out] Z3_func_decl[] a4, [Out] Z3_func_decl[] a5) {
            Z3_sort r = LIB.Z3_mk_enumeration_sort(a0, a1, a2, a3, a4, a5);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_sort Z3_mk_list_sort(Z3_context a0, IntPtr a1, Z3_sort a2, [In, Out] ref Z3_func_decl a3, [In, Out] ref Z3_func_decl a4, [In, Out] ref Z3_func_decl a5, [In, Out] ref Z3_func_decl a6, [In, Out] ref Z3_func_decl a7, [In, Out] ref Z3_func_decl a8) {
            Z3_sort r = LIB.Z3_mk_list_sort(a0, a1, a2, ref a3, ref a4, ref a5, ref a6, ref a7, ref a8);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_constructor Z3_mk_constructor(Z3_context a0, IntPtr a1, IntPtr a2, uint a3, [In] IntPtr[] a4, [In] Z3_sort[] a5, [In] uint[] a6) {
            Z3_constructor r = LIB.Z3_mk_constructor(a0, a1, a2, a3, a4, a5, a6);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_query_constructor(Z3_context a0, Z3_constructor a1, uint a2, [In, Out] ref Z3_func_decl a3, [In, Out] ref Z3_func_decl a4, [Out] Z3_func_decl[] a5) {
            LIB.Z3_query_constructor(a0, a1, a2, ref a3, ref a4, a5);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_del_constructor(Z3_context a0, Z3_constructor a1) {
            LIB.Z3_del_constructor(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static Z3_sort Z3_mk_datatype(Z3_context a0, IntPtr a1, uint a2, [In, Out] Z3_constructor[] a3) {
            Z3_sort r = LIB.Z3_mk_datatype(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_constructor_list Z3_mk_constructor_list(Z3_context a0, uint a1, [In] Z3_constructor[] a2) {
            Z3_constructor_list r = LIB.Z3_mk_constructor_list(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_del_constructor_list(Z3_context a0, Z3_constructor_list a1) {
            LIB.Z3_del_constructor_list(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_mk_datatypes(Z3_context a0, uint a1, [In] IntPtr[] a2, [Out] Z3_sort[] a3, [In, Out] Z3_constructor_list[] a4) {
            LIB.Z3_mk_datatypes(a0, a1, a2, a3, a4);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static int Z3_is_eq_ast(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            int r = LIB.Z3_is_eq_ast(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_is_eq_func_decl(Z3_context a0, Z3_func_decl a1, Z3_func_decl a2) {
            int r = LIB.Z3_is_eq_func_decl(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_func_decl Z3_mk_func_decl(Z3_context a0, IntPtr a1, uint a2, [In] Z3_sort[] a3, Z3_sort a4) {
            Z3_func_decl r = LIB.Z3_mk_func_decl(a0, a1, a2, a3, a4);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_app(Z3_context a0, Z3_func_decl a1, uint a2, [In] Z3_ast[] a3) {
            Z3_ast r = LIB.Z3_mk_app(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_const(Z3_context a0, IntPtr a1, Z3_sort a2) {
            Z3_ast r = LIB.Z3_mk_const(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_label(Z3_context a0, IntPtr a1, int a2, Z3_ast a3) {
            Z3_ast r = LIB.Z3_mk_label(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_func_decl Z3_mk_fresh_func_decl(Z3_context a0, string a1, uint a2, [In] Z3_sort[] a3, Z3_sort a4) {
            Z3_func_decl r = LIB.Z3_mk_fresh_func_decl(a0, a1, a2, a3, a4);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_fresh_const(Z3_context a0, string a1, Z3_sort a2) {
            Z3_ast r = LIB.Z3_mk_fresh_const(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_true(Z3_context a0) {
            Z3_ast r = LIB.Z3_mk_true(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_false(Z3_context a0) {
            Z3_ast r = LIB.Z3_mk_false(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_eq(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_eq(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_distinct(Z3_context a0, uint a1, [In] Z3_ast[] a2) {
            Z3_ast r = LIB.Z3_mk_distinct(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_not(Z3_context a0, Z3_ast a1) {
            Z3_ast r = LIB.Z3_mk_not(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_ite(Z3_context a0, Z3_ast a1, Z3_ast a2, Z3_ast a3) {
            Z3_ast r = LIB.Z3_mk_ite(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_iff(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_iff(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_implies(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_implies(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_xor(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_xor(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_and(Z3_context a0, uint a1, [In] Z3_ast[] a2) {
            Z3_ast r = LIB.Z3_mk_and(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_or(Z3_context a0, uint a1, [In] Z3_ast[] a2) {
            Z3_ast r = LIB.Z3_mk_or(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_add(Z3_context a0, uint a1, [In] Z3_ast[] a2) {
            Z3_ast r = LIB.Z3_mk_add(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_mul(Z3_context a0, uint a1, [In] Z3_ast[] a2) {
            Z3_ast r = LIB.Z3_mk_mul(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_sub(Z3_context a0, uint a1, [In] Z3_ast[] a2) {
            Z3_ast r = LIB.Z3_mk_sub(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_unary_minus(Z3_context a0, Z3_ast a1) {
            Z3_ast r = LIB.Z3_mk_unary_minus(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_div(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_div(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_mod(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_mod(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_rem(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_rem(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_power(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_power(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_is_algebraic_number(Z3_context a0, Z3_ast a1) {
            int r = LIB.Z3_is_algebraic_number(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_get_algebraic_number_lower(Z3_context a0, Z3_ast a1, uint a2) {
            Z3_ast r = LIB.Z3_get_algebraic_number_lower(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_get_algebraic_number_upper(Z3_context a0, Z3_ast a1, uint a2) {
            Z3_ast r = LIB.Z3_get_algebraic_number_upper(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_lt(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_lt(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_le(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_le(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_gt(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_gt(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_ge(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_ge(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_int2real(Z3_context a0, Z3_ast a1) {
            Z3_ast r = LIB.Z3_mk_int2real(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_real2int(Z3_context a0, Z3_ast a1) {
            Z3_ast r = LIB.Z3_mk_real2int(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_is_int(Z3_context a0, Z3_ast a1) {
            Z3_ast r = LIB.Z3_mk_is_int(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvnot(Z3_context a0, Z3_ast a1) {
            Z3_ast r = LIB.Z3_mk_bvnot(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvredand(Z3_context a0, Z3_ast a1) {
            Z3_ast r = LIB.Z3_mk_bvredand(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvredor(Z3_context a0, Z3_ast a1) {
            Z3_ast r = LIB.Z3_mk_bvredor(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvand(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvand(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvor(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvor(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvxor(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvxor(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvnand(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvnand(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvnor(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvnor(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvxnor(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvxnor(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvneg(Z3_context a0, Z3_ast a1) {
            Z3_ast r = LIB.Z3_mk_bvneg(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvadd(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvadd(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvsub(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvsub(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvmul(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvmul(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvudiv(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvudiv(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvsdiv(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvsdiv(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvurem(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvurem(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvsrem(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvsrem(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvsmod(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvsmod(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvult(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvult(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvslt(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvslt(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvule(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvule(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvsle(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvsle(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvuge(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvuge(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvsge(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvsge(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvugt(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvugt(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvsgt(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvsgt(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_concat(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_concat(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_extract(Z3_context a0, uint a1, uint a2, Z3_ast a3) {
            Z3_ast r = LIB.Z3_mk_extract(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_sign_ext(Z3_context a0, uint a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_sign_ext(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_zero_ext(Z3_context a0, uint a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_zero_ext(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_repeat(Z3_context a0, uint a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_repeat(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvshl(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvshl(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvlshr(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvlshr(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvashr(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvashr(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_rotate_left(Z3_context a0, uint a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_rotate_left(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_rotate_right(Z3_context a0, uint a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_rotate_right(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_ext_rotate_left(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_ext_rotate_left(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_ext_rotate_right(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_ext_rotate_right(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_int2bv(Z3_context a0, uint a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_int2bv(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bv2int(Z3_context a0, Z3_ast a1, int a2) {
            Z3_ast r = LIB.Z3_mk_bv2int(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvadd_no_overflow(Z3_context a0, Z3_ast a1, Z3_ast a2, int a3) {
            Z3_ast r = LIB.Z3_mk_bvadd_no_overflow(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvadd_no_underflow(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvadd_no_underflow(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvsub_no_overflow(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvsub_no_overflow(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvsub_no_underflow(Z3_context a0, Z3_ast a1, Z3_ast a2, int a3) {
            Z3_ast r = LIB.Z3_mk_bvsub_no_underflow(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvsdiv_no_overflow(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvsdiv_no_overflow(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvneg_no_overflow(Z3_context a0, Z3_ast a1) {
            Z3_ast r = LIB.Z3_mk_bvneg_no_overflow(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvmul_no_overflow(Z3_context a0, Z3_ast a1, Z3_ast a2, int a3) {
            Z3_ast r = LIB.Z3_mk_bvmul_no_overflow(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bvmul_no_underflow(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_bvmul_no_underflow(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_select(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_select(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_store(Z3_context a0, Z3_ast a1, Z3_ast a2, Z3_ast a3) {
            Z3_ast r = LIB.Z3_mk_store(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_const_array(Z3_context a0, Z3_sort a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_const_array(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_map(Z3_context a0, Z3_func_decl a1, uint a2, [In] Z3_ast[] a3) {
            Z3_ast r = LIB.Z3_mk_map(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_array_default(Z3_context a0, Z3_ast a1) {
            Z3_ast r = LIB.Z3_mk_array_default(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_sort Z3_mk_set_sort(Z3_context a0, Z3_sort a1) {
            Z3_sort r = LIB.Z3_mk_set_sort(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_empty_set(Z3_context a0, Z3_sort a1) {
            Z3_ast r = LIB.Z3_mk_empty_set(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_full_set(Z3_context a0, Z3_sort a1) {
            Z3_ast r = LIB.Z3_mk_full_set(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_set_add(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_set_add(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_set_del(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_set_del(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_set_union(Z3_context a0, uint a1, [In] Z3_ast[] a2) {
            Z3_ast r = LIB.Z3_mk_set_union(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_set_intersect(Z3_context a0, uint a1, [In] Z3_ast[] a2) {
            Z3_ast r = LIB.Z3_mk_set_intersect(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_set_difference(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_set_difference(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_set_complement(Z3_context a0, Z3_ast a1) {
            Z3_ast r = LIB.Z3_mk_set_complement(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_set_member(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_set_member(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_set_subset(Z3_context a0, Z3_ast a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_mk_set_subset(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_numeral(Z3_context a0, string a1, Z3_sort a2) {
            Z3_ast r = LIB.Z3_mk_numeral(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_real(Z3_context a0, int a1, int a2) {
            Z3_ast r = LIB.Z3_mk_real(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_int(Z3_context a0, int a1, Z3_sort a2) {
            Z3_ast r = LIB.Z3_mk_int(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_unsigned_int(Z3_context a0, uint a1, Z3_sort a2) {
            Z3_ast r = LIB.Z3_mk_unsigned_int(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_int64(Z3_context a0, Int64 a1, Z3_sort a2) {
            Z3_ast r = LIB.Z3_mk_int64(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_unsigned_int64(Z3_context a0, UInt64 a1, Z3_sort a2) {
            Z3_ast r = LIB.Z3_mk_unsigned_int64(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_pattern Z3_mk_pattern(Z3_context a0, uint a1, [In] Z3_ast[] a2) {
            Z3_pattern r = LIB.Z3_mk_pattern(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_bound(Z3_context a0, uint a1, Z3_sort a2) {
            Z3_ast r = LIB.Z3_mk_bound(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_forall(Z3_context a0, uint a1, uint a2, [In] Z3_pattern[] a3, uint a4, [In] Z3_sort[] a5, [In] IntPtr[] a6, Z3_ast a7) {
            Z3_ast r = LIB.Z3_mk_forall(a0, a1, a2, a3, a4, a5, a6, a7);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_exists(Z3_context a0, uint a1, uint a2, [In] Z3_pattern[] a3, uint a4, [In] Z3_sort[] a5, [In] IntPtr[] a6, Z3_ast a7) {
            Z3_ast r = LIB.Z3_mk_exists(a0, a1, a2, a3, a4, a5, a6, a7);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_quantifier(Z3_context a0, int a1, uint a2, uint a3, [In] Z3_pattern[] a4, uint a5, [In] Z3_sort[] a6, [In] IntPtr[] a7, Z3_ast a8) {
            Z3_ast r = LIB.Z3_mk_quantifier(a0, a1, a2, a3, a4, a5, a6, a7, a8);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_quantifier_ex(Z3_context a0, int a1, uint a2, IntPtr a3, IntPtr a4, uint a5, [In] Z3_pattern[] a6, uint a7, [In] Z3_ast[] a8, uint a9, [In] Z3_sort[] a10, [In] IntPtr[] a11, Z3_ast a12) {
            Z3_ast r = LIB.Z3_mk_quantifier_ex(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_forall_const(Z3_context a0, uint a1, uint a2, [In] Z3_app[] a3, uint a4, [In] Z3_pattern[] a5, Z3_ast a6) {
            Z3_ast r = LIB.Z3_mk_forall_const(a0, a1, a2, a3, a4, a5, a6);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_exists_const(Z3_context a0, uint a1, uint a2, [In] Z3_app[] a3, uint a4, [In] Z3_pattern[] a5, Z3_ast a6) {
            Z3_ast r = LIB.Z3_mk_exists_const(a0, a1, a2, a3, a4, a5, a6);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_quantifier_const(Z3_context a0, int a1, uint a2, uint a3, [In] Z3_app[] a4, uint a5, [In] Z3_pattern[] a6, Z3_ast a7) {
            Z3_ast r = LIB.Z3_mk_quantifier_const(a0, a1, a2, a3, a4, a5, a6, a7);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_mk_quantifier_const_ex(Z3_context a0, int a1, uint a2, IntPtr a3, IntPtr a4, uint a5, [In] Z3_app[] a6, uint a7, [In] Z3_pattern[] a8, uint a9, [In] Z3_ast[] a10, Z3_ast a11) {
            Z3_ast r = LIB.Z3_mk_quantifier_const_ex(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_ast_id(Z3_context a0, Z3_ast a1) {
            uint r = LIB.Z3_get_ast_id(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_func_decl_id(Z3_context a0, Z3_func_decl a1) {
            uint r = LIB.Z3_get_func_decl_id(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_sort_id(Z3_context a0, Z3_sort a1) {
            uint r = LIB.Z3_get_sort_id(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_is_well_sorted(Z3_context a0, Z3_ast a1) {
            int r = LIB.Z3_is_well_sorted(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_symbol_kind(Z3_context a0, IntPtr a1) {
            uint r = LIB.Z3_get_symbol_kind(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_get_symbol_int(Z3_context a0, IntPtr a1) {
            int r = LIB.Z3_get_symbol_int(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static string Z3_get_symbol_string(Z3_context a0, IntPtr a1) {
            IntPtr r = LIB.Z3_get_symbol_string(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static uint Z3_get_ast_kind(Z3_context a0, Z3_ast a1) {
            uint r = LIB.Z3_get_ast_kind(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_ast_hash(Z3_context a0, Z3_ast a1) {
            uint r = LIB.Z3_get_ast_hash(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static string Z3_get_numeral_string(Z3_context a0, Z3_ast a1) {
            IntPtr r = LIB.Z3_get_numeral_string(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static string Z3_get_numeral_decimal_string(Z3_context a0, Z3_ast a1, uint a2) {
            IntPtr r = LIB.Z3_get_numeral_decimal_string(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static Z3_ast Z3_get_numerator(Z3_context a0, Z3_ast a1) {
            Z3_ast r = LIB.Z3_get_numerator(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_get_denominator(Z3_context a0, Z3_ast a1) {
            Z3_ast r = LIB.Z3_get_denominator(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_get_numeral_small(Z3_context a0, Z3_ast a1, [In, Out] ref Int64 a2, [In, Out] ref Int64 a3) {
            int r = LIB.Z3_get_numeral_small(a0, a1, ref a2, ref a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_get_numeral_int(Z3_context a0, Z3_ast a1, [In, Out] ref int a2) {
            int r = LIB.Z3_get_numeral_int(a0, a1, ref a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_get_numeral_uint(Z3_context a0, Z3_ast a1, [In, Out] ref uint a2) {
            int r = LIB.Z3_get_numeral_uint(a0, a1, ref a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_get_numeral_uint64(Z3_context a0, Z3_ast a1, [In, Out] ref UInt64 a2) {
            int r = LIB.Z3_get_numeral_uint64(a0, a1, ref a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_get_numeral_int64(Z3_context a0, Z3_ast a1, [In, Out] ref Int64 a2) {
            int r = LIB.Z3_get_numeral_int64(a0, a1, ref a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_get_numeral_rational_int64(Z3_context a0, Z3_ast a1, [In, Out] ref Int64 a2, [In, Out] ref Int64 a3) {
            int r = LIB.Z3_get_numeral_rational_int64(a0, a1, ref a2, ref a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_bool_value(Z3_context a0, Z3_ast a1) {
            uint r = LIB.Z3_get_bool_value(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_func_decl Z3_get_app_decl(Z3_context a0, Z3_app a1) {
            Z3_func_decl r = LIB.Z3_get_app_decl(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_app_num_args(Z3_context a0, Z3_app a1) {
            uint r = LIB.Z3_get_app_num_args(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_get_app_arg(Z3_context a0, Z3_app a1, uint a2) {
            Z3_ast r = LIB.Z3_get_app_arg(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_index_value(Z3_context a0, Z3_ast a1) {
            uint r = LIB.Z3_get_index_value(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_is_quantifier_forall(Z3_context a0, Z3_ast a1) {
            int r = LIB.Z3_is_quantifier_forall(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_quantifier_weight(Z3_context a0, Z3_ast a1) {
            uint r = LIB.Z3_get_quantifier_weight(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_quantifier_num_patterns(Z3_context a0, Z3_ast a1) {
            uint r = LIB.Z3_get_quantifier_num_patterns(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_pattern Z3_get_quantifier_pattern_ast(Z3_context a0, Z3_ast a1, uint a2) {
            Z3_pattern r = LIB.Z3_get_quantifier_pattern_ast(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_quantifier_num_no_patterns(Z3_context a0, Z3_ast a1) {
            uint r = LIB.Z3_get_quantifier_num_no_patterns(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_get_quantifier_no_pattern_ast(Z3_context a0, Z3_ast a1, uint a2) {
            Z3_ast r = LIB.Z3_get_quantifier_no_pattern_ast(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static IntPtr Z3_get_quantifier_bound_name(Z3_context a0, Z3_ast a1, uint a2) {
            IntPtr r = LIB.Z3_get_quantifier_bound_name(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_sort Z3_get_quantifier_bound_sort(Z3_context a0, Z3_ast a1, uint a2) {
            Z3_sort r = LIB.Z3_get_quantifier_bound_sort(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_get_quantifier_body(Z3_context a0, Z3_ast a1) {
            Z3_ast r = LIB.Z3_get_quantifier_body(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_quantifier_num_bound(Z3_context a0, Z3_ast a1) {
            uint r = LIB.Z3_get_quantifier_num_bound(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static IntPtr Z3_get_decl_name(Z3_context a0, Z3_func_decl a1) {
            IntPtr r = LIB.Z3_get_decl_name(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_decl_num_parameters(Z3_context a0, Z3_func_decl a1) {
            uint r = LIB.Z3_get_decl_num_parameters(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_decl_parameter_kind(Z3_context a0, Z3_func_decl a1, uint a2) {
            uint r = LIB.Z3_get_decl_parameter_kind(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_get_decl_int_parameter(Z3_context a0, Z3_func_decl a1, uint a2) {
            int r = LIB.Z3_get_decl_int_parameter(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static double Z3_get_decl_double_parameter(Z3_context a0, Z3_func_decl a1, uint a2) {
            double r = LIB.Z3_get_decl_double_parameter(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static IntPtr Z3_get_decl_symbol_parameter(Z3_context a0, Z3_func_decl a1, uint a2) {
            IntPtr r = LIB.Z3_get_decl_symbol_parameter(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_sort Z3_get_decl_sort_parameter(Z3_context a0, Z3_func_decl a1, uint a2) {
            Z3_sort r = LIB.Z3_get_decl_sort_parameter(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_get_decl_ast_parameter(Z3_context a0, Z3_func_decl a1, uint a2) {
            Z3_ast r = LIB.Z3_get_decl_ast_parameter(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_func_decl Z3_get_decl_func_decl_parameter(Z3_context a0, Z3_func_decl a1, uint a2) {
            Z3_func_decl r = LIB.Z3_get_decl_func_decl_parameter(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static string Z3_get_decl_rational_parameter(Z3_context a0, Z3_func_decl a1, uint a2) {
            IntPtr r = LIB.Z3_get_decl_rational_parameter(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static IntPtr Z3_get_sort_name(Z3_context a0, Z3_sort a1) {
            IntPtr r = LIB.Z3_get_sort_name(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_sort Z3_get_sort(Z3_context a0, Z3_ast a1) {
            Z3_sort r = LIB.Z3_get_sort(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_domain_size(Z3_context a0, Z3_func_decl a1) {
            uint r = LIB.Z3_get_domain_size(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_sort Z3_get_domain(Z3_context a0, Z3_func_decl a1, uint a2) {
            Z3_sort r = LIB.Z3_get_domain(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_sort Z3_get_range(Z3_context a0, Z3_func_decl a1) {
            Z3_sort r = LIB.Z3_get_range(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_sort_kind(Z3_context a0, Z3_sort a1) {
            uint r = LIB.Z3_get_sort_kind(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_bv_sort_size(Z3_context a0, Z3_sort a1) {
            uint r = LIB.Z3_get_bv_sort_size(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_sort Z3_get_array_sort_domain(Z3_context a0, Z3_sort a1) {
            Z3_sort r = LIB.Z3_get_array_sort_domain(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_sort Z3_get_array_sort_range(Z3_context a0, Z3_sort a1) {
            Z3_sort r = LIB.Z3_get_array_sort_range(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_func_decl Z3_get_tuple_sort_mk_decl(Z3_context a0, Z3_sort a1) {
            Z3_func_decl r = LIB.Z3_get_tuple_sort_mk_decl(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_decl_kind(Z3_context a0, Z3_func_decl a1) {
            uint r = LIB.Z3_get_decl_kind(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_tuple_sort_num_fields(Z3_context a0, Z3_sort a1) {
            uint r = LIB.Z3_get_tuple_sort_num_fields(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_func_decl Z3_get_tuple_sort_field_decl(Z3_context a0, Z3_sort a1, uint a2) {
            Z3_func_decl r = LIB.Z3_get_tuple_sort_field_decl(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_datatype_sort_num_constructors(Z3_context a0, Z3_sort a1) {
            uint r = LIB.Z3_get_datatype_sort_num_constructors(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_func_decl Z3_get_datatype_sort_constructor(Z3_context a0, Z3_sort a1, uint a2) {
            Z3_func_decl r = LIB.Z3_get_datatype_sort_constructor(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_func_decl Z3_get_datatype_sort_recognizer(Z3_context a0, Z3_sort a1, uint a2) {
            Z3_func_decl r = LIB.Z3_get_datatype_sort_recognizer(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_func_decl Z3_get_datatype_sort_constructor_accessor(Z3_context a0, Z3_sort a1, uint a2, uint a3) {
            Z3_func_decl r = LIB.Z3_get_datatype_sort_constructor_accessor(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_relation_arity(Z3_context a0, Z3_sort a1) {
            uint r = LIB.Z3_get_relation_arity(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_sort Z3_get_relation_column(Z3_context a0, Z3_sort a1, uint a2) {
            Z3_sort r = LIB.Z3_get_relation_column(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_get_finite_domain_sort_size(Z3_context a0, Z3_sort a1, [In, Out] ref UInt64 a2) {
            int r = LIB.Z3_get_finite_domain_sort_size(a0, a1, ref a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_sort Z3_mk_finite_domain_sort(Z3_context a0, IntPtr a1, UInt64 a2) {
            Z3_sort r = LIB.Z3_mk_finite_domain_sort(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_pattern_num_terms(Z3_context a0, Z3_pattern a1) {
            uint r = LIB.Z3_get_pattern_num_terms(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_get_pattern(Z3_context a0, Z3_pattern a1, uint a2) {
            Z3_ast r = LIB.Z3_get_pattern(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_simplify(Z3_context a0, Z3_ast a1) {
            Z3_ast r = LIB.Z3_simplify(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_simplify_ex(Z3_context a0, Z3_ast a1, Z3_params a2) {
            Z3_ast r = LIB.Z3_simplify_ex(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static string Z3_simplify_get_help(Z3_context a0) {
            IntPtr r = LIB.Z3_simplify_get_help(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static Z3_param_descrs Z3_simplify_get_param_descrs(Z3_context a0) {
            Z3_param_descrs r = LIB.Z3_simplify_get_param_descrs(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_update_term(Z3_context a0, Z3_ast a1, uint a2, [In] Z3_ast[] a3) {
            Z3_ast r = LIB.Z3_update_term(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_substitute(Z3_context a0, Z3_ast a1, uint a2, [In] Z3_ast[] a3, [In] Z3_ast[] a4) {
            Z3_ast r = LIB.Z3_substitute(a0, a1, a2, a3, a4);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_substitute_vars(Z3_context a0, Z3_ast a1, uint a2, [In] Z3_ast[] a3) {
            Z3_ast r = LIB.Z3_substitute_vars(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_sort_to_ast(Z3_context a0, Z3_sort a1) {
            Z3_ast r = LIB.Z3_sort_to_ast(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_func_decl_to_ast(Z3_context a0, Z3_func_decl a1) {
            Z3_ast r = LIB.Z3_func_decl_to_ast(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_pattern_to_ast(Z3_context a0, Z3_pattern a1) {
            Z3_ast r = LIB.Z3_pattern_to_ast(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_app_to_ast(Z3_context a0, Z3_app a1) {
            Z3_ast r = LIB.Z3_app_to_ast(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_app Z3_to_app(Z3_context a0, Z3_ast a1) {
            Z3_app r = LIB.Z3_to_app(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_func_decl Z3_to_func_decl(Z3_context a0, Z3_ast a1) {
            Z3_func_decl r = LIB.Z3_to_func_decl(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_push(Z3_context a0) {
            LIB.Z3_push(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_pop(Z3_context a0, uint a1) {
            LIB.Z3_pop(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static uint Z3_get_num_scopes(Z3_context a0) {
            uint r = LIB.Z3_get_num_scopes(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_persist_ast(Z3_context a0, Z3_ast a1, uint a2) {
            LIB.Z3_persist_ast(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_assert_cnstr(Z3_context a0, Z3_ast a1) {
            LIB.Z3_assert_cnstr(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static int Z3_check_and_get_model(Z3_context a0, [In, Out] ref Z3_model a1) {
            int r = LIB.Z3_check_and_get_model(a0, ref a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_check(Z3_context a0) {
            int r = LIB.Z3_check(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_check_assumptions(Z3_context a0, uint a1, [In] Z3_ast[] a2, [In, Out] ref Z3_model a3, [In, Out] ref Z3_ast a4, [In, Out] ref uint a5, [Out] Z3_ast[] a6) {
            int r = LIB.Z3_check_assumptions(a0, a1, a2, ref a3, ref a4, ref a5, a6);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_implied_equalities(Z3_context a0, uint a1, [In] Z3_ast[] a2, [Out] uint[] a3) {
            uint r = LIB.Z3_get_implied_equalities(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_del_model(Z3_context a0, Z3_model a1) {
            LIB.Z3_del_model(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_soft_check_cancel(Z3_context a0) {
            LIB.Z3_soft_check_cancel(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static uint Z3_get_search_failure(Z3_context a0) {
            uint r = LIB.Z3_get_search_failure(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_literals Z3_get_relevant_labels(Z3_context a0) {
            Z3_literals r = LIB.Z3_get_relevant_labels(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_literals Z3_get_relevant_literals(Z3_context a0) {
            Z3_literals r = LIB.Z3_get_relevant_literals(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_literals Z3_get_guessed_literals(Z3_context a0) {
            Z3_literals r = LIB.Z3_get_guessed_literals(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_del_literals(Z3_context a0, Z3_literals a1) {
            LIB.Z3_del_literals(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static uint Z3_get_num_literals(Z3_context a0, Z3_literals a1) {
            uint r = LIB.Z3_get_num_literals(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static IntPtr Z3_get_label_symbol(Z3_context a0, Z3_literals a1, uint a2) {
            IntPtr r = LIB.Z3_get_label_symbol(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_get_literal(Z3_context a0, Z3_literals a1, uint a2) {
            Z3_ast r = LIB.Z3_get_literal(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_disable_literal(Z3_context a0, Z3_literals a1, uint a2) {
            LIB.Z3_disable_literal(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_block_literals(Z3_context a0, Z3_literals a1) {
            LIB.Z3_block_literals(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_model_inc_ref(Z3_context a0, Z3_model a1) {
            LIB.Z3_model_inc_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_model_dec_ref(Z3_context a0, Z3_model a1) {
            LIB.Z3_model_dec_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static Z3_ast Z3_model_get_const_interp(Z3_context a0, Z3_model a1, Z3_func_decl a2) {
            Z3_ast r = LIB.Z3_model_get_const_interp(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_func_interp Z3_model_get_func_interp(Z3_context a0, Z3_model a1, Z3_func_decl a2) {
            Z3_func_interp r = LIB.Z3_model_get_func_interp(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_model_get_num_consts(Z3_context a0, Z3_model a1) {
            uint r = LIB.Z3_model_get_num_consts(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_func_decl Z3_model_get_const_decl(Z3_context a0, Z3_model a1, uint a2) {
            Z3_func_decl r = LIB.Z3_model_get_const_decl(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_model_get_num_funcs(Z3_context a0, Z3_model a1) {
            uint r = LIB.Z3_model_get_num_funcs(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_func_decl Z3_model_get_func_decl(Z3_context a0, Z3_model a1, uint a2) {
            Z3_func_decl r = LIB.Z3_model_get_func_decl(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_model_eval(Z3_context a0, Z3_model a1, Z3_ast a2, int a3, [In, Out] ref Z3_ast a4) {
            int r = LIB.Z3_model_eval(a0, a1, a2, a3, ref a4);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_model_get_num_sorts(Z3_context a0, Z3_model a1) {
            uint r = LIB.Z3_model_get_num_sorts(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_sort Z3_model_get_sort(Z3_context a0, Z3_model a1, uint a2) {
            Z3_sort r = LIB.Z3_model_get_sort(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast_vector Z3_model_get_sort_universe(Z3_context a0, Z3_model a1, Z3_sort a2) {
            Z3_ast_vector r = LIB.Z3_model_get_sort_universe(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_is_as_array(Z3_context a0, Z3_ast a1) {
            int r = LIB.Z3_is_as_array(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_func_decl Z3_get_as_array_func_decl(Z3_context a0, Z3_ast a1) {
            Z3_func_decl r = LIB.Z3_get_as_array_func_decl(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_func_interp_inc_ref(Z3_context a0, Z3_func_interp a1) {
            LIB.Z3_func_interp_inc_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_func_interp_dec_ref(Z3_context a0, Z3_func_interp a1) {
            LIB.Z3_func_interp_dec_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static uint Z3_func_interp_get_num_entries(Z3_context a0, Z3_func_interp a1) {
            uint r = LIB.Z3_func_interp_get_num_entries(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_func_entry Z3_func_interp_get_entry(Z3_context a0, Z3_func_interp a1, uint a2) {
            Z3_func_entry r = LIB.Z3_func_interp_get_entry(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_func_interp_get_else(Z3_context a0, Z3_func_interp a1) {
            Z3_ast r = LIB.Z3_func_interp_get_else(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_func_interp_get_arity(Z3_context a0, Z3_func_interp a1) {
            uint r = LIB.Z3_func_interp_get_arity(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_func_entry_inc_ref(Z3_context a0, Z3_func_entry a1) {
            LIB.Z3_func_entry_inc_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_func_entry_dec_ref(Z3_context a0, Z3_func_entry a1) {
            LIB.Z3_func_entry_dec_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static Z3_ast Z3_func_entry_get_value(Z3_context a0, Z3_func_entry a1) {
            Z3_ast r = LIB.Z3_func_entry_get_value(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_func_entry_get_num_args(Z3_context a0, Z3_func_entry a1) {
            uint r = LIB.Z3_func_entry_get_num_args(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_func_entry_get_arg(Z3_context a0, Z3_func_entry a1, uint a2) {
            Z3_ast r = LIB.Z3_func_entry_get_arg(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_model_num_constants(Z3_context a0, Z3_model a1) {
            uint r = LIB.Z3_get_model_num_constants(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_func_decl Z3_get_model_constant(Z3_context a0, Z3_model a1, uint a2) {
            Z3_func_decl r = LIB.Z3_get_model_constant(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_eval_func_decl(Z3_context a0, Z3_model a1, Z3_func_decl a2, [In, Out] ref Z3_ast a3) {
            int r = LIB.Z3_eval_func_decl(a0, a1, a2, ref a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_is_array_value(Z3_context a0, Z3_model a1, Z3_ast a2, [In, Out] ref uint a3) {
            int r = LIB.Z3_is_array_value(a0, a1, a2, ref a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_get_array_value(Z3_context a0, Z3_model a1, Z3_ast a2, uint a3, [Out] Z3_ast[] a4, [Out] Z3_ast[] a5, [In, Out] ref Z3_ast a6) {
            LIB.Z3_get_array_value(a0, a1, a2, a3, a4, a5, ref a6);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static uint Z3_get_model_num_funcs(Z3_context a0, Z3_model a1) {
            uint r = LIB.Z3_get_model_num_funcs(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_func_decl Z3_get_model_func_decl(Z3_context a0, Z3_model a1, uint a2) {
            Z3_func_decl r = LIB.Z3_get_model_func_decl(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_get_model_func_else(Z3_context a0, Z3_model a1, uint a2) {
            Z3_ast r = LIB.Z3_get_model_func_else(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_model_func_num_entries(Z3_context a0, Z3_model a1, uint a2) {
            uint r = LIB.Z3_get_model_func_num_entries(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_model_func_entry_num_args(Z3_context a0, Z3_model a1, uint a2, uint a3) {
            uint r = LIB.Z3_get_model_func_entry_num_args(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_get_model_func_entry_arg(Z3_context a0, Z3_model a1, uint a2, uint a3, uint a4) {
            Z3_ast r = LIB.Z3_get_model_func_entry_arg(a0, a1, a2, a3, a4);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_get_model_func_entry_value(Z3_context a0, Z3_model a1, uint a2, uint a3) {
            Z3_ast r = LIB.Z3_get_model_func_entry_value(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_eval(Z3_context a0, Z3_model a1, Z3_ast a2, [In, Out] ref Z3_ast a3) {
            int r = LIB.Z3_eval(a0, a1, a2, ref a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_eval_decl(Z3_context a0, Z3_model a1, Z3_func_decl a2, uint a3, [In] Z3_ast[] a4, [In, Out] ref Z3_ast a5) {
            int r = LIB.Z3_eval_decl(a0, a1, a2, a3, a4, ref a5);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_set_ast_print_mode(Z3_context a0, uint a1) {
            LIB.Z3_set_ast_print_mode(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static string Z3_ast_to_string(Z3_context a0, Z3_ast a1) {
            IntPtr r = LIB.Z3_ast_to_string(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static string Z3_pattern_to_string(Z3_context a0, Z3_pattern a1) {
            IntPtr r = LIB.Z3_pattern_to_string(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static string Z3_sort_to_string(Z3_context a0, Z3_sort a1) {
            IntPtr r = LIB.Z3_sort_to_string(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static string Z3_func_decl_to_string(Z3_context a0, Z3_func_decl a1) {
            IntPtr r = LIB.Z3_func_decl_to_string(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static string Z3_model_to_string(Z3_context a0, Z3_model a1) {
            IntPtr r = LIB.Z3_model_to_string(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static string Z3_benchmark_to_smtlib_string(Z3_context a0, string a1, string a2, string a3, string a4, uint a5, [In] Z3_ast[] a6, Z3_ast a7) {
            IntPtr r = LIB.Z3_benchmark_to_smtlib_string(a0, a1, a2, a3, a4, a5, a6, a7);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static string Z3_context_to_string(Z3_context a0) {
            IntPtr r = LIB.Z3_context_to_string(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static string Z3_statistics_to_string(Z3_context a0) {
            IntPtr r = LIB.Z3_statistics_to_string(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static Z3_ast Z3_get_context_assignment(Z3_context a0) {
            Z3_ast r = LIB.Z3_get_context_assignment(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_parse_smtlib_string(Z3_context a0, string a1, uint a2, [In] IntPtr[] a3, [In] Z3_sort[] a4, uint a5, [In] IntPtr[] a6, [In] Z3_func_decl[] a7) {
            LIB.Z3_parse_smtlib_string(a0, a1, a2, a3, a4, a5, a6, a7);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_parse_smtlib_file(Z3_context a0, string a1, uint a2, [In] IntPtr[] a3, [In] Z3_sort[] a4, uint a5, [In] IntPtr[] a6, [In] Z3_func_decl[] a7) {
            LIB.Z3_parse_smtlib_file(a0, a1, a2, a3, a4, a5, a6, a7);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static uint Z3_get_smtlib_num_formulas(Z3_context a0) {
            uint r = LIB.Z3_get_smtlib_num_formulas(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_get_smtlib_formula(Z3_context a0, uint a1) {
            Z3_ast r = LIB.Z3_get_smtlib_formula(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_smtlib_num_assumptions(Z3_context a0) {
            uint r = LIB.Z3_get_smtlib_num_assumptions(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_get_smtlib_assumption(Z3_context a0, uint a1) {
            Z3_ast r = LIB.Z3_get_smtlib_assumption(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_smtlib_num_decls(Z3_context a0) {
            uint r = LIB.Z3_get_smtlib_num_decls(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_func_decl Z3_get_smtlib_decl(Z3_context a0, uint a1) {
            Z3_func_decl r = LIB.Z3_get_smtlib_decl(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_smtlib_num_sorts(Z3_context a0) {
            uint r = LIB.Z3_get_smtlib_num_sorts(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_sort Z3_get_smtlib_sort(Z3_context a0, uint a1) {
            Z3_sort r = LIB.Z3_get_smtlib_sort(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static string Z3_get_smtlib_error(Z3_context a0) {
            IntPtr r = LIB.Z3_get_smtlib_error(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static Z3_ast Z3_parse_z3_string(Z3_context a0, string a1) {
            Z3_ast r = LIB.Z3_parse_z3_string(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_parse_z3_file(Z3_context a0, string a1) {
            Z3_ast r = LIB.Z3_parse_z3_file(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_parse_smtlib2_string(Z3_context a0, string a1, uint a2, [In] IntPtr[] a3, [In] Z3_sort[] a4, uint a5, [In] IntPtr[] a6, [In] Z3_func_decl[] a7) {
            Z3_ast r = LIB.Z3_parse_smtlib2_string(a0, a1, a2, a3, a4, a5, a6, a7);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_parse_smtlib2_file(Z3_context a0, string a1, uint a2, [In] IntPtr[] a3, [In] Z3_sort[] a4, uint a5, [In] IntPtr[] a6, [In] Z3_func_decl[] a7) {
            Z3_ast r = LIB.Z3_parse_smtlib2_file(a0, a1, a2, a3, a4, a5, a6, a7);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_error_code(Z3_context a0) {
            uint r = LIB.Z3_get_error_code(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_set_error(Z3_context a0, uint a1) {
            LIB.Z3_set_error(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static string Z3_get_error_msg(uint a0) {
            IntPtr r = LIB.Z3_get_error_msg(a0);
            return Marshal.PtrToStringAnsi(r);
        }

        public static void Z3_get_version([In, Out] ref uint a0, [In, Out] ref uint a1, [In, Out] ref uint a2, [In, Out] ref uint a3) {
            LIB.Z3_get_version(ref a0, ref a1, ref a2, ref a3);
        }

        public static void Z3_reset_memory() {
            LIB.Z3_reset_memory();
        }

        public static int Z3_is_app(Z3_context a0, Z3_ast a1) {
            int r = LIB.Z3_is_app(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_is_numeral_ast(Z3_context a0, Z3_ast a1) {
            int r = LIB.Z3_is_numeral_ast(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_arity(Z3_context a0, Z3_func_decl a1) {
            uint r = LIB.Z3_get_arity(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_func_decl Z3_mk_injective_function(Z3_context a0, IntPtr a1, uint a2, [In] Z3_sort[] a3, Z3_sort a4) {
            Z3_func_decl r = LIB.Z3_mk_injective_function(a0, a1, a2, a3, a4);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_fixedpoint Z3_mk_fixedpoint(Z3_context a0) {
            Z3_fixedpoint r = LIB.Z3_mk_fixedpoint(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_fixedpoint_inc_ref(Z3_context a0, Z3_fixedpoint a1) {
            LIB.Z3_fixedpoint_inc_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_fixedpoint_dec_ref(Z3_context a0, Z3_fixedpoint a1) {
            LIB.Z3_fixedpoint_dec_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_fixedpoint_push(Z3_context a0, Z3_fixedpoint a1) {
            LIB.Z3_fixedpoint_push(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_fixedpoint_pop(Z3_context a0, Z3_fixedpoint a1) {
            LIB.Z3_fixedpoint_pop(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_fixedpoint_register_relation(Z3_context a0, Z3_fixedpoint a1, Z3_func_decl a2) {
            LIB.Z3_fixedpoint_register_relation(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_fixedpoint_assert(Z3_context a0, Z3_fixedpoint a1, Z3_ast a2) {
            LIB.Z3_fixedpoint_assert(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_fixedpoint_add_rule(Z3_context a0, Z3_fixedpoint a1, Z3_ast a2, IntPtr a3) {
            LIB.Z3_fixedpoint_add_rule(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_fixedpoint_add_fact(Z3_context a0, Z3_fixedpoint a1, Z3_func_decl a2, uint a3, [In] uint[] a4) {
            LIB.Z3_fixedpoint_add_fact(a0, a1, a2, a3, a4);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static int Z3_fixedpoint_query(Z3_context a0, Z3_fixedpoint a1, Z3_ast a2) {
            int r = LIB.Z3_fixedpoint_query(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_fixedpoint_query_relations(Z3_context a0, Z3_fixedpoint a1, uint a2, [In] Z3_func_decl[] a3) {
            int r = LIB.Z3_fixedpoint_query_relations(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_fixedpoint_get_answer(Z3_context a0, Z3_fixedpoint a1) {
            Z3_ast r = LIB.Z3_fixedpoint_get_answer(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_fixedpoint_update_rule(Z3_context a0, Z3_fixedpoint a1, Z3_ast a2, IntPtr a3) {
            LIB.Z3_fixedpoint_update_rule(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static uint Z3_fixedpoint_get_num_levels(Z3_context a0, Z3_fixedpoint a1, Z3_func_decl a2) {
            uint r = LIB.Z3_fixedpoint_get_num_levels(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_fixedpoint_get_cover_delta(Z3_context a0, Z3_fixedpoint a1, int a2, Z3_func_decl a3) {
            Z3_ast r = LIB.Z3_fixedpoint_get_cover_delta(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_fixedpoint_add_cover(Z3_context a0, Z3_fixedpoint a1, int a2, Z3_func_decl a3, Z3_ast a4) {
            LIB.Z3_fixedpoint_add_cover(a0, a1, a2, a3, a4);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static Z3_stats Z3_fixedpoint_get_statistics(Z3_context a0, Z3_fixedpoint a1) {
            Z3_stats r = LIB.Z3_fixedpoint_get_statistics(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static string Z3_fixedpoint_get_help(Z3_context a0, Z3_fixedpoint a1) {
            IntPtr r = LIB.Z3_fixedpoint_get_help(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static Z3_param_descrs Z3_fixedpoint_get_param_descrs(Z3_context a0, Z3_fixedpoint a1) {
            Z3_param_descrs r = LIB.Z3_fixedpoint_get_param_descrs(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_fixedpoint_set_params(Z3_context a0, Z3_fixedpoint a1, Z3_params a2) {
            LIB.Z3_fixedpoint_set_params(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static string Z3_fixedpoint_to_string(Z3_context a0, Z3_fixedpoint a1, uint a2, [In] Z3_ast[] a3) {
            IntPtr r = LIB.Z3_fixedpoint_to_string(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static string Z3_fixedpoint_get_reason_unknown(Z3_context a0, Z3_fixedpoint a1) {
            IntPtr r = LIB.Z3_fixedpoint_get_reason_unknown(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static void Z3_fixedpoint_set_predicate_representation(Z3_context a0, Z3_fixedpoint a1, Z3_func_decl a2, uint a3, [In] IntPtr[] a4) {
            LIB.Z3_fixedpoint_set_predicate_representation(a0, a1, a2, a3, a4);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static Z3_ast_vector Z3_fixedpoint_simplify_rules(Z3_context a0, Z3_fixedpoint a1, uint a2, [In] Z3_ast[] a3, uint a4, [In] Z3_func_decl[] a5) {
            Z3_ast_vector r = LIB.Z3_fixedpoint_simplify_rules(a0, a1, a2, a3, a4, a5);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_params Z3_mk_params(Z3_context a0) {
            Z3_params r = LIB.Z3_mk_params(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_params_inc_ref(Z3_context a0, Z3_params a1) {
            LIB.Z3_params_inc_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_params_dec_ref(Z3_context a0, Z3_params a1) {
            LIB.Z3_params_dec_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_params_set_bool(Z3_context a0, Z3_params a1, IntPtr a2, int a3) {
            LIB.Z3_params_set_bool(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_params_set_uint(Z3_context a0, Z3_params a1, IntPtr a2, uint a3) {
            LIB.Z3_params_set_uint(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_params_set_double(Z3_context a0, Z3_params a1, IntPtr a2, double a3) {
            LIB.Z3_params_set_double(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_params_set_symbol(Z3_context a0, Z3_params a1, IntPtr a2, IntPtr a3) {
            LIB.Z3_params_set_symbol(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static string Z3_params_to_string(Z3_context a0, Z3_params a1) {
            IntPtr r = LIB.Z3_params_to_string(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static void Z3_params_validate(Z3_context a0, Z3_params a1, Z3_param_descrs a2) {
            LIB.Z3_params_validate(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_param_descrs_inc_ref(Z3_context a0, Z3_param_descrs a1) {
            LIB.Z3_param_descrs_inc_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_param_descrs_dec_ref(Z3_context a0, Z3_param_descrs a1) {
            LIB.Z3_param_descrs_dec_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static uint Z3_param_descrs_get_kind(Z3_context a0, Z3_param_descrs a1, IntPtr a2) {
            uint r = LIB.Z3_param_descrs_get_kind(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_param_descrs_size(Z3_context a0, Z3_param_descrs a1) {
            uint r = LIB.Z3_param_descrs_size(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static IntPtr Z3_param_descrs_get_name(Z3_context a0, Z3_param_descrs a1, uint a2) {
            IntPtr r = LIB.Z3_param_descrs_get_name(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_interrupt(Z3_context a0) {
            LIB.Z3_interrupt(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static string Z3_get_error_msg_ex(Z3_context a0, uint a1) {
            IntPtr r = LIB.Z3_get_error_msg_ex(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static Z3_ast Z3_translate(Z3_context a0, Z3_ast a1, Z3_context a2) {
            Z3_ast r = LIB.Z3_translate(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_goal Z3_mk_goal(Z3_context a0, int a1, int a2, int a3) {
            Z3_goal r = LIB.Z3_mk_goal(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_goal_inc_ref(Z3_context a0, Z3_goal a1) {
            LIB.Z3_goal_inc_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_goal_dec_ref(Z3_context a0, Z3_goal a1) {
            LIB.Z3_goal_dec_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static uint Z3_goal_precision(Z3_context a0, Z3_goal a1) {
            uint r = LIB.Z3_goal_precision(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_goal_assert(Z3_context a0, Z3_goal a1, Z3_ast a2) {
            LIB.Z3_goal_assert(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static int Z3_goal_inconsistent(Z3_context a0, Z3_goal a1) {
            int r = LIB.Z3_goal_inconsistent(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_goal_depth(Z3_context a0, Z3_goal a1) {
            uint r = LIB.Z3_goal_depth(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_goal_reset(Z3_context a0, Z3_goal a1) {
            LIB.Z3_goal_reset(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static uint Z3_goal_size(Z3_context a0, Z3_goal a1) {
            uint r = LIB.Z3_goal_size(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_goal_formula(Z3_context a0, Z3_goal a1, uint a2) {
            Z3_ast r = LIB.Z3_goal_formula(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_goal_num_exprs(Z3_context a0, Z3_goal a1) {
            uint r = LIB.Z3_goal_num_exprs(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_goal_is_decided_sat(Z3_context a0, Z3_goal a1) {
            int r = LIB.Z3_goal_is_decided_sat(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_goal_is_decided_unsat(Z3_context a0, Z3_goal a1) {
            int r = LIB.Z3_goal_is_decided_unsat(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_goal Z3_goal_translate(Z3_context a0, Z3_goal a1, Z3_context a2) {
            Z3_goal r = LIB.Z3_goal_translate(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static string Z3_goal_to_string(Z3_context a0, Z3_goal a1) {
            IntPtr r = LIB.Z3_goal_to_string(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static Z3_tactic Z3_mk_tactic(Z3_context a0, string a1) {
            Z3_tactic r = LIB.Z3_mk_tactic(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_probe Z3_mk_probe(Z3_context a0, string a1) {
            Z3_probe r = LIB.Z3_mk_probe(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_tactic_inc_ref(Z3_context a0, Z3_tactic a1) {
            LIB.Z3_tactic_inc_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_tactic_dec_ref(Z3_context a0, Z3_tactic a1) {
            LIB.Z3_tactic_dec_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_probe_inc_ref(Z3_context a0, Z3_probe a1) {
            LIB.Z3_probe_inc_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_probe_dec_ref(Z3_context a0, Z3_probe a1) {
            LIB.Z3_probe_dec_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static Z3_tactic Z3_tactic_and_then(Z3_context a0, Z3_tactic a1, Z3_tactic a2) {
            Z3_tactic r = LIB.Z3_tactic_and_then(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_tactic Z3_tactic_or_else(Z3_context a0, Z3_tactic a1, Z3_tactic a2) {
            Z3_tactic r = LIB.Z3_tactic_or_else(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_tactic Z3_tactic_par_or(Z3_context a0, uint a1, [In] Z3_tactic[] a2) {
            Z3_tactic r = LIB.Z3_tactic_par_or(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_tactic Z3_tactic_par_and_then(Z3_context a0, Z3_tactic a1, Z3_tactic a2) {
            Z3_tactic r = LIB.Z3_tactic_par_and_then(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_tactic Z3_tactic_try_for(Z3_context a0, Z3_tactic a1, uint a2) {
            Z3_tactic r = LIB.Z3_tactic_try_for(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_tactic Z3_tactic_when(Z3_context a0, Z3_probe a1, Z3_tactic a2) {
            Z3_tactic r = LIB.Z3_tactic_when(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_tactic Z3_tactic_cond(Z3_context a0, Z3_probe a1, Z3_tactic a2, Z3_tactic a3) {
            Z3_tactic r = LIB.Z3_tactic_cond(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_tactic Z3_tactic_repeat(Z3_context a0, Z3_tactic a1, uint a2) {
            Z3_tactic r = LIB.Z3_tactic_repeat(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_tactic Z3_tactic_skip(Z3_context a0) {
            Z3_tactic r = LIB.Z3_tactic_skip(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_tactic Z3_tactic_fail(Z3_context a0) {
            Z3_tactic r = LIB.Z3_tactic_fail(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_tactic Z3_tactic_fail_if(Z3_context a0, Z3_probe a1) {
            Z3_tactic r = LIB.Z3_tactic_fail_if(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_tactic Z3_tactic_fail_if_not_decided(Z3_context a0) {
            Z3_tactic r = LIB.Z3_tactic_fail_if_not_decided(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_tactic Z3_tactic_using_params(Z3_context a0, Z3_tactic a1, Z3_params a2) {
            Z3_tactic r = LIB.Z3_tactic_using_params(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_probe Z3_probe_const(Z3_context a0, double a1) {
            Z3_probe r = LIB.Z3_probe_const(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_probe Z3_probe_lt(Z3_context a0, Z3_probe a1, Z3_probe a2) {
            Z3_probe r = LIB.Z3_probe_lt(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_probe Z3_probe_le(Z3_context a0, Z3_probe a1, Z3_probe a2) {
            Z3_probe r = LIB.Z3_probe_le(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_probe Z3_probe_gt(Z3_context a0, Z3_probe a1, Z3_probe a2) {
            Z3_probe r = LIB.Z3_probe_gt(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_probe Z3_probe_ge(Z3_context a0, Z3_probe a1, Z3_probe a2) {
            Z3_probe r = LIB.Z3_probe_ge(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_probe Z3_probe_eq(Z3_context a0, Z3_probe a1, Z3_probe a2) {
            Z3_probe r = LIB.Z3_probe_eq(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_probe Z3_probe_and(Z3_context a0, Z3_probe a1, Z3_probe a2) {
            Z3_probe r = LIB.Z3_probe_and(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_probe Z3_probe_or(Z3_context a0, Z3_probe a1, Z3_probe a2) {
            Z3_probe r = LIB.Z3_probe_or(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_probe Z3_probe_not(Z3_context a0, Z3_probe a1) {
            Z3_probe r = LIB.Z3_probe_not(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_get_num_tactics(Z3_context a0) {
            uint r = LIB.Z3_get_num_tactics(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static string Z3_get_tactic_name(Z3_context a0, uint a1) {
            IntPtr r = LIB.Z3_get_tactic_name(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static uint Z3_get_num_probes(Z3_context a0) {
            uint r = LIB.Z3_get_num_probes(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static string Z3_get_probe_name(Z3_context a0, uint a1) {
            IntPtr r = LIB.Z3_get_probe_name(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static string Z3_tactic_get_help(Z3_context a0, Z3_tactic a1) {
            IntPtr r = LIB.Z3_tactic_get_help(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static Z3_param_descrs Z3_tactic_get_param_descrs(Z3_context a0, Z3_tactic a1) {
            Z3_param_descrs r = LIB.Z3_tactic_get_param_descrs(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static string Z3_tactic_get_descr(Z3_context a0, string a1) {
            IntPtr r = LIB.Z3_tactic_get_descr(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static string Z3_probe_get_descr(Z3_context a0, string a1) {
            IntPtr r = LIB.Z3_probe_get_descr(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static double Z3_probe_apply(Z3_context a0, Z3_probe a1, Z3_goal a2) {
            double r = LIB.Z3_probe_apply(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_apply_result Z3_tactic_apply(Z3_context a0, Z3_tactic a1, Z3_goal a2) {
            Z3_apply_result r = LIB.Z3_tactic_apply(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_apply_result Z3_tactic_apply_ex(Z3_context a0, Z3_tactic a1, Z3_goal a2, Z3_params a3) {
            Z3_apply_result r = LIB.Z3_tactic_apply_ex(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_apply_result_inc_ref(Z3_context a0, Z3_apply_result a1) {
            LIB.Z3_apply_result_inc_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_apply_result_dec_ref(Z3_context a0, Z3_apply_result a1) {
            LIB.Z3_apply_result_dec_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static string Z3_apply_result_to_string(Z3_context a0, Z3_apply_result a1) {
            IntPtr r = LIB.Z3_apply_result_to_string(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static uint Z3_apply_result_get_num_subgoals(Z3_context a0, Z3_apply_result a1) {
            uint r = LIB.Z3_apply_result_get_num_subgoals(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_goal Z3_apply_result_get_subgoal(Z3_context a0, Z3_apply_result a1, uint a2) {
            Z3_goal r = LIB.Z3_apply_result_get_subgoal(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_model Z3_apply_result_convert_model(Z3_context a0, Z3_apply_result a1, uint a2, Z3_model a3) {
            Z3_model r = LIB.Z3_apply_result_convert_model(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_solver Z3_mk_solver(Z3_context a0) {
            Z3_solver r = LIB.Z3_mk_solver(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_solver Z3_mk_simple_solver(Z3_context a0) {
            Z3_solver r = LIB.Z3_mk_simple_solver(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_solver Z3_mk_solver_for_logic(Z3_context a0, IntPtr a1) {
            Z3_solver r = LIB.Z3_mk_solver_for_logic(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_solver Z3_mk_solver_from_tactic(Z3_context a0, Z3_tactic a1) {
            Z3_solver r = LIB.Z3_mk_solver_from_tactic(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static string Z3_solver_get_help(Z3_context a0, Z3_solver a1) {
            IntPtr r = LIB.Z3_solver_get_help(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static Z3_param_descrs Z3_solver_get_param_descrs(Z3_context a0, Z3_solver a1) {
            Z3_param_descrs r = LIB.Z3_solver_get_param_descrs(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_solver_set_params(Z3_context a0, Z3_solver a1, Z3_params a2) {
            LIB.Z3_solver_set_params(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_solver_inc_ref(Z3_context a0, Z3_solver a1) {
            LIB.Z3_solver_inc_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_solver_dec_ref(Z3_context a0, Z3_solver a1) {
            LIB.Z3_solver_dec_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_solver_push(Z3_context a0, Z3_solver a1) {
            LIB.Z3_solver_push(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_solver_pop(Z3_context a0, Z3_solver a1, uint a2) {
            LIB.Z3_solver_pop(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_solver_reset(Z3_context a0, Z3_solver a1) {
            LIB.Z3_solver_reset(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static uint Z3_solver_get_num_scopes(Z3_context a0, Z3_solver a1) {
            uint r = LIB.Z3_solver_get_num_scopes(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_solver_assert(Z3_context a0, Z3_solver a1, Z3_ast a2) {
            LIB.Z3_solver_assert(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static Z3_ast_vector Z3_solver_get_assertions(Z3_context a0, Z3_solver a1) {
            Z3_ast_vector r = LIB.Z3_solver_get_assertions(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_solver_check(Z3_context a0, Z3_solver a1) {
            int r = LIB.Z3_solver_check(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_solver_check_assumptions(Z3_context a0, Z3_solver a1, uint a2, [In] Z3_ast[] a3) {
            int r = LIB.Z3_solver_check_assumptions(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_model Z3_solver_get_model(Z3_context a0, Z3_solver a1) {
            Z3_model r = LIB.Z3_solver_get_model(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_solver_get_proof(Z3_context a0, Z3_solver a1) {
            Z3_ast r = LIB.Z3_solver_get_proof(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast_vector Z3_solver_get_unsat_core(Z3_context a0, Z3_solver a1) {
            Z3_ast_vector r = LIB.Z3_solver_get_unsat_core(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static string Z3_solver_get_reason_unknown(Z3_context a0, Z3_solver a1) {
            IntPtr r = LIB.Z3_solver_get_reason_unknown(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static Z3_stats Z3_solver_get_statistics(Z3_context a0, Z3_solver a1) {
            Z3_stats r = LIB.Z3_solver_get_statistics(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static string Z3_solver_to_string(Z3_context a0, Z3_solver a1) {
            IntPtr r = LIB.Z3_solver_to_string(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static string Z3_stats_to_string(Z3_context a0, Z3_stats a1) {
            IntPtr r = LIB.Z3_stats_to_string(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static void Z3_stats_inc_ref(Z3_context a0, Z3_stats a1) {
            LIB.Z3_stats_inc_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_stats_dec_ref(Z3_context a0, Z3_stats a1) {
            LIB.Z3_stats_dec_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static uint Z3_stats_size(Z3_context a0, Z3_stats a1) {
            uint r = LIB.Z3_stats_size(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static string Z3_stats_get_key(Z3_context a0, Z3_stats a1, uint a2) {
            IntPtr r = LIB.Z3_stats_get_key(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static int Z3_stats_is_uint(Z3_context a0, Z3_stats a1, uint a2) {
            int r = LIB.Z3_stats_is_uint(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static int Z3_stats_is_double(Z3_context a0, Z3_stats a1, uint a2) {
            int r = LIB.Z3_stats_is_double(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static uint Z3_stats_get_uint_value(Z3_context a0, Z3_stats a1, uint a2) {
            uint r = LIB.Z3_stats_get_uint_value(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static double Z3_stats_get_double_value(Z3_context a0, Z3_stats a1, uint a2) {
            double r = LIB.Z3_stats_get_double_value(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast_vector Z3_mk_ast_vector(Z3_context a0) {
            Z3_ast_vector r = LIB.Z3_mk_ast_vector(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_ast_vector_inc_ref(Z3_context a0, Z3_ast_vector a1) {
            LIB.Z3_ast_vector_inc_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_ast_vector_dec_ref(Z3_context a0, Z3_ast_vector a1) {
            LIB.Z3_ast_vector_dec_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static uint Z3_ast_vector_size(Z3_context a0, Z3_ast_vector a1) {
            uint r = LIB.Z3_ast_vector_size(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_ast_vector_get(Z3_context a0, Z3_ast_vector a1, uint a2) {
            Z3_ast r = LIB.Z3_ast_vector_get(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_ast_vector_set(Z3_context a0, Z3_ast_vector a1, uint a2, Z3_ast a3) {
            LIB.Z3_ast_vector_set(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_ast_vector_resize(Z3_context a0, Z3_ast_vector a1, uint a2) {
            LIB.Z3_ast_vector_resize(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_ast_vector_push(Z3_context a0, Z3_ast_vector a1, Z3_ast a2) {
            LIB.Z3_ast_vector_push(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static Z3_ast_vector Z3_ast_vector_translate(Z3_context a0, Z3_ast_vector a1, Z3_context a2) {
            Z3_ast_vector r = LIB.Z3_ast_vector_translate(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static string Z3_ast_vector_to_string(Z3_context a0, Z3_ast_vector a1) {
            IntPtr r = LIB.Z3_ast_vector_to_string(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static Z3_ast_map Z3_mk_ast_map(Z3_context a0) {
            Z3_ast_map r = LIB.Z3_mk_ast_map(a0);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_ast_map_inc_ref(Z3_context a0, Z3_ast_map a1) {
            LIB.Z3_ast_map_inc_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_ast_map_dec_ref(Z3_context a0, Z3_ast_map a1) {
            LIB.Z3_ast_map_dec_ref(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static int Z3_ast_map_contains(Z3_context a0, Z3_ast_map a1, Z3_ast a2) {
            int r = LIB.Z3_ast_map_contains(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static Z3_ast Z3_ast_map_find(Z3_context a0, Z3_ast_map a1, Z3_ast a2) {
            Z3_ast r = LIB.Z3_ast_map_find(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_ast_map_insert(Z3_context a0, Z3_ast_map a1, Z3_ast a2, Z3_ast a3) {
            LIB.Z3_ast_map_insert(a0, a1, a2, a3);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static void Z3_ast_map_erase(Z3_context a0, Z3_ast_map a1, Z3_ast a2) {
            LIB.Z3_ast_map_erase(a0, a1, a2);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static uint Z3_ast_map_size(Z3_context a0, Z3_ast_map a1) {
            uint r = LIB.Z3_ast_map_size(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static void Z3_ast_map_reset(Z3_context a0, Z3_ast_map a1) {
            LIB.Z3_ast_map_reset(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
        }

        public static Z3_ast_vector Z3_ast_map_keys(Z3_context a0, Z3_ast_map a1) {
            Z3_ast_vector r = LIB.Z3_ast_map_keys(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return r;
        }

        public static string Z3_ast_map_to_string(Z3_context a0, Z3_ast_map a1) {
            IntPtr r = LIB.Z3_ast_map_to_string(a0, a1);
            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);
            if (err != Z3_error_code.Z3_OK)
                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));
            return Marshal.PtrToStringAnsi(r);
        }

        public static int Z3_open_log(string a0) {
            int r = LIB.Z3_open_log(a0);
            return r;
        }

        public static void Z3_append_log(string a0) {
            LIB.Z3_append_log(a0);
        }

        public static void Z3_close_log() {
            LIB.Z3_close_log();
        }

    }

}

