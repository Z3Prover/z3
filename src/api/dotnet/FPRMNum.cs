/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    FPRMExpr.cs

Abstract:

    Z3 Managed API: Floating Point Rounding Mode Numerals

Author:

    Christoph Wintersteiger (cwinter) 2013-06-10

Notes:
    
--*/
using System.Diagnostics;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;


namespace Microsoft.Z3
{
    /// <summary>
    /// Floating-point rounding mode numerals
    /// </summary>
    public class FPRMNum : FPRMExpr
    {
        /// <summary>
        /// Indicates whether the term is the floating-point rounding numeral roundNearestTiesToEven
        /// </summary>
        public bool isRoundNearestTiesToEven { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN; } }

        /// <summary>
        /// Indicates whether the term is the floating-point rounding numeral roundNearestTiesToEven
        /// </summary>
        public bool isRNE { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN; } }

        /// <summary>
        /// Indicates whether the term is the floating-point rounding numeral roundNearestTiesToAway
        /// </summary>
        public bool isRoundNearestTiesToAway { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY; } }

        /// <summary>
        /// Indicates whether the term is the floating-point rounding numeral roundNearestTiesToAway
        /// </summary>
        public bool isRNA { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY; } }

        /// <summary>
        /// Indicates whether the term is the floating-point rounding numeral roundTowardPositive
        /// </summary>
        public bool isRoundTowardPositive { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_POSITIVE; } }

        /// <summary>
        /// Indicates whether the term is the floating-point rounding numeral roundTowardPositive
        /// </summary>
        public bool isRTP { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_POSITIVE; } }

        /// <summary>
        /// Indicates whether the term is the floating-point rounding numeral roundTowardNegative
        /// </summary>
        public bool isRoundTowardNegative { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_NEGATIVE; } }

        /// <summary>
        /// Indicates whether the term is the floating-point rounding numeral roundTowardNegative
        /// </summary>
        public bool isRTN { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_NEGATIVE; } }

        /// <summary>
        /// Indicates whether the term is the floating-point rounding numeral roundTowardZero
        /// </summary>
        public bool isRoundTowardZero { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_ZERO; } }

        /// <summary>
        /// Indicates whether the term is the floating-point rounding numeral roundTowardZero
        /// </summary>
        public bool isRTZ { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_ZERO; } }

        /// <summary>
        /// Returns a string representation of the numeral.
        /// </summary>        
        public override string ToString()
        {
            return Native.Z3_get_numeral_string(Context.nCtx, NativeObject);
        }

        #region Internal
        /// <summary> Constructor for FPRMNum </summary>
        internal FPRMNum(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Debug.Assert(ctx != null);
        }
        #endregion
    }
}
