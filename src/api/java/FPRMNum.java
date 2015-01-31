/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    FPRMNum.java

Abstract:

Author:

    Christoph Wintersteiger (cwinter) 2013-06-10

Notes:
    
--*/
package com.microsoft.z3;

import com.microsoft.z3.enumerations.Z3_decl_kind;

/**
 * FloatingPoint RoundingMode Numerals
 */
public class FPRMNum extends FPRMExpr {

    /**
     * Indicates whether the term is the floating-point rounding numeral roundNearestTiesToEven
     * @throws Z3Exception 
     * **/
    public boolean isRoundNearestTiesToEven() throws Z3Exception { return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN; }

    /**
     * Indicates whether the term is the floating-point rounding numeral roundNearestTiesToEven
     * @throws Z3Exception 
     */
    public boolean isRNE() throws Z3Exception { return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN; }

    /**
     * Indicates whether the term is the floating-point rounding numeral roundNearestTiesToAway
     * @throws Z3Exception 
     */
    public boolean isRoundNearestTiesToAway() throws Z3Exception { return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY; }

    /**
     * Indicates whether the term is the floating-point rounding numeral roundNearestTiesToAway
     * @throws Z3Exception 
     */
    public boolean isRNA() throws Z3Exception { return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY; }

    /**
     * Indicates whether the term is the floating-point rounding numeral roundTowardPositive
     * @throws Z3Exception 
     */
    public boolean isRoundTowardPositive() throws Z3Exception { return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_POSITIVE; }

    /**
     * Indicates whether the term is the floating-point rounding numeral roundTowardPositive
     * @throws Z3Exception 
     */
    public boolean isRTP() throws Z3Exception { return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_POSITIVE; }

    /**
     * Indicates whether the term is the floating-point rounding numeral roundTowardNegative
     * @throws Z3Exception 
     */
    public boolean isRoundTowardNegative() throws Z3Exception { return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_NEGATIVE; }

    /**
     * Indicates whether the term is the floating-point rounding numeral roundTowardNegative
     * @throws Z3Exception 
     */
    public boolean isRTN() throws Z3Exception { return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_NEGATIVE; } 

    /**
     * Indicates whether the term is the floating-point rounding numeral roundTowardZero
     * @throws Z3Exception 
     */
    public boolean isRoundTowardZero() throws Z3Exception { return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_ZERO; }

    /**
     * Indicates whether the term is the floating-point rounding numeral roundTowardZero
     * @throws Z3Exception 
     */
    public boolean isRTZ() throws Z3Exception { return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_ZERO; }
    
    public FPRMNum(Context ctx, long obj) throws Z3Exception {
        super(ctx, obj);
    }

}
