/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

   InterpolationContext.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

import java.util.Map;
import java.lang.String;

import com.microsoft.z3.enumerations.Z3_lbool;

/** 
 *  The InterpolationContext is suitable for generation of interpolants.
 *
 * Remarks: For more information on interpolation please refer
 * too the C/C++ API, which is well documented. 
 **/
public class InterpolationContext extends Context
{
    /**
     * Constructor.
     **/
    public InterpolationContext() throws Z3Exception
    {
        m_ctx = Native.mkInterpolationContext(0);
        initContext(); 
    }

    /** 
     * Constructor.
     *
     * 
     * Remarks: 
     * @see Context#Context
     **/
    public InterpolationContext(Map<String, String> settings) throws Z3Exception
    { 
        long cfg = Native.mkConfig();
        for (Map.Entry<String, String> kv : settings.entrySet())
            Native.setParamValue(cfg, kv.getKey(), kv.getValue());
        m_ctx = Native.mkInterpolationContext(cfg);
        Native.delConfig(cfg);
        initContext();
    }

    /** 
      * Create an expression that marks a formula position for interpolation.
      * @throws Z3Exception 
      **/
    public BoolExpr MkInterpolant(BoolExpr a) throws Z3Exception
    {
        checkContextMatch(a);        
        return new BoolExpr(this, Native.mkInterpolant(nCtx(), a.getNativeObject()));
    }

    /**
     * Computes an interpolant.
     * Remarks: For more information on interpolation please refer
     * too the function Z3_get_interpolant in the C/C++ API, which is 
     * well documented.
     * @throws Z3Exception 
     **/
    Expr[] GetInterpolant(Expr pf, Expr pat, Params p) throws Z3Exception
    {
        checkContextMatch(pf);
        checkContextMatch(pat);
        checkContextMatch(p);

        ASTVector seq = new ASTVector(this, Native.getInterpolant(nCtx(), pf.getNativeObject(), pat.getNativeObject(), p.getNativeObject()));
        int n = seq.size();
        Expr[] res = new Expr[n];
        for (int i = 0; i < n; i++)
            res[i] = Expr.create(this, seq.get(i).getNativeObject());
        return res;
    }

    /**
     * Computes an interpolant.   
     * Remarks: For more information on interpolation please refer
     * too the function Z3_compute_interpolant in the C/C++ API, which is 
     * well documented.
     * @throws Z3Exception 
     **/
    Z3_lbool ComputeInterpolant(Expr pat, Params p, ASTVector interp, Model model) throws Z3Exception
    {
        checkContextMatch(pat);
        checkContextMatch(p);

        Native.LongPtr n_i = new Native.LongPtr();
        Native.LongPtr n_m = new Native.LongPtr();
        int r = Native.computeInterpolant(nCtx(), pat.getNativeObject(), p.getNativeObject(), n_i, n_m);
        interp = new ASTVector(this, n_i.value);
        model = new Model(this, n_m.value);
        return Z3_lbool.fromInt(r);
    }

    ///  
    /// Return a string summarizing cumulative time used for interpolation.
    ///    
    /// Remarks: For more information on interpolation please refer
    /// too the function Z3_interpolation_profile in the C/C++ API, which is 
    /// well documented.
    public String InterpolationProfile() throws Z3Exception
    {
        return Native.interpolationProfile(nCtx());
    }

    ///  
    /// Checks the correctness of an interpolant.
    ///    
    /// Remarks: For more information on interpolation please refer
    /// too the function Z3_check_interpolant in the C/C++ API, which is 
    /// well documented.
    public int CheckInterpolant(Expr[] cnsts, int[] parents, Expr[] interps, String error, Expr[] theory) throws Z3Exception
    {
        Native.StringPtr n_err_str = new Native.StringPtr();
        int r = Native.checkInterpolant(nCtx(),
                                        cnsts.length,
                                        Expr.arrayToNative(cnsts),
                                        parents,
                                        Expr.arrayToNative(interps),
                                        n_err_str,
                                        theory.length,
                                        Expr.arrayToNative(theory));
        error = n_err_str.value;
        return r;
    }

    ///  
    /// Reads an interpolation problem from a file.
    ///    
    /// Remarks: For more information on interpolation please refer
    /// too the function Z3_read_interpolation_problem in the C/C++ API, which is 
    /// well documented.
    public int ReadInterpolationProblem(String filename, Expr[] cnsts, int[] parents, String error, Expr[] theory) throws Z3Exception
    {
        Native.IntPtr n_num = new Native.IntPtr();
        Native.IntPtr n_num_theory = new Native.IntPtr();
        Native.ObjArrayPtr n_cnsts = new Native.ObjArrayPtr();
        Native.UIntArrayPtr n_parents = new Native.UIntArrayPtr();
        Native.ObjArrayPtr n_theory = new Native.ObjArrayPtr();
        Native.StringPtr n_err_str = new Native.StringPtr();
        int r = Native.readInterpolationProblem(nCtx(), n_num, n_cnsts, n_parents, filename, n_err_str, n_num_theory, n_theory);
        int num = n_num.value;
        int num_theory = n_num_theory.value;
        error = n_err_str.value;
        cnsts = new Expr[num];
        parents = new int[num];
        theory = new Expr[num_theory];
        for (int i = 0; i < num; i++)
        {
            cnsts[i] = Expr.create(this, n_cnsts.value[i]);
            parents[i] = n_parents.value[i];
        }
        for (int i = 0; i < num_theory; i++)
            theory[i] = Expr.create(this, n_theory.value[i]);
        return r;
    }

    ///  
    /// Writes an interpolation problem to a file.
    ///    
    /// Remarks: For more information on interpolation please refer
    /// too the function Z3_write_interpolation_problem in the C/C++ API, which is 
    /// well documented.
    public void WriteInterpolationProblem(String filename, Expr[] cnsts, int[] parents, String error, Expr[] theory) throws Z3Exception
    {
        Native.writeInterpolationProblem(nCtx(), cnsts.length, Expr.arrayToNative(cnsts), parents, filename, theory.length, Expr.arrayToNative(theory));     
    }
}
