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
    public InterpolationContext()
    {
        super();
        synchronized(creation_lock) {
            m_ctx = Native.mkInterpolationContext(0);
            initContext(); 
        }
    }

    /** 
     * Constructor.
     *
     * 
     * Remarks: 
     * @see Context#Context
     **/
    public InterpolationContext(Map<String, String> settings)
    { 
        super();
        synchronized(creation_lock) {
            long cfg = Native.mkConfig();
            for (Map.Entry<String, String> kv : settings.entrySet())
                Native.setParamValue(cfg, kv.getKey(), kv.getValue());
            m_ctx = Native.mkInterpolationContext(cfg);
            Native.delConfig(cfg);
            initContext();
        }
    }

    /** 
      * Create an expression that marks a formula position for interpolation.
      * @throws Z3Exception 
      **/
    public BoolExpr MkInterpolant(BoolExpr a)
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
    public BoolExpr[] GetInterpolant(Expr pf, Expr pat, Params p)
    {
        checkContextMatch(pf);
        checkContextMatch(pat);
        checkContextMatch(p);

        ASTVector seq = new ASTVector(this, Native.getInterpolant(nCtx(), pf.getNativeObject(), pat.getNativeObject(), p.getNativeObject()));
        return seq.ToBoolExprArray();
    }

    public class ComputeInterpolantResult 
    {
        public Z3_lbool status = Z3_lbool.Z3_L_UNDEF;
        public BoolExpr[] interp = null;
        public Model model = null;
    };
    
    /**
     * Computes an interpolant.   
     * Remarks: For more information on interpolation please refer
     * too the function Z3_compute_interpolant in the C/C++ API, which is 
     * well documented.
     * @throws Z3Exception 
     **/
    public ComputeInterpolantResult ComputeInterpolant(Expr pat, Params p)
    {
        checkContextMatch(pat);
        checkContextMatch(p);

        ComputeInterpolantResult res = new ComputeInterpolantResult();
        Native.LongPtr n_i = new Native.LongPtr();
        Native.LongPtr n_m = new Native.LongPtr();
        res.status = Z3_lbool.fromInt(Native.computeInterpolant(nCtx(), pat.getNativeObject(), p.getNativeObject(), n_i, n_m));        
        if (res.status == Z3_lbool.Z3_L_FALSE)
            res.interp = (new ASTVector(this, n_i.value)).ToBoolExprArray();
        if (res.status == Z3_lbool.Z3_L_TRUE) 
            res.model = new Model(this, n_m.value);
        return res;
    }

    ///  
    /// Return a string summarizing cumulative time used for interpolation.
    ///    
    /// Remarks: For more information on interpolation please refer
    /// too the function Z3_interpolation_profile in the C/C++ API, which is 
    /// well documented.
    public String InterpolationProfile()
    {
        return Native.interpolationProfile(nCtx());
    }

    public class CheckInterpolantResult
    {
        public int return_value = 0;
        public String error = null;
    }
    
    ///  
    /// Checks the correctness of an interpolant.
    ///    
    /// Remarks: For more information on interpolation please refer
    /// too the function Z3_check_interpolant in the C/C++ API, which is 
    /// well documented.
    public CheckInterpolantResult CheckInterpolant(Expr[] cnsts, int[] parents, BoolExpr[] interps, String error, Expr[] theory)
    {
        CheckInterpolantResult res = new CheckInterpolantResult();
        Native.StringPtr n_err_str = new Native.StringPtr();
        res.return_value = Native.checkInterpolant(nCtx(),
                                        cnsts.length,
                                        Expr.arrayToNative(cnsts),
                                        parents,
                                        Expr.arrayToNative(interps),
                                        n_err_str,
                                        theory.length,
                                        Expr.arrayToNative(theory));
        res.error = n_err_str.value;
        return res;
    }

    public class ReadInterpolationProblemResult 
    {
        public int return_value = 0;
        public Expr[] cnsts;
        public int[] parents;
        public String error;
        public Expr[] theory;
    };
    
    ///  
    /// Reads an interpolation problem from a file.
    ///    
    /// Remarks: For more information on interpolation please refer
    /// too the function Z3_read_interpolation_problem in the C/C++ API, which is 
    /// well documented.
    public ReadInterpolationProblemResult ReadInterpolationProblem(String filename, Expr[] cnsts, int[] parents, String error, Expr[] theory)
    {
        ReadInterpolationProblemResult res = new ReadInterpolationProblemResult();
        
        Native.IntPtr n_num = new Native.IntPtr();
        Native.IntPtr n_num_theory = new Native.IntPtr();
        Native.ObjArrayPtr n_cnsts = new Native.ObjArrayPtr();
        Native.UIntArrayPtr n_parents = new Native.UIntArrayPtr();
        Native.ObjArrayPtr n_theory = new Native.ObjArrayPtr();
        Native.StringPtr n_err_str = new Native.StringPtr();
        res.return_value = Native.readInterpolationProblem(nCtx(), n_num, n_cnsts, n_parents, filename, n_err_str, n_num_theory, n_theory);
        int num = n_num.value;
        int num_theory = n_num_theory.value;
        res.error = n_err_str.value;
        res.cnsts = new Expr[num];
        res.parents = new int[num];
        theory = new Expr[num_theory];
        for (int i = 0; i < num; i++)
        {
            res.cnsts[i] = Expr.create(this, n_cnsts.value[i]);
            res.parents[i] = n_parents.value[i];
        }
        for (int i = 0; i < num_theory; i++)
            res.theory[i] = Expr.create(this, n_theory.value[i]);
        return res;
    }
    
    ///  
    /// Writes an interpolation problem to a file.
    ///    
    /// Remarks: For more information on interpolation please refer
    /// too the function Z3_write_interpolation_problem in the C/C++ API, which is 
    /// well documented.
    public void WriteInterpolationProblem(String filename, Expr[] cnsts, int[] parents, String error, Expr[] theory)
    {
        Native.writeInterpolationProblem(nCtx(), cnsts.length, Expr.arrayToNative(cnsts), parents, filename, theory.length, Expr.arrayToNative(theory));     
    }
}
