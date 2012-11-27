/**
 * This file was automatically generated from Params.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * A ParameterSet represents a configuration in the form of Symbol/value pairs.
 **/
public class Params extends Z3Object
{
    /**
     * Adds a parameter setting.
     **/
    public void Add(Symbol name, boolean value) throws Z3Exception
    {
        Native.paramsSetBool(Context().nCtx(), NativeObject(),
                name.NativeObject(), (value) ? true : false);
    }

    /**
     * Adds a parameter setting.
     **/
    public void Add(Symbol name, double value) throws Z3Exception
    {
        Native.paramsSetDouble(Context().nCtx(), NativeObject(),
                name.NativeObject(), value);
    }

    /**
     * Adds a parameter setting.
     **/
    public void Add(Symbol name, Symbol value) throws Z3Exception
    {

        Native.paramsSetSymbol(Context().nCtx(), NativeObject(),
                name.NativeObject(), value.NativeObject());
    }

    /**
     * Adds a parameter setting.
     **/
    public void Add(String name, boolean value) throws Z3Exception
    {
        Native.paramsSetBool(Context().nCtx(), NativeObject(), Context()
                .MkSymbol(name).NativeObject(), (value) ? true : false);
    }

    /**
     * Adds a parameter setting.
     **/
    public void Add(String name, int value) throws Z3Exception
    {
        Native.paramsSetUint(Context().nCtx(), NativeObject(), Context()
                .MkSymbol(name).NativeObject(), value);
    }

    /**
     * Adds a parameter setting.
     **/
    public void Add(String name, double value) throws Z3Exception
    {
        Native.paramsSetDouble(Context().nCtx(), NativeObject(), Context()
                .MkSymbol(name).NativeObject(), value);
    }

    /**
     * Adds a parameter setting.
     **/
    public void Add(String name, Symbol value) throws Z3Exception
    {
        Native.paramsSetSymbol(Context().nCtx(), NativeObject(), Context()
                .MkSymbol(name).NativeObject(), value.NativeObject());
    }

    /**
     * A string representation of the parameter set.
     **/
    public String toString()
    {
        return Native.paramsToString(Context().nCtx(), NativeObject());
    }

    Params(Context ctx) throws Z3Exception
    {
        super(ctx, Native.mkParams(ctx.nCtx()));
    }

    void IncRef(long o) throws Z3Exception
    {
        Context().Params_DRQ().IncAndClear(Context(), o);
        super.IncRef(o);
    }

    void DecRef(long o) throws Z3Exception
    {
        Context().Params_DRQ().Add(o);
        super.DecRef(o);
    }
}
