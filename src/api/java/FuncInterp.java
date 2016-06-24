/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    FuncInterp.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

/**
 * A function interpretation is represented as a finite map and an 'else' value.
 * Each entry in the finite map represents the value of a function given a set
 * of arguments.
 **/
public class FuncInterp extends Z3Object {

    /**
     * An Entry object represents an element in the finite map used to encode a
     * function interpretation.
     **/
    public static class Entry extends Z3Object {

        /**
         * Return the (symbolic) value of this entry.
         *
         * @throws Z3Exception
         * @throws Z3Exception on error
         **/
        public Expr getValue()
        {
            return Expr.create(getContext(),
                    Native.funcEntryGetValue(getContext().nCtx(), getNativeObject()));
        }

        /**
         * The number of arguments of the entry.
         * @throws Z3Exception on error
         **/
        public int getNumArgs()
        {
            return Native.funcEntryGetNumArgs(getContext().nCtx(), getNativeObject());
        }

        /**
         * The arguments of the function entry.
         *
         * @throws Z3Exception
         * @throws Z3Exception on error
         **/
        public Expr[] getArgs()
        {
            int n = getNumArgs();
            Expr[] res = new Expr[n];
            for (int i = 0; i < n; i++)
                res[i] = Expr.create(getContext(), Native.funcEntryGetArg(
                        getContext().nCtx(), getNativeObject(), i));
            return res;
        }

        /**
         * A string representation of the function entry.
         **/
        @Override
        public String toString()
        {
            int n = getNumArgs();
            String res = "[";
            Expr[] args = getArgs();
            for (int i = 0; i < n; i++)
                res += args[i] + ", ";
            return res + getValue() + "]";
        }

        Entry(Context ctx, long obj) {
            super(ctx, obj);
        }

        @Override
        void incRef() {
            Native.funcEntryIncRef(getContext().nCtx(), getNativeObject());
        }

        @Override
        void addToReferenceQueue() {
            getContext().getFuncEntryDRQ().storeReference(getContext(), this);
        }
    }

    /**
     * The number of entries in the function interpretation.
     * @throws Z3Exception on error
     * @return an int
     **/
    public int getNumEntries()
    {
        return Native.funcInterpGetNumEntries(getContext().nCtx(), getNativeObject());
    }

    /**
     * The entries in the function interpretation
     * 
     * @throws Z3Exception
     * @throws Z3Exception on error
     **/
    public Entry[] getEntries()
    {
        int n = getNumEntries();
        Entry[] res = new Entry[n];
        for (int i = 0; i < n; i++)
            res[i] = new Entry(getContext(), Native.funcInterpGetEntry(getContext()
                    .nCtx(), getNativeObject(), i));
        return res;
    }

    /**
     * The (symbolic) `else' value of the function interpretation.
     * 
     * @throws Z3Exception
     * @throws Z3Exception on error
     * @return an Expr
     **/
    public Expr getElse()
    {
        return Expr.create(getContext(),
                Native.funcInterpGetElse(getContext().nCtx(), getNativeObject()));
    }

    /**
     * The arity of the function interpretation
     * @throws Z3Exception on error
     * @return an int
     **/
    public int getArity()
    {
        return Native.funcInterpGetArity(getContext().nCtx(), getNativeObject());
    }

    /**
     * A string representation of the function interpretation.
     **/
    public String toString()
    {
        String res = "";
        res += "[";
        for (Entry e : getEntries())
        {
            int n = e.getNumArgs();
            if (n > 1)
                res += "[";
            Expr[] args = e.getArgs();
            for (int i = 0; i < n; i++)
            {
                if (i != 0)
                    res += ", ";
                res += args[i];
            }
            if (n > 1)
                res += "]";
            res += " -> " + e.getValue() + ", ";
        }
        res += "else -> " + getElse();
        res += "]";
        return res;
    }

    FuncInterp(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    @Override
    void incRef() {
        Native.funcInterpIncRef(getContext().nCtx(), getNativeObject());
    }

    @Override
    void addToReferenceQueue() {
        getContext().getFuncInterpDRQ().storeReference(getContext(), this);
    }
}
