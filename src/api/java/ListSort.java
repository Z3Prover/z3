/**
 * This file was automatically generated from ListSort.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * List sorts.
 **/
public class ListSort extends Sort
{
    /**
     * The declaration of the nil function of this list sort.
     * @throws Z3Exception 
     **/
    public FuncDecl getNilDecl() throws Z3Exception
    {
        return new FuncDecl(getContext(), Native.getDatatypeSortConstructor(getContext().nCtx(), getNativeObject(), 0));
    }

    /**
     * The empty list.
     * @throws Z3Exception 
     **/
    public Expr getNil() throws Z3Exception
    {
        return getContext().mkApp(getNilDecl());
    }

    /**
     * The declaration of the isNil function of this list sort.
     * @throws Z3Exception 
     **/
    public FuncDecl getIsNilDecl() throws Z3Exception
    {
        return new FuncDecl(getContext(), Native.getDatatypeSortRecognizer(getContext().nCtx(), getNativeObject(), 0));
    }

    /**
     * The declaration of the cons function of this list sort.
     * @throws Z3Exception 
     **/
    public FuncDecl getConsDecl() throws Z3Exception
    {
        return new FuncDecl(getContext(), Native.getDatatypeSortConstructor(getContext().nCtx(), getNativeObject(), 1));
    }

    /**
     * The declaration of the isCons function of this list sort.
     * @throws Z3Exception 
     * 
     **/
    public FuncDecl getIsConsDecl() throws Z3Exception
    {
        return new FuncDecl(getContext(), Native.getDatatypeSortRecognizer(getContext().nCtx(), getNativeObject(), 1));
    }

    /**
     * The declaration of the head function of this list sort.
     * @throws Z3Exception 
     **/
    public FuncDecl getHeadDecl() throws Z3Exception
    {
        return new FuncDecl(getContext(), Native.getDatatypeSortConstructorAccessor(getContext().nCtx(), getNativeObject(), 1, 0));
    }

    /**
     * The declaration of the tail function of this list sort.
     * @throws Z3Exception 
     **/
    public FuncDecl getTailDecl() throws Z3Exception
    {
        return new FuncDecl(getContext(), Native.getDatatypeSortConstructorAccessor(getContext().nCtx(), getNativeObject(), 1, 1));
    }

    ListSort(Context ctx, Symbol name, Sort elemSort) throws Z3Exception
    {
        super(ctx);

        Native.LongPtr inil = new Native.LongPtr(), iisnil = new Native.LongPtr();
        Native.LongPtr icons = new Native.LongPtr(), iiscons = new Native.LongPtr();
        Native.LongPtr ihead = new Native.LongPtr(), itail = new Native.LongPtr();

        setNativeObject(Native.mkListSort(ctx.nCtx(), name.getNativeObject(),
                elemSort.getNativeObject(), inil, iisnil, icons, iiscons, ihead,
                itail));
    }
};
