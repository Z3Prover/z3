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
     **/
    public FuncDecl NilDecl()
    {

        return nilDecl;
    }

    /**
     * The empty list.
     **/
    public Expr Nil()
    {

        return nilConst;
    }

    /**
     * The declaration of the isNil function of this list sort.
     **/
    public FuncDecl IsNilDecl()
    {

        return isNilDecl;
    }

    /**
     * The declaration of the cons function of this list sort.
     **/
    public FuncDecl ConsDecl()
    {

        return consDecl;
    }

    /**
     * The declaration of the isCons function of this list sort.
     * 
     **/
    public FuncDecl IsConsDecl()
    {

        return isConsDecl;
    }

    /**
     * The declaration of the head function of this list sort.
     **/
    public FuncDecl HeadDecl()
    {

        return headDecl;
    }

    /**
     * The declaration of the tail function of this list sort.
     **/
    public FuncDecl TailDecl()
    {

        return tailDecl;
    }

    private FuncDecl nilDecl, isNilDecl, consDecl, isConsDecl, headDecl,
            tailDecl;
    private Expr nilConst;

    ListSort(Context ctx, Symbol name, Sort elemSort) throws Z3Exception
    {
        super(ctx);

        Native.LongPtr inil = new Native.LongPtr(), iisnil = new Native.LongPtr();
        Native.LongPtr icons = new Native.LongPtr(), iiscons = new Native.LongPtr();
        Native.LongPtr ihead = new Native.LongPtr(), itail = new Native.LongPtr();

        setNativeObject(Native.mkListSort(ctx.nCtx(), name.NativeObject(),
                elemSort.NativeObject(), inil, iisnil, icons, iiscons, ihead,
                itail));
        nilDecl = new FuncDecl(ctx, inil.value);
        isNilDecl = new FuncDecl(ctx, iisnil.value);
        consDecl = new FuncDecl(ctx, icons.value);
        isConsDecl = new FuncDecl(ctx, iiscons.value);
        headDecl = new FuncDecl(ctx, ihead.value);
        tailDecl = new FuncDecl(ctx, itail.value);
        nilConst = ctx.MkConst(nilDecl);
    }
};
