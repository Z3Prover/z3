/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    AST.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

import com.microsoft.z3.enumerations.Z3_ast_kind;

/**
 * The abstract syntax tree (AST) class.
 **/
public class AST extends Z3Object implements Comparable
{
    /**
     * Object comparison.
     * 
     * @param o another AST
     **/    
    public boolean equals(Object o)
    {
        AST casted = null;

        try
        {
            casted = AST.class.cast(o);
        } catch (ClassCastException e)
        {
            return false;
        }

        return  (this == casted) ||
                (this != null) &&
                (casted != null) &&
                (getContext().nCtx() == casted.getContext().nCtx()) &&
                (Native.isEqAst(getContext().nCtx(), getNativeObject(), casted.getNativeObject()));
    }

    /**
     * Object Comparison. 
     * @param other Another AST
     * 
     * @return Negative if the object should be sorted before {@code other}, 
     * positive if after else zero.
     * @throws Z3Exception on error
     **/
    public int compareTo(Object other)
    {
        if (other == null)
            return 1;

        AST oAST = null;
        try
        {
            oAST = AST.class.cast(other);
        } catch (ClassCastException e)
        {
            return 1;
        }

        if (getId() < oAST.getId())
            return -1;
        else if (getId() > oAST.getId())
            return +1;
        else
            return 0;
    }

    /**
     * The AST's hash code.
     * 
     * @return A hash code
     **/
    public int hashCode()
    {
        int r = 0;
        try {
            Native.getAstHash(getContext().nCtx(), getNativeObject());
        }
        catch (Z3Exception ex) {}
        return r;
    }

    /**
     * A unique identifier for the AST (unique among all ASTs).
     * @throws Z3Exception on error
     **/
    public int getId()
    {
        return Native.getAstId(getContext().nCtx(), getNativeObject());
    }

    /**
     * Translates (copies) the AST to the Context {@code ctx}. 
     * @param ctx A context
     * 
     * @return A copy of the AST which is associated with {@code ctx}
     * @throws Z3Exception on error
     **/
    public AST translate(Context ctx)
    {

        if (getContext() == ctx)
            return this;
        else
            return new AST(ctx, Native.translate(getContext().nCtx(),
                    getNativeObject(), ctx.nCtx()));
    }

    /**
     * The kind of the AST.
     * @throws Z3Exception on error
     **/
    public Z3_ast_kind getASTKind()
    {
        return Z3_ast_kind.fromInt(Native.getAstKind(getContext().nCtx(),
                getNativeObject()));
    }

    /**
     * Indicates whether the AST is an Expr
     * @throws Z3Exception on error
     * @throws Z3Exception on error
     **/
    public boolean isExpr()
    {
        switch (getASTKind())
        {
        case Z3_APP_AST:
        case Z3_NUMERAL_AST:
        case Z3_QUANTIFIER_AST:
        case Z3_VAR_AST:
            return true;
        default:
            return false;
        }
    }

    /**
     * Indicates whether the AST is an application
     * @return a boolean
     * @throws Z3Exception on error
     **/
    public boolean isApp()
    {
        return this.getASTKind() == Z3_ast_kind.Z3_APP_AST;
    }

    /**
     * Indicates whether the AST is a BoundVariable.
     * @return a boolean
     * @throws Z3Exception on error
     **/
    public boolean isVar()
    {
        return this.getASTKind() == Z3_ast_kind.Z3_VAR_AST;
    }

    /**
     * Indicates whether the AST is a Quantifier
     * @return a boolean
     * @throws Z3Exception on error
     **/
    public boolean isQuantifier()
    {
        return this.getASTKind() == Z3_ast_kind.Z3_QUANTIFIER_AST;
    }

    /**
     * Indicates whether the AST is a Sort
     **/
    public boolean isSort()
    {
        return this.getASTKind() == Z3_ast_kind.Z3_SORT_AST;
    }

    /**
     * Indicates whether the AST is a FunctionDeclaration
     **/
    public boolean isFuncDecl()
    {
        return this.getASTKind() == Z3_ast_kind.Z3_FUNC_DECL_AST;
    }

    /**
     * A string representation of the AST.
     **/
    public String toString()
    {
        try
        {
            return Native.astToString(getContext().nCtx(), getNativeObject());
        } catch (Z3Exception e)
        {
            return "Z3Exception: " + e.getMessage();
        }
    }

    /**
     * A string representation of the AST in s-expression notation.
     **/
    public String getSExpr()
    {
        return Native.astToString(getContext().nCtx(), getNativeObject());
    }

    AST(Context ctx)
    {
        super(ctx);
    }

    AST(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    void incRef(long o)
    {
        // Console.WriteLine("AST IncRef()");
        if (getContext() == null || o == 0)
            return;
        getContext().getASTDRQ().incAndClear(getContext(), o);
        super.incRef(o);
    }

    void decRef(long o)
    {
        // Console.WriteLine("AST DecRef()");
        if (getContext() == null || o == 0)
            return;
        getContext().getASTDRQ().add(o);
        super.decRef(o);
    }

    static AST create(Context ctx, long obj)
    {
        switch (Z3_ast_kind.fromInt(Native.getAstKind(ctx.nCtx(), obj)))
        {
        case Z3_FUNC_DECL_AST:
            return new FuncDecl(ctx, obj);
        case Z3_QUANTIFIER_AST:
            return new Quantifier(ctx, obj);
        case Z3_SORT_AST:
            return Sort.create(ctx, obj);
        case Z3_APP_AST:
        case Z3_NUMERAL_AST:
        case Z3_VAR_AST:
            return Expr.create(ctx, obj);
        default:
            throw new Z3Exception("Unknown AST kind");
        }
    }
}
