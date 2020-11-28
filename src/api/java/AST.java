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
public class AST extends Z3Object implements Comparable<AST>
{
    /**
     * Object comparison.
     * 
     * @param o another AST
     **/
    @Override
    public boolean equals(Object o)
    {
        if (o == this) return true;
        if (!(o instanceof AST)) return false;
        AST casted = (AST) o;

        return
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
    @Override
    public int compareTo(AST other)
    {
        if (other == null) {
            return 1;
        }
        return Integer.compare(getId(), other.getId());
    }

    /**
     * The AST's hash code.
     * 
     * @return A hash code
     **/
    @Override
    public int hashCode()
    {
        return Native.getAstHash(getContext().nCtx(), getNativeObject());
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
        if (getContext() == ctx) {
            return this;
        } else {
            return create(ctx, Native.translate(getContext().nCtx(), getNativeObject(), ctx.nCtx()));
        }
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
    @Override
    public String toString() {
        return Native.astToString(getContext().nCtx(), getNativeObject());
    }

    /**
     * A string representation of the AST in s-expression notation.
     **/
    public String getSExpr()
    {
        return Native.astToString(getContext().nCtx(), getNativeObject());
    }

    AST(Context ctx, long obj) {
        super(ctx, obj);
    }

    @Override
    void incRef() {
        Native.incRef(getContext().nCtx(), getNativeObject());
    }

    @Override
    void addToReferenceQueue() {
        getContext().getASTDRQ().storeReference(getContext(), this);
    }

    static AST create(Context ctx, long obj)
    {
        switch (Z3_ast_kind.fromInt(Native.getAstKind(ctx.nCtx(), obj)))
        {
        case Z3_FUNC_DECL_AST:
            return new FuncDecl<>(ctx, obj);
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
