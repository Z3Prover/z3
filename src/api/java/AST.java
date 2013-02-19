/**
 * This file was automatically generated from AST.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

import com.microsoft.z3.enumerations.Z3_ast_kind;

/**
 * The abstract syntax tree (AST) class.
 **/
public class AST extends Z3Object
{
    /**
     * Comparison operator. <param name="a">An AST</param> <param name="b">An
     * AST</param>
     * 
     * @return True if <paramref name="a"/> and <paramref name="b"/> are from
     *         the same context and represent the same sort; false otherwise.
     **/
    /* Overloaded operators are not translated. */

    /**
     * Comparison operator. <param name="a">An AST</param> <param name="b">An
     * AST</param>
     * 
     * @return True if <paramref name="a"/> and <paramref name="b"/> are not
     *         from the same context or represent different sorts; false
     *         otherwise.
     **/
    /* Overloaded operators are not translated. */

    /**
     * Object comparison.
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

        return this.getNativeObject() == casted.getNativeObject();
    }

    /**
     * Object Comparison. <param name="other">Another AST</param>
     * 
     * @return Negative if the object should be sorted before <paramref
     *         name="other"/>, positive if after else zero.
     **/
    public int compareTo(Object other) throws Z3Exception
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
     **/
    public int getId() throws Z3Exception
    {
        return Native.getAstId(getContext().nCtx(), getNativeObject());
    }

    /**
     * Translates (copies) the AST to the Context <paramref name="ctx"/>. <param
     * name="ctx">A context</param>
     * 
     * @return A copy of the AST which is associated with <paramref name="ctx"/>
     **/
    public AST translate(Context ctx) throws Z3Exception
    {

        if (getContext() == ctx)
            return this;
        else
            return new AST(ctx, Native.translate(getContext().nCtx(),
                    getNativeObject(), ctx.nCtx()));
    }

    /**
     * The kind of the AST.
     **/
    public Z3_ast_kind getASTKind() throws Z3Exception
    {
        return Z3_ast_kind.fromInt(Native.getAstKind(getContext().nCtx(),
                getNativeObject()));
    }

    /**
     * Indicates whether the AST is an Expr
     **/
    public boolean isExpr() throws Z3Exception
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
     **/
    public boolean isApp() throws Z3Exception
    {
        return this.getASTKind() == Z3_ast_kind.Z3_APP_AST;
    }

    /**
     * Indicates whether the AST is a BoundVariable
     **/
    public boolean isVar() throws Z3Exception
    {
        return this.getASTKind() == Z3_ast_kind.Z3_VAR_AST;
    }

    /**
     * Indicates whether the AST is a Quantifier
     **/
    public boolean isQuantifier() throws Z3Exception
    {
        return this.getASTKind() == Z3_ast_kind.Z3_QUANTIFIER_AST;
    }

    /**
     * Indicates whether the AST is a Sort
     **/
    public boolean isSort() throws Z3Exception
    {
        return this.getASTKind() == Z3_ast_kind.Z3_SORT_AST;
    }

    /**
     * Indicates whether the AST is a FunctionDeclaration
     **/
    public boolean isFuncDecl() throws Z3Exception
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
    public String getSExpr() throws Z3Exception
    {
        return Native.astToString(getContext().nCtx(), getNativeObject());
    }

    AST(Context ctx)
    {
        super(ctx);
    }

    AST(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    void incRef(long o) throws Z3Exception
    {
        // Console.WriteLine("AST IncRef()");
        if (getContext() == null)
            throw new Z3Exception("inc() called on null context");
        if (o == 0)
            throw new Z3Exception("inc() called on null AST");
        getContext().ast_DRQ().incAndClear(getContext(), o);
        super.incRef(o);
    }

    void decRef(long o) throws Z3Exception
    {
        // Console.WriteLine("AST DecRef()");
        if (getContext() == null)
            throw new Z3Exception("dec() called on null context");
        if (o == 0)
            throw new Z3Exception("dec() called on null AST");
        getContext().ast_DRQ().add(o);
        super.decRef(o);
    }

    static AST create(Context ctx, long obj) throws Z3Exception
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
