/**
 * This file was automatically generated from AST.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

import com.microsoft.z3.enumerations.*;

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

        return this.NativeObject() == casted.NativeObject();
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

        if (Id() < oAST.Id())
            return -1;
        else if (Id() > oAST.Id())
            return +1;
        else
            return 0;
    }

    /**
     * The AST's hash code.
     * 
     * @return A hash code
     **/
    public int GetHashCode() throws Z3Exception
    {
        return (int) Native.getAstHash(Context().nCtx(), NativeObject());
    }

    /**
     * A unique identifier for the AST (unique among all ASTs).
     **/
    public int Id() throws Z3Exception
    {
        return Native.getAstId(Context().nCtx(), NativeObject());
    }

    /**
     * Translates (copies) the AST to the Context <paramref name="ctx"/>. <param
     * name="ctx">A context</param>
     * 
     * @return A copy of the AST which is associated with <paramref name="ctx"/>
     **/
    public AST Translate(Context ctx) throws Z3Exception
    {

        if (Context() == ctx)
            return this;
        else
            return new AST(ctx, Native.translate(Context().nCtx(),
                    NativeObject(), ctx.nCtx()));
    }

    /**
     * The kind of the AST.
     **/
    public Z3_ast_kind ASTKind() throws Z3Exception
    {
        return Z3_ast_kind.fromInt(Native.getAstKind(Context().nCtx(),
                NativeObject()));
    }

    /**
     * Indicates whether the AST is an Expr
     **/
    public boolean IsExpr() throws Z3Exception
    {
        switch (ASTKind())
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
     * Indicates whether the AST is a BoundVariable
     **/
    public boolean IsVar() throws Z3Exception
    {
        return this.ASTKind() == Z3_ast_kind.Z3_VAR_AST;
    }

    /**
     * Indicates whether the AST is a Quantifier
     **/
    public boolean IsQuantifier() throws Z3Exception
    {
        return this.ASTKind() == Z3_ast_kind.Z3_QUANTIFIER_AST;
    }

    /**
     * Indicates whether the AST is a Sort
     **/
    public boolean IsSort() throws Z3Exception
    {
        return this.ASTKind() == Z3_ast_kind.Z3_SORT_AST;
    }

    /**
     * Indicates whether the AST is a FunctionDeclaration
     **/
    public boolean IsFuncDecl() throws Z3Exception
    {
        return this.ASTKind() == Z3_ast_kind.Z3_FUNC_DECL_AST;
    }

    /**
     * A string representation of the AST.
     **/
    public String toString()
    {
        try
        {
            return Native.astToString(Context().nCtx(), NativeObject());
        } catch (Z3Exception e)
        {
            return "Z3Exception: " + e.getMessage();
        }
    }

    /**
     * A string representation of the AST in s-expression notation.
     **/
    public String SExpr() throws Z3Exception
    {
        return Native.astToString(Context().nCtx(), NativeObject());
    }

    AST(Context ctx)
    {
        super(ctx);
    }

    AST(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    void IncRef(long o) throws Z3Exception
    {
        // Console.WriteLine("AST IncRef()");
        if (Context() == null)
            throw new Z3Exception("inc() called on null context");
        if (o == 0)
            throw new Z3Exception("inc() called on null AST");
        Context().AST_DRQ().IncAndClear(Context(), o);
        super.IncRef(o);
    }

    void DecRef(long o) throws Z3Exception
    {
        // Console.WriteLine("AST DecRef()");
        if (Context() == null)
            throw new Z3Exception("dec() called on null context");
        if (o == 0)
            throw new Z3Exception("dec() called on null AST");
        Context().AST_DRQ().Add(o);
        super.DecRef(o);
    }

    static AST Create(Context ctx, long obj) throws Z3Exception
    {
        switch (Z3_ast_kind.fromInt(Native.getAstKind(ctx.nCtx(), obj)))
        {
        case Z3_FUNC_DECL_AST:
            return new FuncDecl(ctx, obj);
        case Z3_QUANTIFIER_AST:
            return new Quantifier(ctx, obj);
        case Z3_SORT_AST:
            return Sort.Create(ctx, obj);
        case Z3_APP_AST:
        case Z3_NUMERAL_AST:
        case Z3_VAR_AST:
            return Expr.Create(ctx, obj);
        default:
            throw new Z3Exception("Unknown AST kind");
        }
    }
}
