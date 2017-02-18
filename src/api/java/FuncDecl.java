/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    FuncDecl.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

import com.microsoft.z3.enumerations.Z3_ast_kind;
import com.microsoft.z3.enumerations.Z3_decl_kind;
import com.microsoft.z3.enumerations.Z3_parameter_kind;

/**
 * Function declarations.
 **/
public class FuncDecl extends AST
{
    /**
     * Object comparison.
     **/
    @Override
    public boolean equals(Object o)
    {
        if (o == this) return true;
        if (!(o instanceof FuncDecl)) return false;
        FuncDecl other = (FuncDecl) o;

        return
            (getContext().nCtx() == other.getContext().nCtx()) &&
            (Native.isEqFuncDecl(
                getContext().nCtx(),
                getNativeObject(),
                other.getNativeObject()));
    }

    @Override
    public String toString()
    {
        return Native.funcDeclToString(getContext().nCtx(), getNativeObject());
    }

    /**
     * Returns a unique identifier for the function declaration.
     **/
    @Override
    public int getId()
    {
        return Native.getFuncDeclId(getContext().nCtx(), getNativeObject());
    }

    /**
     * The arity of the function declaration
     **/
    public int getArity()
    {
        return Native.getArity(getContext().nCtx(), getNativeObject());
    }

    /**
     * The size of the domain of the function declaration 
     * @see #getArity
     **/
    public int getDomainSize()
    {
        return Native.getDomainSize(getContext().nCtx(), getNativeObject());
    }

    /**
     * The domain of the function declaration
     **/
    public Sort[] getDomain()
    {

        int n = getDomainSize();

        Sort[] res = new Sort[n];
        for (int i = 0; i < n; i++)
            res[i] = Sort.create(getContext(),
                    Native.getDomain(getContext().nCtx(), getNativeObject(), i));
        return res;
    }

    /**
     * The range of the function declaration
     **/
    public Sort getRange()
    {

        return Sort.create(getContext(),
                Native.getRange(getContext().nCtx(), getNativeObject()));
    }

    /**
     * The kind of the function declaration.
     **/
    public Z3_decl_kind getDeclKind()
    {
        return Z3_decl_kind.fromInt(Native.getDeclKind(getContext().nCtx(),
                getNativeObject()));
    }

    /**
     * The name of the function declaration
     **/
    public Symbol getName()
    {

        return Symbol.create(getContext(),
                Native.getDeclName(getContext().nCtx(), getNativeObject()));
    }

    /**
     * The number of parameters of the function declaration
     **/
    public int getNumParameters()
    {
        return Native.getDeclNumParameters(getContext().nCtx(), getNativeObject());
    }

    /**
     * The parameters of the function declaration
     **/
    public Parameter[] getParameters()
    {

        int num = getNumParameters();
        Parameter[] res = new Parameter[num];
        for (int i = 0; i < num; i++)
        {
            Z3_parameter_kind k = Z3_parameter_kind.fromInt(Native
                    .getDeclParameterKind(getContext().nCtx(), getNativeObject(), i));
            switch (k)
            {
            case Z3_PARAMETER_INT:
                res[i] = new Parameter(k, Native.getDeclIntParameter(getContext()
                        .nCtx(), getNativeObject(), i));
                break;
            case Z3_PARAMETER_DOUBLE:
                res[i] = new Parameter(k, Native.getDeclDoubleParameter(
                        getContext().nCtx(), getNativeObject(), i));
                break;
            case Z3_PARAMETER_SYMBOL:
                res[i] = new Parameter(k, Symbol.create(getContext(), Native
                        .getDeclSymbolParameter(getContext().nCtx(),
                                getNativeObject(), i)));
                break;
            case Z3_PARAMETER_SORT:
                res[i] = new Parameter(k, Sort.create(getContext(), Native
                        .getDeclSortParameter(getContext().nCtx(), getNativeObject(),
                                i)));
                break;
            case Z3_PARAMETER_AST:
                res[i] = new Parameter(k, new AST(getContext(),
                        Native.getDeclAstParameter(getContext().nCtx(),
                                getNativeObject(), i)));
                break;
            case Z3_PARAMETER_FUNC_DECL:
                res[i] = new Parameter(k, new FuncDecl(getContext(),
                        Native.getDeclFuncDeclParameter(getContext().nCtx(),
                                getNativeObject(), i)));
                break;
            case Z3_PARAMETER_RATIONAL:
                res[i] = new Parameter(k, Native.getDeclRationalParameter(
                        getContext().nCtx(), getNativeObject(), i));
                break;
            default:
                throw new Z3Exception(
                        "Unknown function declaration parameter kind encountered");
            }
        }
        return res;
    }

    /**
     * Function declarations can have Parameters associated with them.
     **/
    public class Parameter
    {
        private Z3_parameter_kind kind;
        private int i;
        private double d;
        private Symbol sym;
        private Sort srt;
        private AST ast;
        private FuncDecl fd;
        private String r;

        /**
         * The int value of the parameter.
         **/
        public int getInt()
        {
            if (getParameterKind() != Z3_parameter_kind.Z3_PARAMETER_INT)
                throw new Z3Exception("parameter is not an int");
            return i;
        }

        /**
         * The double value of the parameter.
         **/
        public double getDouble()
        {
            if (getParameterKind() != Z3_parameter_kind.Z3_PARAMETER_DOUBLE)
                throw new Z3Exception("parameter is not a double ");
            return d;
        }

        /**
         * The Symbol value of the parameter.
         **/
        public Symbol getSymbol()
        {
            if (getParameterKind() != Z3_parameter_kind.Z3_PARAMETER_SYMBOL)
                throw new Z3Exception("parameter is not a Symbol");
            return sym;
        }

        /**
         * The Sort value of the parameter.
         **/
        public Sort getSort()
        {
            if (getParameterKind() != Z3_parameter_kind.Z3_PARAMETER_SORT)
                throw new Z3Exception("parameter is not a Sort");
            return srt;
        }

        /**
         * The AST value of the parameter.
         **/
        public AST getAST()
        {
            if (getParameterKind() != Z3_parameter_kind.Z3_PARAMETER_AST)
                throw new Z3Exception("parameter is not an AST");
            return ast;
        }

        /**
         * The FunctionDeclaration value of the parameter.
         **/
        public FuncDecl getFuncDecl()
        {
            if (getParameterKind() != Z3_parameter_kind.Z3_PARAMETER_FUNC_DECL)
                throw new Z3Exception("parameter is not a function declaration");
            return fd;
        }

        /**
         * The rational string value of the parameter.
         **/
        public String getRational()
        {
            if (getParameterKind() != Z3_parameter_kind.Z3_PARAMETER_RATIONAL)
                throw new Z3Exception("parameter is not a rational String");
            return r;
        }

        /**
         * The kind of the parameter.
         **/
        public Z3_parameter_kind getParameterKind()
        {
            return kind;
        }

        Parameter(Z3_parameter_kind k, int i)
        {
            this.kind = k;
            this.i = i;
        }

        Parameter(Z3_parameter_kind k, double d)
        {
            this.kind = k;
            this.d = d;
        }

        Parameter(Z3_parameter_kind k, Symbol s)
        {
            this.kind = k;
            this.sym = s;
        }

        Parameter(Z3_parameter_kind k, Sort s)
        {
            this.kind = k;
            this.srt = s;
        }

        Parameter(Z3_parameter_kind k, AST a)
        {
            this.kind = k;
            this.ast = a;
        }

        Parameter(Z3_parameter_kind k, FuncDecl fd)
        {
            this.kind = k;
            this.fd = fd;
        }

        Parameter(Z3_parameter_kind k, String r)
        {
            this.kind = k;
            this.r = r;
        }
    }

    FuncDecl(Context ctx, long obj)
    {
        super(ctx, obj);

    }

    FuncDecl(Context ctx, Symbol name, Sort[] domain, Sort range)
           
    {
        super(ctx, Native.mkFuncDecl(ctx.nCtx(), name.getNativeObject(),
                AST.arrayLength(domain), AST.arrayToNative(domain),
                range.getNativeObject()));

    }

    FuncDecl(Context ctx, String prefix, Sort[] domain, Sort range)
           
    {
        super(ctx, Native.mkFreshFuncDecl(ctx.nCtx(), prefix,
                AST.arrayLength(domain), AST.arrayToNative(domain),
                range.getNativeObject()));

    }

    void checkNativeObject(long obj)
    {
        if (Native.getAstKind(getContext().nCtx(), obj) != Z3_ast_kind.Z3_FUNC_DECL_AST
                .toInt())
            throw new Z3Exception(
                    "Underlying object is not a function declaration");
        super.checkNativeObject(obj);
    }

    /**
     * Create expression that applies function to arguments. 
     **/
    public Expr apply(Expr ... args)
    {
        getContext().checkContextMatch(args);
        return Expr.create(getContext(), this, args);
    }
}
