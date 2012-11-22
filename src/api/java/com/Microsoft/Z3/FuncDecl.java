/**
 * This file was automatically generated from FuncDecl.cs 
 **/

package com.Microsoft.Z3;

/* using System; */

    /**
     * Function declarations. 
     **/
    public class FuncDecl extends AST
    {
        /**
         * Comparison operator.
         * @return True if <paramref name="a"/> and <paramref name="b"/> share the same context and are equal, false otherwise.
         **/
         /* Overloaded operators are not translated. */

        /**
         * Comparison operator.
         * @return True if <paramref name="a"/> and <paramref name="b"/> do not share the same context or are not equal, false otherwise.
         **/
         /* Overloaded operators are not translated. */

        /**
         * Object comparison.
         **/
        public boolean Equals(object o)
        {
            FuncDecl casted = o as FuncDecl;
            if (casted == null) return false;
            return this == casted;
        }

        /**
         * A hash code.
         **/
        public int GetHashCode()
        {
            return super.GetHashCode();
        }

        /**
         * A string representations of the function declaration.
         **/
        public String toString()
        {
            return Native.funcDecltoString(Context.nCtx, NativeObject);
        }

        /**
         * Returns a unique identifier for the function declaration.
         **/
        new public Integer Id()  { return Native.getFuncDeclId(Context.nCtx, NativeObject); }

        /**
         * The arity of the function declaration
         **/
        public Integer Arity()  { return Native.getArity(Context.nCtx, NativeObject); }

        /**
         * The size of the domain of the function declaration
         * <seealso cref="Arity"/>
         **/
        public Integer DomainSize()  { return Native.getDomainSize(Context.nCtx, NativeObject); }

        /**
         * The domain of the function declaration
         **/
        public Sort[] Domain() 
            {
                

                var n = DomainSize;

                Sort[] res = new Sort[n];
                for (Integer i = 0; i < n; i++)
                    res[i] = Sort.Create(Context, Native.getDomain(Context.nCtx, NativeObject, i));
                return res;
        }

        /**
         * The range of the function declaration
         **/
        public Sort Range()  {
                
                return Sort.Create(Context, Native.getRange(Context.nCtx, NativeObject)); }

        /**
         * The kind of the function declaration.
         **/
        public Z3_decl_kind DeclKind()  { return (Z3DeclKind)Native.getDeclKind(Context.nCtx, NativeObject); }

        /**
         * The name of the function declaration
         **/
        public Symbol Name()  {
                
                return Symbol.Create(Context, Native.getDeclName(Context.nCtx, NativeObject)); }

        /**
         * The number of parameters of the function declaration
         **/
        public Integer NumParameters()  { return Native.getDeclNumParameters(Context.nCtx, NativeObject); }

        /**
         * The parameters of the function declaration
         **/
        public Parameter[] Parameters() 
            {
                

                Integer num = NumParameters;
                Parameter[] res = new Parameter[num];
                for (Integer i = 0; i < num; i++)
                {
                    Z3ParameterKind k = (Z3ParameterKind)Native.getDeclParameterKind(Context.nCtx, NativeObject, i);
                    switch (k)
                    {
                        case Z3ParameterKind.Z3PARAMETERINT:
                            res[i] = new Parameter(k, Native.getDeclIntParameter(Context.nCtx, NativeObject, i));
                            break;
                        case Z3ParameterKind.Z3PARAMETERDOUBLE:
                            res[i] = new Parameter(k, Native.getDeclDoubleParameter(Context.nCtx, NativeObject, i));
                            break;
                        case Z3ParameterKind.Z3PARAMETERSYMBOL:
                            res[i] = new Parameter(k, Symbol.Create(Context, Native.getDeclSymbolParameter(Context.nCtx, NativeObject, i)));
                            break;
                        case Z3ParameterKind.Z3PARAMETERSORT:
                            res[i] = new Parameter(k, Sort.Create(Context, Native.getDeclSortParameter(Context.nCtx, NativeObject, i)));
                            break;
                        case Z3ParameterKind.Z3PARAMETERAST:
                            res[i] = new Parameter(k, new AST(Context, Native.getDeclAstParameter(Context.nCtx, NativeObject, i)));
                            break;
                        case Z3ParameterKind.Z3PARAMETERFUNCDECL:
                            res[i] = new Parameter(k, new FuncDecl(Context, Native.getDeclFuncDeclParameter(Context.nCtx, NativeObject, i)));
                            break;
                        case Z3ParameterKind.Z3PARAMETERRATIONAL:
                            res[i] = new Parameter(k, Native.getDeclRationalParameter(Context.nCtx, NativeObject, i));
                            break;
                        default:
                            throw new Z3Exception("Unknown function declaration parameter kind encountered");
                }
                return res;
            }
        }

        /**
         * Function declarations can have Parameters associated with them. 
         **/
        public class Parameter
        {
            private Z3ParameterKind kind;
            private int i;
            private double d;
            private Symbol sym;
            private Sort srt;
            private AST ast;
            private FuncDecl fd;
            private String r;

            /**The int value of the parameter.</summary>
         **/
             /* Overloaded operators are not translated. */

            Parameter(Z3ParameterKind k, double d)
            {
                this.kind = k;
                this.d = d;
            }

            Parameter(Z3ParameterKind k, Symbol s)
            {
                this.kind = k;
                this.sym = s;
            }

            Parameter(Z3ParameterKind k, Sort s)
            {
                this.kind = k;
                this.srt = s;
            }

            Parameter(Z3ParameterKind k, AST a)
            {
                this.kind = k;
                this.ast = a;
            }

            Parameter(Z3ParameterKind k, FuncDecl fd)
            {
                this.kind = k;
                this.fd = fd;
            }

            Parameter(Z3ParameterKind k, String r)
            {
                this.kind = k;
                this.r = r;
            }
        }

        FuncDecl(Context ctx, IntPtr obj) { super(ctx, obj); 
             
        }

        FuncDecl(Context ctx, Symbol name, Sort[] domain, Sort range)
            : base(ctx, Native.mkFuncDecl(ctx.nCtx, name.NativeObject,
                                             AST.ArrayLength(domain), AST.ArrayToNative(domain),
                                             range.NativeObject))
            
            
            
        }        

        FuncDecl(Context ctx, String prefix, Sort[] domain, Sort range)
            : base(ctx, Native.mkFreshFuncDecl(ctx.nCtx, prefix,
                                             AST.ArrayLength(domain), AST.ArrayToNative(domain),
                                             range.NativeObject))
            
            
        }

        void CheckNativeObject(IntPtr obj)
        {
            if (Native.getAstKind(Context.nCtx, obj) != (Integer)Z3AstKind.Z3FUNCDECLAST)
                throw new Z3Exception("Underlying object is not a function declaration");
            super.CheckNativeObject(obj);
        }

        /**
         * Create expression that applies function to arguments.
         * <param name="args"></param>
         * @return 
         **/
        public Expr this[params() lic Expr this[params Expr[] args] 
        public Expr this[params()  {
                

                return Apply(args); 
        }

        /**
         * Create expression that applies function to arguments.
         * <param name="args"></param>
         * @return 
         **/
        public Expr Apply(Expr[] args)
        {
            

            Context.CheckContextMatch(args);
            return Expr.Create(Context, this, args);
        }

    }
