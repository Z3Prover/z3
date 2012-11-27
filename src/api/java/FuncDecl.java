/**
 * This file was automatically generated from FuncDecl.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.Microsoft.Z3;

import com.Microsoft.Z3.Enumerations.*;

/**
 * Function declarations.
 **/
public class FuncDecl extends AST
{
	/**
	 * Comparison operator.
	 * 
	 * @return True if <paramref name="a"/> and <paramref name="b"/> share the
	 *         same context and are equal, false otherwise.
	 **/
	/* Overloaded operators are not translated. */

	/**
	 * Comparison operator.
	 * 
	 * @return True if <paramref name="a"/> and <paramref name="b"/> do not
	 *         share the same context or are not equal, false otherwise.
	 **/
	/* Overloaded operators are not translated. */

	/**
	 * Object comparison.
	 **/
	public boolean Equals(Object o)
	{
		FuncDecl casted = (FuncDecl) o;
		if (casted == null)
			return false;
		return this == casted;
	}

	/**
	 * A hash code.
	 **/
	public int GetHashCode() throws Z3Exception
	{
		return super.GetHashCode();
	}

	/**
	 * A string representations of the function declaration.
	 **/
	public String toString()
	{
		return Native.funcDeclToString(Context().nCtx(), NativeObject());
	}

	/**
	 * Returns a unique identifier for the function declaration.
	 **/
	public int Id() throws Z3Exception
	{
		return Native.getFuncDeclId(Context().nCtx(), NativeObject());
	}

	/**
	 * The arity of the function declaration
	 **/
	public int Arity() throws Z3Exception
	{
		return Native.getArity(Context().nCtx(), NativeObject());
	}

	/**
	 * The size of the domain of the function declaration <seealso
	 * cref="Arity"/>
	 **/
	public int DomainSize()
	{
		return Native.getDomainSize(Context().nCtx(), NativeObject());
	}

	/**
	 * The domain of the function declaration
	 **/
	public Sort[] Domain() throws Z3Exception
	{

		int n = DomainSize();

		Sort[] res = new Sort[n];
		for (int i = 0; i < n; i++)
			res[i] = Sort.Create(Context(),
					Native.getDomain(Context().nCtx(), NativeObject(), i));
		return res;
	}

	/**
	 * The range of the function declaration
	 **/
	public Sort Range() throws Z3Exception
	{

		return Sort.Create(Context(),
				Native.getRange(Context().nCtx(), NativeObject()));
	}

	/**
	 * The kind of the function declaration.
	 **/
	public Z3_decl_kind DeclKind() throws Z3Exception
	{
		return Z3_decl_kind.fromInt(Native.getDeclKind(Context().nCtx(),
				NativeObject()));
	}

	/**
	 * The name of the function declaration
	 **/
	public Symbol Name() throws Z3Exception
	{

		return Symbol.Create(Context(),
				Native.getDeclName(Context().nCtx(), NativeObject()));
	}

	/**
	 * The number of parameters of the function declaration
	 **/
	public int NumParameters() throws Z3Exception
	{
		return Native.getDeclNumParameters(Context().nCtx(), NativeObject());
	}

	/**
	 * The parameters of the function declaration
	 **/
	public Parameter[] Parameters() throws Z3Exception
	{

		int num = NumParameters();
		Parameter[] res = new Parameter[num];
		for (int i = 0; i < num; i++)
		{
			Z3_parameter_kind k = Z3_parameter_kind.fromInt(Native
					.getDeclParameterKind(Context().nCtx(), NativeObject(), i));
			switch (k)
			{
			case Z3_PARAMETER_INT:
				res[i] = new Parameter(k, Native.getDeclIntParameter(Context()
						.nCtx(), NativeObject(), i));
				break;
			case Z3_PARAMETER_DOUBLE:
				res[i] = new Parameter(k, Native.getDeclDoubleParameter(
						Context().nCtx(), NativeObject(), i));
				break;
			case Z3_PARAMETER_SYMBOL:
				res[i] = new Parameter(k, Symbol.Create(Context(), Native
						.getDeclSymbolParameter(Context().nCtx(),
								NativeObject(), i)));
				break;
			case Z3_PARAMETER_SORT:
				res[i] = new Parameter(k, Sort.Create(Context(), Native
						.getDeclSortParameter(Context().nCtx(), NativeObject(),
								i)));
				break;
			case Z3_PARAMETER_AST:
				res[i] = new Parameter(k, new AST(Context(),
						Native.getDeclAstParameter(Context().nCtx(),
								NativeObject(), i)));
				break;
			case Z3_PARAMETER_FUNC_DECL:
				res[i] = new Parameter(k, new FuncDecl(Context(),
						Native.getDeclFuncDeclParameter(Context().nCtx(),
								NativeObject(), i)));
				break;
			case Z3_PARAMETER_RATIONAL:
				res[i] = new Parameter(k, Native.getDeclRationalParameter(
						Context().nCtx(), NativeObject(), i));
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
		 * The int value of the parameter.</summary>
		 **/
		public int Int() throws Z3Exception
		{
			if (ParameterKind() != Z3_parameter_kind.Z3_PARAMETER_INT)
				throw new Z3Exception("parameter is not an int");
			return i;
		}

		/**
		 * The double value of the parameter.</summary>
		 **/
		public double Double() throws Z3Exception
		{
			if (ParameterKind() != Z3_parameter_kind.Z3_PARAMETER_DOUBLE)
				throw new Z3Exception("parameter is not a double ");
			return d;
		}

		/**
		 * The Symbol value of the parameter.</summary>
		 **/
		public Symbol Symbol() throws Z3Exception
		{
			if (ParameterKind() != Z3_parameter_kind.Z3_PARAMETER_SYMBOL)
				throw new Z3Exception("parameter is not a Symbol");
			return sym;
		}

		/**
		 * The Sort value of the parameter.</summary>
		 **/
		public Sort Sort() throws Z3Exception
		{
			if (ParameterKind() != Z3_parameter_kind.Z3_PARAMETER_SORT)
				throw new Z3Exception("parameter is not a Sort");
			return srt;
		}

		/**
		 * The AST value of the parameter.</summary>
		 **/
		public AST AST() throws Z3Exception
		{
			if (ParameterKind() != Z3_parameter_kind.Z3_PARAMETER_AST)
				throw new Z3Exception("parameter is not an AST");
			return ast;
		}

		/**
		 * The FunctionDeclaration value of the parameter.</summary>
		 **/
		public FuncDecl FuncDecl() throws Z3Exception
		{
			if (ParameterKind() != Z3_parameter_kind.Z3_PARAMETER_FUNC_DECL)
				throw new Z3Exception("parameter is not a function declaration");
			return fd;
		}

		/**
		 * The rational string value of the parameter.</summary>
		 **/
		public String Rational() throws Z3Exception
		{
			if (ParameterKind() != Z3_parameter_kind.Z3_PARAMETER_RATIONAL)
				throw new Z3Exception("parameter is not a rational String");
			return r;
		}

		/**
		 * The kind of the parameter.
		 **/
		public Z3_parameter_kind ParameterKind() throws Z3Exception
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

	FuncDecl(Context ctx, long obj) throws Z3Exception
	{
		super(ctx, obj);

	}

	FuncDecl(Context ctx, Symbol name, Sort[] domain, Sort range)
			throws Z3Exception
	{
		super(ctx, Native.mkFuncDecl(ctx.nCtx(), name.NativeObject(),
				AST.ArrayLength(domain), AST.ArrayToNative(domain),
				range.NativeObject()));

	}

	FuncDecl(Context ctx, String prefix, Sort[] domain, Sort range)
			throws Z3Exception
	{
		super(ctx, Native.mkFreshFuncDecl(ctx.nCtx(), prefix,
				AST.ArrayLength(domain), AST.ArrayToNative(domain),
				range.NativeObject()));

	}

	void CheckNativeObject(long obj) throws Z3Exception
	{
		if (Native.getAstKind(Context().nCtx(), obj) != Z3_ast_kind.Z3_FUNC_DECL_AST
				.toInt())
			throw new Z3Exception(
					"Underlying object is not a function declaration");
		super.CheckNativeObject(obj);
	}

	/**
	 * Create expression that applies function to arguments. <param
	 * name="args"></param>
	 * 
	 * @return
	 **/
	/* operator this[] not translated */

	/**
	 * Create expression that applies function to arguments. <param
	 * name="args"></param>
	 * 
	 * @return
	 **/
	public Expr Apply(Expr[] args) throws Z3Exception
	{

		Context().CheckContextMatch(args);
		return Expr.Create(Context(), this, args);
	}

}
