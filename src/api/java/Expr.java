/**
 * This file was automatically generated from Expr.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

import com.microsoft.z3.enumerations.Z3_ast_kind;
import com.microsoft.z3.enumerations.Z3_decl_kind;
import com.microsoft.z3.enumerations.Z3_lbool;
import com.microsoft.z3.enumerations.Z3_sort_kind;

/* using System; */

/**
 * Expressions are terms.
 **/
public class Expr extends AST
{
	/**
	 * Returns a simplified version of the expression
	 **/
	public Expr simplify() throws Z3Exception
	{
	    return simplify(null);
	}

	/**
	 * Returns a simplified version of the expression 
	 * A set of
	 * parameters <param name="p" /> to configure the simplifier 
	 * <seealso cref="Context.SimplifyHelp"/>
	 **/
	public Expr simplify(Params p) throws Z3Exception
	{

		if (p == null)
			return Expr.create(getContext(),
					Native.simplify(getContext().nCtx(), getNativeObject()));
		else
			return Expr.create(
					getContext(),
					Native.simplifyEx(getContext().nCtx(), getNativeObject(),
							p.getNativeObject()));
	}

	/**
	 * The function declaration of the function that is applied in this
	 * expression.
	 **/
	public FuncDecl getFuncDecl() throws Z3Exception
	{
		return new FuncDecl(getContext(), Native.getAppDecl(getContext().nCtx(),
				getNativeObject()));
	}

	/**
	 * Indicates whether the expression is the true or false expression or
	 * something else (Z3_L_UNDEF).
	 **/
	public Z3_lbool getBoolValue() throws Z3Exception
	{
		return Z3_lbool.fromInt(Native.getBoolValue(getContext().nCtx(),
				getNativeObject()));
	}

	/**
	 * The number of arguments of the expression.
	 **/
	public int getNumArgs() throws Z3Exception
	{
		return Native.getAppNumArgs(getContext().nCtx(), getNativeObject());
	}

	/**
	 * The arguments of the expression.
	 **/
	public Expr[] getArgs() throws Z3Exception
	{
		int n = getNumArgs();
		Expr[] res = new Expr[n];
		for (int i = 0; i < n; i++)
			res[i] = Expr.create(getContext(),
					Native.getAppArg(getContext().nCtx(), getNativeObject(), i));
		return res;
	}

	/**
	 * Update the arguments of the expression using the arguments <paramref
	 * name="args"/> The number of new arguments should coincide with the
	 * current number of arguments.
	 **/
	public void update(Expr[] args) throws Z3Exception
	{
		getContext().checkContextMatch(args);
		if (args.length != getNumArgs())
			throw new Z3Exception("Number of arguments does not match");
		setNativeObject(Native.updateTerm(getContext().nCtx(), getNativeObject(),
				(int) args.length, Expr.arrayToNative(args)));
	}

	/**
	 * Substitute every occurrence of <code>from[i]</code> in the expression
	 * with <code>to[i]</code>, for <code>i</code> smaller than
	 * <code>num_exprs</code>. <remarks> The result is the new expression. The
	 * arrays <code>from</code> and <code>to</code> must have size
	 * <code>num_exprs</code>. For every <code>i</code> smaller than
	 * <code>num_exprs</code>, we must have that sort of <code>from[i]</code>
	 * must be equal to sort of <code>to[i]</code>. </remarks>
	 **/
	public Expr substitute(Expr[] from, Expr[] to) throws Z3Exception
	{
		getContext().checkContextMatch(from);
		getContext().checkContextMatch(to);
		if (from.length != to.length)
			throw new Z3Exception("Argument sizes do not match");
		return Expr.create(getContext(), Native.substitute(getContext().nCtx(),
				getNativeObject(), (int) from.length, Expr.arrayToNative(from),
				Expr.arrayToNative(to)));
	}

	/**
	 * Substitute every occurrence of <code>from</code> in the expression with
	 * <code>to</code>. <seealso cref="Substitute(Expr[],Expr[])"/>
	 **/
	public Expr substitute(Expr from, Expr to) throws Z3Exception
	{

		return substitute(new Expr[] { from }, new Expr[] { to });
	}

	/**
	 * Substitute the free variables in the expression with the expressions in
	 * <paramref name="to"/> <remarks> For every <code>i</code> smaller than
	 * <code>num_exprs</code>, the variable with de-Bruijn index <code>i</code>
	 * is replaced with term <code>to[i]</code>. </remarks>
	 **/
	public Expr substituteVars(Expr[] to) throws Z3Exception
	{

		getContext().checkContextMatch(to);
		return Expr.create(getContext(), Native.substituteVars(getContext().nCtx(),
				getNativeObject(), (int) to.length, Expr.arrayToNative(to)));
	}

	/**
	 * Translates (copies) the term to the Context <paramref name="ctx"/>.
	 * <param name="ctx">A context</param>
	 * 
	 * @return A copy of the term which is associated with <paramref
	 *         name="ctx"/>
	 **/
	public Expr translate(Context ctx) throws Z3Exception
	{

		if (getContext() == ctx)
			return this;
		else
			return Expr.create(
					ctx,
					Native.translate(getContext().nCtx(), getNativeObject(),
							ctx.nCtx()));
	}

	/**
	 * Returns a string representation of the expression.
	 **/
	public String toString()
	{
		return super.toString();
	}

	/**
	 * Indicates whether the term is a numeral
	 **/
	public boolean isNumeral() throws Z3Exception
	{
		return Native.isNumeralAst(getContext().nCtx(), getNativeObject());
	}

	/**
	 * Indicates whether the term is well-sorted.
	 * 
	 * @return True if the term is well-sorted, false otherwise.
	 **/
	public boolean isWellSorted() throws Z3Exception
	{
		return Native.isWellSorted(getContext().nCtx(), getNativeObject());
	}

	/**
	 * The Sort of the term.
	 **/
	public Sort getSort() throws Z3Exception
	{
		return Sort.create(getContext(),
				Native.getSort(getContext().nCtx(), getNativeObject()));
	}

	/**
	 * Indicates whether the term represents a constant.
	 **/
	public boolean isConst() throws Z3Exception
	{
		return isApp() && getNumArgs() == 0 && getFuncDecl().getDomainSize() == 0;
	}

	/**
	 * Indicates whether the term is an integer numeral.
	 **/
	public boolean isIntNum() throws Z3Exception
	{
		return isNumeral() && isInt();
	}

	/**
	 * Indicates whether the term is a real numeral.
	 **/
	public boolean isRatNum() throws Z3Exception
	{
		return isNumeral() && isReal();
	}

	/**
	 * Indicates whether the term is an algebraic number
	 **/
	public boolean isAlgebraicNumber() throws Z3Exception
	{
		return Native.isAlgebraicNumber(getContext().nCtx(), getNativeObject());
	}

	/**
	 * Indicates whether the term has Boolean sort.
	 **/
	public boolean isBool() throws Z3Exception
	{
		return (isExpr() && Native.isEqSort(getContext().nCtx(),
				Native.mkBoolSort(getContext().nCtx()),
				Native.getSort(getContext().nCtx(), getNativeObject())));
	}

	/**
	 * Indicates whether the term is the constant true.
	 **/
	public boolean isTrue() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_TRUE;
	}

	/**
	 * Indicates whether the term is the constant false.
	 **/
	public boolean isFalse() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_FALSE;
	}

	/**
	 * Indicates whether the term is an equality predicate.
	 **/
	public boolean isEq() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_EQ;
	}

	/**
	 * Indicates whether the term is an n-ary distinct predicate (every argument
	 * is mutually distinct).
	 **/
	public boolean isDistinct() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_DISTINCT;
	}

	/**
	 * Indicates whether the term is a ternary if-then-else term
	 **/
	public boolean isITE() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_ITE;
	}

	/**
	 * Indicates whether the term is an n-ary conjunction
	 **/
	public boolean isAnd() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_AND;
	}

	/**
	 * Indicates whether the term is an n-ary disjunction
	 **/
	public boolean isOr() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_OR;
	}

	/**
	 * Indicates whether the term is an if-and-only-if (Boolean equivalence,
	 * binary)
	 **/
	public boolean isIff() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_IFF;
	}

	/**
	 * Indicates whether the term is an exclusive or
	 **/
	public boolean isXor() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_XOR;
	}

	/**
	 * Indicates whether the term is a negation
	 **/
	public boolean isNot() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_NOT;
	}

	/**
	 * Indicates whether the term is an implication
	 **/
	public boolean isImplies() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_IMPLIES;
	}

	/**
	 * Indicates whether the term is of integer sort.
	 **/
	public boolean isInt() throws Z3Exception
	{
		return (Native.isNumeralAst(getContext().nCtx(), getNativeObject()) && Native
				.getSortKind(getContext().nCtx(),
						Native.getSort(getContext().nCtx(), getNativeObject())) == Z3_sort_kind.Z3_INT_SORT
				.toInt());
	}

	/**
	 * Indicates whether the term is of sort real.
	 **/
	public boolean isReal() throws Z3Exception
	{
		return Native.getSortKind(getContext().nCtx(),
				Native.getSort(getContext().nCtx(), getNativeObject())) == Z3_sort_kind.Z3_REAL_SORT
				.toInt();
	}

	/**
	 * Indicates whether the term is an arithmetic numeral.
	 **/
	public boolean isArithmeticNumeral() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_ANUM;
	}

	/**
	 * Indicates whether the term is a less-than-or-equal
	 **/
	public boolean isLE() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_LE;
	}

	/**
	 * Indicates whether the term is a greater-than-or-equal
	 **/
	public boolean isGE() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_GE;
	}

	/**
	 * Indicates whether the term is a less-than
	 **/
	public boolean isLT() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_LT;
	}

	/**
	 * Indicates whether the term is a greater-than
	 **/
	public boolean isGT() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_GT;
	}

	/**
	 * Indicates whether the term is addition (binary)
	 **/
	public boolean isAdd() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_ADD;
	}

	/**
	 * Indicates whether the term is subtraction (binary)
	 **/
	public boolean isSub() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SUB;
	}

	/**
	 * Indicates whether the term is a unary minus
	 **/
	public boolean isUMinus() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_UMINUS;
	}

	/**
	 * Indicates whether the term is multiplication (binary)
	 **/
	public boolean isMul() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_MUL;
	}

	/**
	 * Indicates whether the term is division (binary)
	 **/
	public boolean isDiv() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_DIV;
	}

	/**
	 * Indicates whether the term is integer division (binary)
	 **/
	public boolean isIDiv() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_IDIV;
	}

	/**
	 * Indicates whether the term is remainder (binary)
	 **/
	public boolean isRemainder() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_REM;
	}

	/**
	 * Indicates whether the term is modulus (binary)
	 **/
	public boolean isModulus() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_MOD;
	}

	/**
	 * Indicates whether the term is a coercion of integer to real (unary)
	 **/
	public boolean isIntToReal() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_TO_REAL;
	}

	/**
	 * Indicates whether the term is a coercion of real to integer (unary)
	 **/
	public boolean isRealToInt() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_TO_INT;
	}

	/**
	 * Indicates whether the term is a check that tests whether a real is
	 * integral (unary)
	 **/
	public boolean isRealIsInt() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_IS_INT;
	}

	/**
	 * Indicates whether the term is of an array sort.
	 **/
	public boolean isArray() throws Z3Exception
	{
		return (Native.isApp(getContext().nCtx(), getNativeObject()) && Z3_sort_kind
				.fromInt(Native.getSortKind(getContext().nCtx(),
						Native.getSort(getContext().nCtx(), getNativeObject()))) == Z3_sort_kind.Z3_ARRAY_SORT);
	}

	/**
	 * Indicates whether the term is an array store. <remarks>It satisfies
	 * select(store(a,i,v),j) = if i = j then v else select(a,j). Array store
	 * takes at least 3 arguments. </remarks>
	 **/
	public boolean isStore() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_STORE;
	}

	/**
	 * Indicates whether the term is an array select.
	 **/
	public boolean isSelect() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SELECT;
	}

	/**
	 * Indicates whether the term is a constant array. <remarks>For example,
	 * select(const(v),i) = v holds for every v and i. The function is
	 * unary.</remarks>
	 **/
	public boolean isConstantArray() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_CONST_ARRAY;
	}

	/**
	 * Indicates whether the term is a default array. <remarks>For example
	 * default(const(v)) = v. The function is unary.</remarks>
	 **/
	public boolean isDefaultArray() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_ARRAY_DEFAULT;
	}

	/**
	 * Indicates whether the term is an array map. <remarks>It satisfies
	 * map[f](a1,..,a_n)[i] = f(a1[i],...,a_n[i]) for every i.</remarks>
	 **/
	public boolean isArrayMap() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_ARRAY_MAP;
	}

	/**
	 * Indicates whether the term is an as-array term. <remarks>An as-array term
	 * is n array value that behaves as the function graph of the function
	 * passed as parameter.</remarks>
	 **/
	public boolean isAsArray() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_AS_ARRAY;
	}

	/**
	 * Indicates whether the term is set union
	 **/
	public boolean isSetUnion() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SET_UNION;
	}

	/**
	 * Indicates whether the term is set intersection
	 **/
	public boolean isSetIntersect() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SET_INTERSECT;
	}

	/**
	 * Indicates whether the term is set difference
	 **/
	public boolean isSetDifference() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SET_DIFFERENCE;
	}

	/**
	 * Indicates whether the term is set complement
	 **/
	public boolean isSetComplement() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SET_COMPLEMENT;
	}

	/**
	 * Indicates whether the term is set subset
	 **/
	public boolean isSetSubset() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SET_SUBSET;
	}

	/**
	 * Indicates whether the terms is of bit-vector sort.
	 **/
	public boolean isBV() throws Z3Exception
	{
		return Native.getSortKind(getContext().nCtx(),
				Native.getSort(getContext().nCtx(), getNativeObject())) == Z3_sort_kind.Z3_BV_SORT
				.toInt();
	}

	/**
	 * Indicates whether the term is a bit-vector numeral
	 **/
	public boolean isBVNumeral() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BNUM;
	}

	/**
	 * Indicates whether the term is a one-bit bit-vector with value one
	 **/
	public boolean isBVBitOne() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BIT1;
	}

	/**
	 * Indicates whether the term is a one-bit bit-vector with value zero
	 **/
	public boolean isBVBitZero() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BIT0;
	}

	/**
	 * Indicates whether the term is a bit-vector unary minus
	 **/
	public boolean isBVUMinus() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BNEG;
	}

	/**
	 * Indicates whether the term is a bit-vector addition (binary)
	 **/
	public boolean isBVAdd() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BADD;
	}

	/**
	 * Indicates whether the term is a bit-vector subtraction (binary)
	 **/
	public boolean isBVSub() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BSUB;
	}

	/**
	 * Indicates whether the term is a bit-vector multiplication (binary)
	 **/
	public boolean isBVMul() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BMUL;
	}

	/**
	 * Indicates whether the term is a bit-vector signed division (binary)
	 **/
	public boolean isBVSDiv() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BSDIV;
	}

	/**
	 * Indicates whether the term is a bit-vector unsigned division (binary)
	 **/
	public boolean isBVUDiv() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BUDIV;
	}

	/**
	 * Indicates whether the term is a bit-vector signed remainder (binary)
	 **/
	public boolean isBVSRem() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BSREM;
	}

	/**
	 * Indicates whether the term is a bit-vector unsigned remainder (binary)
	 **/
	public boolean isBVURem() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BUREM;
	}

	/**
	 * Indicates whether the term is a bit-vector signed modulus
	 **/
	public boolean isBVSMod() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BSMOD;
	}

	/**
	 * Indicates whether the term is a bit-vector signed division by zero
	 **/
	boolean IsBVSDiv0() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BSDIV0;
	}

	/**
	 * Indicates whether the term is a bit-vector unsigned division by zero
	 **/
	boolean IsBVUDiv0() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BUDIV0;
	}

	/**
	 * Indicates whether the term is a bit-vector signed remainder by zero
	 **/
	boolean IsBVSRem0() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BSREM0;
	}

	/**
	 * Indicates whether the term is a bit-vector unsigned remainder by zero
	 **/
	boolean IsBVURem0() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BUREM0;
	}

	/**
	 * Indicates whether the term is a bit-vector signed modulus by zero
	 **/
	boolean IsBVSMod0() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BSMOD0;
	}

	/**
	 * Indicates whether the term is an unsigned bit-vector less-than-or-equal
	 **/
	public boolean isBVULE() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_ULEQ;
	}

	/**
	 * Indicates whether the term is a signed bit-vector less-than-or-equal
	 **/
	public boolean isBVSLE() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SLEQ;
	}

	/**
	 * Indicates whether the term is an unsigned bit-vector
	 * greater-than-or-equal
	 **/
	public boolean isBVUGE() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_UGEQ;
	}

	/**
	 * Indicates whether the term is a signed bit-vector greater-than-or-equal
	 **/
	public boolean isBVSGE() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SGEQ;
	}

	/**
	 * Indicates whether the term is an unsigned bit-vector less-than
	 **/
	public boolean isBVULT() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_ULT;
	}

	/**
	 * Indicates whether the term is a signed bit-vector less-than
	 **/
	public boolean isBVSLT() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SLT;
	}

	/**
	 * Indicates whether the term is an unsigned bit-vector greater-than
	 **/
	public boolean isBVUGT() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_UGT;
	}

	/**
	 * Indicates whether the term is a signed bit-vector greater-than
	 **/
	public boolean isBVSGT() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SGT;
	}

	/**
	 * Indicates whether the term is a bit-wise AND
	 **/
	public boolean isBVAND() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BAND;
	}

	/**
	 * Indicates whether the term is a bit-wise OR
	 **/
	public boolean isBVOR() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BOR;
	}

	/**
	 * Indicates whether the term is a bit-wise NOT
	 **/
	public boolean isBVNOT() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BNOT;
	}

	/**
	 * Indicates whether the term is a bit-wise XOR
	 **/
	public boolean isBVXOR() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BXOR;
	}

	/**
	 * Indicates whether the term is a bit-wise NAND
	 **/
	public boolean isBVNAND() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BNAND;
	}

	/**
	 * Indicates whether the term is a bit-wise NOR
	 **/
	public boolean isBVNOR() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BNOR;
	}

	/**
	 * Indicates whether the term is a bit-wise XNOR
	 **/
	public boolean isBVXNOR() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BXNOR;
	}

	/**
	 * Indicates whether the term is a bit-vector concatenation (binary)
	 **/
	public boolean isBVConcat() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_CONCAT;
	}

	/**
	 * Indicates whether the term is a bit-vector sign extension
	 **/
	public boolean isBVSignExtension() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SIGN_EXT;
	}

	/**
	 * Indicates whether the term is a bit-vector zero extension
	 **/
	public boolean isBVZeroExtension() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_ZERO_EXT;
	}

	/**
	 * Indicates whether the term is a bit-vector extraction
	 **/
	public boolean isBVExtract() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_EXTRACT;
	}

	/**
	 * Indicates whether the term is a bit-vector repetition
	 **/
	public boolean isBVRepeat() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_REPEAT;
	}

	/**
	 * Indicates whether the term is a bit-vector reduce OR
	 **/
	public boolean isBVReduceOR() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BREDOR;
	}

	/**
	 * Indicates whether the term is a bit-vector reduce AND
	 **/
	public boolean isBVReduceAND() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BREDAND;
	}

	/**
	 * Indicates whether the term is a bit-vector comparison
	 **/
	public boolean isBVComp() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BCOMP;
	}

	/**
	 * Indicates whether the term is a bit-vector shift left
	 **/
	public boolean isBVShiftLeft() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BSHL;
	}

	/**
	 * Indicates whether the term is a bit-vector logical shift right
	 **/
	public boolean isBVShiftRightLogical() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BLSHR;
	}

	/**
	 * Indicates whether the term is a bit-vector arithmetic shift left
	 **/
	public boolean isBVShiftRightArithmetic() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BASHR;
	}

	/**
	 * Indicates whether the term is a bit-vector rotate left
	 **/
	public boolean isBVRotateLeft() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_ROTATE_LEFT;
	}

	/**
	 * Indicates whether the term is a bit-vector rotate right
	 **/
	public boolean isBVRotateRight() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_ROTATE_RIGHT;
	}

	/**
	 * Indicates whether the term is a bit-vector rotate left (extended)
	 * <remarks>Similar to Z3_OP_ROTATE_LEFT, but it is a binary operator
	 * instead of a parametric one.</remarks>
	 **/
	public boolean isBVRotateLeftExtended() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_EXT_ROTATE_LEFT;
	}

	/**
	 * Indicates whether the term is a bit-vector rotate right (extended)
	 * <remarks>Similar to Z3_OP_ROTATE_RIGHT, but it is a binary operator
	 * instead of a parametric one.</remarks>
	 **/
	public boolean isBVRotateRightExtended() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_EXT_ROTATE_RIGHT;
	}

	/**
	 * Indicates whether the term is a coercion from integer to bit-vector
	 * <remarks>This function is not supported by the decision procedures. Only
	 * the most rudimentary simplification rules are applied to this
	 * function.</remarks>
	 **/
	public boolean isIntToBV() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_INT2BV;
	}

	/**
	 * Indicates whether the term is a coercion from bit-vector to integer
	 * <remarks>This function is not supported by the decision procedures. Only
	 * the most rudimentary simplification rules are applied to this
	 * function.</remarks>
	 **/
	public boolean isBVToInt() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BV2INT;
	}

	/**
	 * Indicates whether the term is a bit-vector carry <remarks>Compute the
	 * carry bit in a full-adder. The meaning is given by the equivalence (carry
	 * l1 l2 l3) &lt;=&gt; (or (and l1 l2) (and l1 l3) (and l2 l3)))</remarks>
	 **/
	public boolean isBVCarry() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_CARRY;
	}

	/**
	 * Indicates whether the term is a bit-vector ternary XOR <remarks>The
	 * meaning is given by the equivalence (xor3 l1 l2 l3) &lt;=&gt; (xor (xor
	 * l1 l2) l3)</remarks>
	 **/
	public boolean isBVXOR3() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_XOR3;
	}

	/**
	 * Indicates whether the term is a label (used by the Boogie Verification
	 * condition generator). <remarks>The label has two parameters, a string and
	 * a Boolean polarity. It takes one argument, a formula.</remarks>
	 **/
	public boolean isLabel() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_LABEL;
	}

	/**
	 * Indicates whether the term is a label literal (used by the Boogie
	 * Verification condition generator). <remarks>A label literal has a set of
	 * string parameters. It takes no arguments.</remarks>
	 **/
	public boolean isLabelLit() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_LABEL_LIT;
	}

	/**
	 * Indicates whether the term is a binary equivalence modulo namings.
	 * <remarks>This binary predicate is used in proof terms. It captures
	 * equisatisfiability and equivalence modulo renamings.</remarks>
	 **/
	public boolean isOEQ() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_OEQ;
	}

	/**
	 * Indicates whether the term is a Proof for the expression 'true'.
	 **/
	public boolean isProofTrue() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_TRUE;
	}

	/**
	 * Indicates whether the term is a proof for a fact asserted by the user.
	 **/
	public boolean isProofAsserted() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_ASSERTED;
	}

	/**
	 * Indicates whether the term is a proof for a fact (tagged as goal)
	 * asserted by the user.
	 **/
	public boolean isProofGoal() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_GOAL;
	}

	/**
	 * Indicates whether the term is proof via modus ponens <remarks> Given a
	 * proof for p and a proof for (implies p q), produces a proof for q. T1: p
	 * T2: (implies p q) [mp T1 T2]: q The second antecedents may also be a
	 * proof for (iff p q).</remarks>
	 **/
	public boolean isProofModusPonens() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_MODUS_PONENS;
	}

	/**
	 * Indicates whether the term is a proof for (R t t), where R is a reflexive
	 * relation. <remarks>This proof object has no antecedents. The only
	 * reflexive relations that are used are equivalence modulo namings,
	 * equality and equivalence. That is, R is either '~', '=' or
	 * 'iff'.</remarks>
	 **/
	public boolean isProofReflexivity() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_REFLEXIVITY;
	}

	/**
	 * Indicates whether the term is proof by symmetricity of a relation
	 * <remarks> Given an symmetric relation R and a proof for (R t s), produces
	 * a proof for (R s t). T1: (R t s) [symmetry T1]: (R s t) T1 is the
	 * antecedent of this proof object. </remarks>
	 **/
	public boolean isProofSymmetry() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_SYMMETRY;
	}

	/**
	 * Indicates whether the term is a proof by transitivity of a relation
	 * <remarks> Given a transitive relation R, and proofs for (R t s) and (R s
	 * u), produces a proof for (R t u). T1: (R t s) T2: (R s u) [trans T1 T2]:
	 * (R t u) </remarks>
	 **/
	public boolean isProofTransitivity() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_TRANSITIVITY;
	}

	/**
	 * Indicates whether the term is a proof by condensed transitivity of a
	 * relation <remarks> Condensed transitivity proof. This proof object is
	 * only used if the parameter PROOF_MODE is 1. It combines several symmetry
	 * and transitivity proofs. Example: T1: (R a b) T2: (R c b) T3: (R c d)
	 * [trans* T1 T2 T3]: (R a d) R must be a symmetric and transitive relation.
	 * 
	 * Assuming that this proof object is a proof for (R s t), then a proof
	 * checker must check if it is possible to prove (R s t) using the
	 * antecedents, symmetry and transitivity. That is, if there is a path from
	 * s to t, if we view every antecedent (R a b) as an edge between a and b.
	 * </remarks>
	 **/
	public boolean isProofTransitivityStar() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_TRANSITIVITY_STAR;
	}

	/**
	 * Indicates whether the term is a monotonicity proof object. <remarks> T1:
	 * (R t_1 s_1) ... Tn: (R t_n s_n) [monotonicity T1 ... Tn]: (R (f t_1 ...
	 * t_n) (f s_1 ... s_n)) Remark: if t_i == s_i, then the antecedent Ti is
	 * suppressed. That is, reflexivity proofs are supressed to save space.
	 * </remarks>
	 **/
	public boolean isProofMonotonicity() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_MONOTONICITY;
	}

	/**
	 * Indicates whether the term is a quant-intro proof <remarks> Given a proof
	 * for (~ p q), produces a proof for (~ (forall (x) p) (forall (x) q)). T1:
	 * (~ p q) [quant-intro T1]: (~ (forall (x) p) (forall (x) q)) </remarks>
	 **/
	public boolean isProofQuantIntro() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_QUANT_INTRO;
	}

	/**
	 * Indicates whether the term is a distributivity proof object. <remarks>
	 * Given that f (= or) distributes over g (= and), produces a proof for (=
	 * (f a (g c d)) (g (f a c) (f a d))) If f and g are associative, this proof
	 * also justifies the following equality: (= (f (g a b) (g c d)) (g (f a c)
	 * (f a d) (f b c) (f b d))) where each f and g can have arbitrary number of
	 * arguments.
	 * 
	 * This proof object has no antecedents. Remark. This rule is used by the
	 * CNF conversion pass and instantiated by f = or, and g = and. </remarks>
	 **/
	public boolean isProofDistributivity() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_DISTRIBUTIVITY;
	}

	/**
	 * Indicates whether the term is a proof by elimination of AND <remarks>
	 * Given a proof for (and l_1 ... l_n), produces a proof for l_i T1: (and
	 * l_1 ... l_n) [and-elim T1]: l_i </remarks>
	 **/
	public boolean isProofAndElimination() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_AND_ELIM;
	}

	/**
	 * Indicates whether the term is a proof by eliminiation of not-or <remarks>
	 * Given a proof for (not (or l_1 ... l_n)), produces a proof for (not l_i).
	 * T1: (not (or l_1 ... l_n)) [not-or-elim T1]: (not l_i) </remarks>
	 **/
	public boolean isProofOrElimination() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_NOT_OR_ELIM;
	}

	/**
	 * Indicates whether the term is a proof by rewriting <remarks> A proof for
	 * a local rewriting step (= t s). The head function symbol of t is
	 * interpreted.
	 * 
	 * This proof object has no antecedents. The conclusion of a rewrite rule is
	 * either an equality (= t s), an equivalence (iff t s), or
	 * equi-satisfiability (~ t s). Remark: if f is bool, then = is iff.
	 * 
	 * Examples: (= (+ x 0) x) (= (+ x 1 2) (+ 3 x)) (iff (or x false) x)
	 * </remarks>
	 **/
	public boolean isProofRewrite() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_REWRITE;
	}

	/**
	 * Indicates whether the term is a proof by rewriting <remarks> A proof for
	 * rewriting an expression t into an expression s. This proof object is used
	 * if the parameter PROOF_MODE is 1. This proof object can have n
	 * antecedents. The antecedents are proofs for equalities used as
	 * substitution rules. The object is also used in a few cases if the
	 * parameter PROOF_MODE is 2. The cases are: - When applying contextual
	 * simplification (CONTEXT_SIMPLIFIER=true) - When converting bit-vectors to
	 * Booleans (BIT2BOOL=true) - When pulling ite expression up
	 * (PULL_CHEAP_ITE_TREES=true) </remarks>
	 **/
	public boolean isProofRewriteStar() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_REWRITE_STAR;
	}

	/**
	 * Indicates whether the term is a proof for pulling quantifiers out.
	 * <remarks> A proof for (iff (f (forall (x) q(x)) r) (forall (x) (f (q x)
	 * r))). This proof object has no antecedents. </remarks>
	 **/
	public boolean isProofPullQuant() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_PULL_QUANT;
	}

	/**
	 * Indicates whether the term is a proof for pulling quantifiers out.
	 * <remarks> A proof for (iff P Q) where Q is in prenex normal form. This
	 * proof object is only used if the parameter PROOF_MODE is 1. This proof
	 * object has no antecedents </remarks>
	 **/
	public boolean isProofPullQuantStar() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_PULL_QUANT_STAR;
	}

	/**
	 * Indicates whether the term is a proof for pushing quantifiers in.
	 * <remarks> A proof for: (iff (forall (x_1 ... x_m) (and p_1[x_1 ... x_m]
	 * ... p_n[x_1 ... x_m])) (and (forall (x_1 ... x_m) p_1[x_1 ... x_m]) ...
	 * (forall (x_1 ... x_m) p_n[x_1 ... x_m]))) This proof object has no
	 * antecedents </remarks>
	 **/
	public boolean isProofPushQuant() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_PUSH_QUANT;
	}

	/**
	 * Indicates whether the term is a proof for elimination of unused
	 * variables. <remarks> A proof for (iff (forall (x_1 ... x_n y_1 ... y_m)
	 * p[x_1 ... x_n]) (forall (x_1 ... x_n) p[x_1 ... x_n]))
	 * 
	 * It is used to justify the elimination of unused variables. This proof
	 * object has no antecedents. </remarks>
	 **/
	public boolean isProofElimUnusedVars() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_ELIM_UNUSED_VARS;
	}

	/**
	 * Indicates whether the term is a proof for destructive equality resolution
	 * <remarks> A proof for destructive equality resolution: (iff (forall (x)
	 * (or (not (= x t)) P[x])) P[t]) if x does not occur in t.
	 * 
	 * This proof object has no antecedents.
	 * 
	 * Several variables can be eliminated simultaneously. </remarks>
	 **/
	public boolean isProofDER() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_DER;
	}

	/**
	 * Indicates whether the term is a proof for quantifier instantiation
	 * <remarks> A proof of (or (not (forall (x) (P x))) (P a)) </remarks>
	 **/
	public boolean isProofQuantInst() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_QUANT_INST;
	}

	/**
	 * Indicates whether the term is a hypthesis marker. <remarks>Mark a
	 * hypothesis in a natural deduction style proof.</remarks>
	 **/
	public boolean isProofHypothesis() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_HYPOTHESIS;
	}

	/**
	 * Indicates whether the term is a proof by lemma <remarks> T1: false [lemma
	 * T1]: (or (not l_1) ... (not l_n))
	 * 
	 * This proof object has one antecedent: a hypothetical proof for false. It
	 * converts the proof in a proof for (or (not l_1) ... (not l_n)), when T1
	 * contains the hypotheses: l_1, ..., l_n. </remarks>
	 **/
	public boolean isProofLemma() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_LEMMA;
	}

	/**
	 * Indicates whether the term is a proof by unit resolution <remarks> T1:
	 * (or l_1 ... l_n l_1' ... l_m') T2: (not l_1) ... T(n+1): (not l_n)
	 * [unit-resolution T1 ... T(n+1)]: (or l_1' ... l_m') </remarks>
	 **/
	public boolean isProofUnitResolution() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_UNIT_RESOLUTION;
	}

	/**
	 * Indicates whether the term is a proof by iff-true <remarks> T1: p
	 * [iff-true T1]: (iff p true) </remarks>
	 **/
	public boolean isProofIFFTrue() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_IFF_TRUE;
	}

	/**
	 * Indicates whether the term is a proof by iff-false <remarks> T1: (not p)
	 * [iff-false T1]: (iff p false) </remarks>
	 **/
	public boolean isProofIFFFalse() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_IFF_FALSE;
	}

	/**
	 * Indicates whether the term is a proof by commutativity <remarks> [comm]:
	 * (= (f a b) (f b a))
	 * 
	 * f is a commutative operator.
	 * 
	 * This proof object has no antecedents. Remark: if f is bool, then = is
	 * iff. </remarks>
	 **/
	public boolean isProofCommutativity() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_COMMUTATIVITY;
	}

	/**
	 * Indicates whether the term is a proof for Tseitin-like axioms <remarks>
	 * Proof object used to justify Tseitin's like axioms:
	 * 
	 * (or (not (and p q)) p) (or (not (and p q)) q) (or (not (and p q r)) p)
	 * (or (not (and p q r)) q) (or (not (and p q r)) r) ... (or (and p q) (not
	 * p) (not q)) (or (not (or p q)) p q) (or (or p q) (not p)) (or (or p q)
	 * (not q)) (or (not (iff p q)) (not p) q) (or (not (iff p q)) p (not q))
	 * (or (iff p q) (not p) (not q)) (or (iff p q) p q) (or (not (ite a b c))
	 * (not a) b) (or (not (ite a b c)) a c) (or (ite a b c) (not a) (not b))
	 * (or (ite a b c) a (not c)) (or (not (not a)) (not a)) (or (not a) a)
	 * 
	 * This proof object has no antecedents. Note: all axioms are propositional
	 * tautologies. Note also that 'and' and 'or' can take multiple arguments.
	 * You can recover the propositional tautologies by unfolding the Boolean
	 * connectives in the axioms a small bounded number of steps (=3).
	 * </remarks>
	 **/
	public boolean isProofDefAxiom() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_DEF_AXIOM;
	}

	/**
	 * Indicates whether the term is a proof for introduction of a name
	 * <remarks> Introduces a name for a formula/term. Suppose e is an
	 * expression with free variables x, and def-intro introduces the name n(x).
	 * The possible cases are:
	 * 
	 * When e is of Boolean type: [def-intro]: (and (or n (not e)) (or (not n)
	 * e))
	 * 
	 * or: [def-intro]: (or (not n) e) when e only occurs positively.
	 * 
	 * When e is of the form (ite cond th el): [def-intro]: (and (or (not cond)
	 * (= n th)) (or cond (= n el)))
	 * 
	 * Otherwise: [def-intro]: (= n e) </remarks>
	 **/
	public boolean isProofDefIntro() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_DEF_INTRO;
	}

	/**
	 * Indicates whether the term is a proof for application of a definition
	 * <remarks> [apply-def T1]: F ~ n F is 'equivalent' to n, given that T1 is
	 * a proof that n is a name for F. </remarks>
	 **/
	public boolean isProofApplyDef() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_APPLY_DEF;
	}

	/**
	 * Indicates whether the term is a proof iff-oeq <remarks> T1: (iff p q)
	 * [iff~ T1]: (~ p q) </remarks>
	 **/
	public boolean isProofIFFOEQ() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_IFF_OEQ;
	}

	/**
	 * Indicates whether the term is a proof for a positive NNF step <remarks>
	 * Proof for a (positive) NNF step. Example:
	 * 
	 * T1: (not s_1) ~ r_1 T2: (not s_2) ~ r_2 T3: s_1 ~ r_1' T4: s_2 ~ r_2'
	 * [nnf-pos T1 T2 T3 T4]: (~ (iff s_1 s_2) (and (or r_1 r_2') (or r_1'
	 * r_2)))
	 * 
	 * The negation normal form steps NNF_POS and NNF_NEG are used in the
	 * following cases: (a) When creating the NNF of a positive force
	 * quantifier. The quantifier is retained (unless the bound variables are
	 * eliminated). Example T1: q ~ q_new [nnf-pos T1]: (~ (forall (x T) q)
	 * (forall (x T) q_new))
	 * 
	 * (b) When recursively creating NNF over Boolean formulas, where the
	 * top-level connective is changed during NNF conversion. The relevant
	 * Boolean connectives for NNF_POS are 'implies', 'iff', 'xor', 'ite'.
	 * NNF_NEG furthermore handles the case where negation is pushed over
	 * Boolean connectives 'and' and 'or'. </remarks>
	 **/
	public boolean isProofNNFPos() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_NNF_POS;
	}

	/**
	 * Indicates whether the term is a proof for a negative NNF step <remarks>
	 * Proof for a (negative) NNF step. Examples:
	 * 
	 * T1: (not s_1) ~ r_1 ... Tn: (not s_n) ~ r_n [nnf-neg T1 ... Tn]: (not
	 * (and s_1 ... s_n)) ~ (or r_1 ... r_n) and T1: (not s_1) ~ r_1 ... Tn:
	 * (not s_n) ~ r_n [nnf-neg T1 ... Tn]: (not (or s_1 ... s_n)) ~ (and r_1
	 * ... r_n) and T1: (not s_1) ~ r_1 T2: (not s_2) ~ r_2 T3: s_1 ~ r_1' T4:
	 * s_2 ~ r_2' [nnf-neg T1 T2 T3 T4]: (~ (not (iff s_1 s_2)) (and (or r_1
	 * r_2) (or r_1' r_2'))) </remarks>
	 **/
	public boolean isProofNNFNeg() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_NNF_NEG;
	}

	/**
	 * Indicates whether the term is a proof for (~ P Q) here Q is in negation
	 * normal form. <remarks> A proof for (~ P Q) where Q is in negation normal
	 * form.
	 * 
	 * This proof object is only used if the parameter PROOF_MODE is 1.
	 * 
	 * This proof object may have n antecedents. Each antecedent is a
	 * PR_DEF_INTRO. </remarks>
	 **/
	public boolean isProofNNFStar() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_NNF_STAR;
	}

	/**
	 * Indicates whether the term is a proof for (~ P Q) where Q is in
	 * conjunctive normal form. <remarks> A proof for (~ P Q) where Q is in
	 * conjunctive normal form. This proof object is only used if the parameter
	 * PROOF_MODE is 1. This proof object may have n antecedents. Each
	 * antecedent is a PR_DEF_INTRO. </remarks>
	 **/
	public boolean isProofCNFStar() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_CNF_STAR;
	}

	/**
	 * Indicates whether the term is a proof for a Skolemization step <remarks>
	 * Proof for:
	 * 
	 * [sk]: (~ (not (forall x (p x y))) (not (p (sk y) y))) [sk]: (~ (exists x
	 * (p x y)) (p (sk y) y))
	 * 
	 * This proof object has no antecedents. </remarks>
	 **/
	public boolean isProofSkolemize() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_SKOLEMIZE;
	}

	/**
	 * Indicates whether the term is a proof by modus ponens for
	 * equi-satisfiability. <remarks> Modus ponens style rule for
	 * equi-satisfiability. T1: p T2: (~ p q) [mp~ T1 T2]: q </remarks>
	 **/
	public boolean isProofModusPonensOEQ() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_MODUS_PONENS_OEQ;
	}

	/**
	 * Indicates whether the term is a proof for theory lemma <remarks> Generic
	 * proof for theory lemmas.
	 * 
	 * The theory lemma function comes with one or more parameters. The first
	 * parameter indicates the name of the theory. For the theory of arithmetic,
	 * additional parameters provide hints for checking the theory lemma. The
	 * hints for arithmetic are: - farkas - followed by rational coefficients.
	 * Multiply the coefficients to the inequalities in the lemma, add the
	 * (negated) inequalities and obtain a contradiction. - triangle-eq -
	 * Indicates a lemma related to the equivalence: (iff (= t1 t2) (and (&lt;=
	 * t1 t2) (&lt;= t2 t1))) - gcd-test - Indicates an integer linear
	 * arithmetic lemma that uses a gcd test. </remarks>
	 **/
	public boolean isProofTheoryLemma() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_TH_LEMMA;
	}

	/**
	 * Indicates whether the term is of an array sort.
	 **/
	public boolean isRelation() throws Z3Exception
	{
		return (Native.isApp(getContext().nCtx(), getNativeObject()) && Native
				.getSortKind(getContext().nCtx(),
						Native.getSort(getContext().nCtx(), getNativeObject())) == Z3_sort_kind.Z3_RELATION_SORT
				.toInt());
	}

	/**
	 * Indicates whether the term is an relation store <remarks> Insert a record
	 * into a relation. The function takes <code>n+1</code> arguments, where the
	 * first argument is the relation and the remaining <code>n</code> elements
	 * correspond to the <code>n</code> columns of the relation. </remarks>
	 **/
	public boolean isRelationStore() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_STORE;
	}

	/**
	 * Indicates whether the term is an empty relation
	 **/
	public boolean isEmptyRelation() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_EMPTY;
	}

	/**
	 * Indicates whether the term is a test for the emptiness of a relation
	 **/
	public boolean isIsEmptyRelation() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_IS_EMPTY;
	}

	/**
	 * Indicates whether the term is a relational join
	 **/
	public boolean isRelationalJoin() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_JOIN;
	}

	/**
	 * Indicates whether the term is the union or convex hull of two relations.
	 * <remarks>The function takes two arguments.</remarks>
	 **/
	public boolean isRelationUnion() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_UNION;
	}

	/**
	 * Indicates whether the term is the widening of two relations <remarks>The
	 * function takes two arguments.</remarks>
	 **/
	public boolean isRelationWiden() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_WIDEN;
	}

	/**
	 * Indicates whether the term is a projection of columns (provided as
	 * numbers in the parameters). <remarks>The function takes one
	 * argument.</remarks>
	 **/
	public boolean isRelationProject() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_PROJECT;
	}

	/**
	 * Indicates whether the term is a relation filter <remarks> Filter
	 * (restrict) a relation with respect to a predicate. The first argument is
	 * a relation. The second argument is a predicate with free de-Brujin
	 * indices corresponding to the columns of the relation. So the first column
	 * in the relation has index 0. </remarks>
	 **/
	public boolean isRelationFilter() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_FILTER;
	}

	/**
	 * Indicates whether the term is an intersection of a relation with the
	 * negation of another. <remarks> Intersect the first relation with respect
	 * to negation of the second relation (the function takes two arguments).
	 * Logically, the specification can be described by a function
	 * 
	 * target = filter_by_negation(pos, neg, columns)
	 * 
	 * where columns are pairs c1, d1, .., cN, dN of columns from pos and neg,
	 * such that target are elements in x in pos, such that there is no y in neg
	 * that agrees with x on the columns c1, d1, .., cN, dN. </remarks>
	 **/
	public boolean isRelationNegationFilter() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_NEGATION_FILTER;
	}

	/**
	 * Indicates whether the term is the renaming of a column in a relation
	 * <remarks> The function takes one argument. The parameters contain the
	 * renaming as a cycle. </remarks>
	 **/
	public boolean isRelationRename() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_RENAME;
	}

	/**
	 * Indicates whether the term is the complement of a relation
	 **/
	public boolean isRelationComplement() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_COMPLEMENT;
	}

	/**
	 * Indicates whether the term is a relational select <remarks> Check if a
	 * record is an element of the relation. The function takes <code>n+1</code>
	 * arguments, where the first argument is a relation, and the remaining
	 * <code>n</code> arguments correspond to a record. </remarks>
	 **/
	public boolean isRelationSelect() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_SELECT;
	}

	/**
	 * Indicates whether the term is a relational clone (copy) <remarks> Create
	 * a fresh copy (clone) of a relation. The function is logically the
	 * identity, but in the context of a register machine allows for terms of
	 * kind <seealso cref="IsRelationUnion"/> to perform destructive updates to
	 * the first argument. </remarks>
	 **/
	public boolean isRelationClone() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_CLONE;
	}

	/**
	 * Indicates whether the term is of an array sort.
	 **/
	public boolean isFiniteDomain() throws Z3Exception
	{
		return (Native.isApp(getContext().nCtx(), getNativeObject()) && Native
				.getSortKind(getContext().nCtx(),
						Native.getSort(getContext().nCtx(), getNativeObject())) == Z3_sort_kind.Z3_FINITE_DOMAIN_SORT
				.toInt());
	}

	/**
	 * Indicates whether the term is a less than predicate over a finite domain.
	 **/
	public boolean isFiniteDomainLT() throws Z3Exception
	{
		return getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_FD_LT;
	}

	/**
	 * The de-Burijn index of a bound variable. <remarks> Bound variables are
	 * indexed by de-Bruijn indices. It is perhaps easiest to explain the
	 * meaning of de-Bruijn indices by indicating the compilation process from
	 * non-de-Bruijn formulas to de-Bruijn format. <code>
	 * abs(forall (x1) phi) = forall (x1) abs1(phi, x1, 0)
	 * abs(forall (x1, x2) phi) = abs(forall (x1) abs(forall (x2) phi))
	 * abs1(x, x, n) = b_n
	 * abs1(y, x, n) = y
	 * abs1(f(t1,...,tn), x, n) = f(abs1(t1,x,n), ..., abs1(tn,x,n))
	 * abs1(forall (x1) phi, x, n) = forall (x1) (abs1(phi, x, n+1))
	 * </code> The last line is significant: the index of a bound variable is
	 * different depending on the scope in which it appears. The deeper x
	 * appears, the higher is its index. </remarks>
	 **/
	public int getIndex() throws Z3Exception
	{
		if (!isVar())
			throw new Z3Exception("Term is not a bound variable.");

		return Native.getIndexValue(getContext().nCtx(), getNativeObject());
	}

	/**
	 * Constructor for Expr
	 **/
	protected Expr(Context ctx)
	{
		super(ctx);
		{
		}
	}

	/**
	 * Constructor for Expr
	 **/
	protected Expr(Context ctx, long obj) throws Z3Exception
	{
		super(ctx, obj);
		{
		}
	}

	void checkNativeObject(long obj) throws Z3Exception
	{
		if (!Native.isApp(getContext().nCtx(), obj) && 
		    Native.getAstKind(getContext().nCtx(), obj) != Z3_ast_kind.Z3_VAR_AST.toInt() &&
		    Native.getAstKind(getContext().nCtx(), obj) != Z3_ast_kind.Z3_QUANTIFIER_AST.toInt())
		    throw new Z3Exception("Underlying object is not a term");
		super.checkNativeObject(obj);
	}

	static Expr create(Context ctx, FuncDecl f, Expr ... arguments)
			throws Z3Exception
	{
		long obj = Native.mkApp(ctx.nCtx(), f.getNativeObject(),
				AST.arrayLength(arguments), AST.arrayToNative(arguments));
		return create(ctx, obj);
	}

	static Expr create(Context ctx, long obj) throws Z3Exception
	{
		Z3_ast_kind k = Z3_ast_kind.fromInt(Native.getAstKind(ctx.nCtx(), obj));
		if (k == Z3_ast_kind.Z3_QUANTIFIER_AST)
			return new Quantifier(ctx, obj);
		long s = Native.getSort(ctx.nCtx(), obj);
		Z3_sort_kind sk = Z3_sort_kind
				.fromInt(Native.getSortKind(ctx.nCtx(), s));

		if (Native.isAlgebraicNumber(ctx.nCtx(), obj)) // is this a numeral ast?
			return new AlgebraicNum(ctx, obj);

		if (Native.isNumeralAst(ctx.nCtx(), obj))
		{
			switch (sk)
			{
			case Z3_INT_SORT:
				return new IntNum(ctx, obj);
			case Z3_REAL_SORT:
				return new RatNum(ctx, obj);
			case Z3_BV_SORT:
				return new BitVecNum(ctx, obj);
			default: ;
			}
		}

		switch (sk)
		{
		case Z3_BOOL_SORT:
			return new BoolExpr(ctx, obj);
		case Z3_INT_SORT:
			return new IntExpr(ctx, obj);
		case Z3_REAL_SORT:
			return new RealExpr(ctx, obj);
		case Z3_BV_SORT:
			return new BitVecExpr(ctx, obj);
		case Z3_ARRAY_SORT:
			return new ArrayExpr(ctx, obj);
		case Z3_DATATYPE_SORT:
			return new DatatypeExpr(ctx, obj);
		default: ;
		}

		return new Expr(ctx, obj);
	}
}
