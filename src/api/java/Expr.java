/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    Expr.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
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
     * @return Expr
     * @throws Z3Exception on error
     **/
    public Expr simplify()
    {
        return simplify(null);
    }

    /**
     * Returns a simplified version of the expression 
     * A set of
     * parameters 
     * @param p a Params object to configure the simplifier 
     * @see Context#SimplifyHelp
     * @return an Expr
     * @throws Z3Exception on error
     **/
    public Expr simplify(Params p)
    {

        if (p == null) {
            return Expr.create(getContext(),
                Native.simplify(getContext().nCtx(), getNativeObject()));
        }
        else {
            return Expr.create(
                getContext(),
                Native.simplifyEx(getContext().nCtx(), getNativeObject(),
                    p.getNativeObject()));
        }
    }

    /**
     * The function declaration of the function that is applied in this
     * expression.
     * @return a FuncDecl
     * @throws Z3Exception on error 
     **/
    public FuncDecl getFuncDecl()
    {
        return new FuncDecl(getContext(), Native.getAppDecl(getContext().nCtx(),
                getNativeObject()));
    }

    /**
     * Indicates whether the expression is the true or false expression or
     * something else (Z3_L_UNDEF).
     * @throws Z3Exception on error     
     * @return a Z3_lbool
     **/
    public Z3_lbool getBoolValue()
    {
        return Z3_lbool.fromInt(Native.getBoolValue(getContext().nCtx(),
                getNativeObject()));
    }

    /**
     * The number of arguments of the expression.
     * @throws Z3Exception on error
     * @return an int
     **/
    public int getNumArgs()
    {
        return Native.getAppNumArgs(getContext().nCtx(), getNativeObject());
    }

    /**
     * The arguments of the expression.
     * @throws Z3Exception on error
     * @return an Expr[]
     **/
    public Expr[] getArgs()
    {
        int n = getNumArgs();
        Expr[] res = new Expr[n];
        for (int i = 0; i < n; i++) {
            res[i] = Expr.create(getContext(),
                Native.getAppArg(getContext().nCtx(), getNativeObject(), i));
        }
        return res;
    }

    /**
     * Update the arguments of the expression using the arguments {@code args}
     * The number of new arguments should coincide with the
     * current number of arguments.
     * @param args arguments
     * @throws Z3Exception on error
     **/
    public Expr update(Expr[] args)
    {
        getContext().checkContextMatch(args);
        if (isApp() && args.length != getNumArgs()) {
            throw new Z3Exception("Number of arguments does not match");
        }
        return Expr.create(getContext(), Native.updateTerm(getContext().nCtx(), getNativeObject(),
                args.length, Expr.arrayToNative(args)));
    }

    /**
     * Substitute every occurrence of {@code from[i]} in the expression
     * with {@code to[i]}, for {@code i} smaller than
     * {@code num_exprs}. 
     * Remarks: The result is the new expression. The
     * arrays {@code from} and {@code to} must have size
     * {@code num_exprs}. For every {@code i} smaller than
     * {@code num_exprs}, we must have that sort of {@code from[i]}
     * must be equal to sort of {@code to[i]}.
     * @throws Z3Exception on error
     * @return an Expr
     **/
    public Expr substitute(Expr[] from, Expr[] to)
    {
        getContext().checkContextMatch(from);
        getContext().checkContextMatch(to);
        if (from.length != to.length) {
            throw new Z3Exception("Argument sizes do not match");
        }
        return Expr.create(getContext(), Native.substitute(getContext().nCtx(),
                getNativeObject(), from.length, Expr.arrayToNative(from),
                Expr.arrayToNative(to)));
    }

    /**
     * Substitute every occurrence of {@code from} in the expression with
     * {@code to}. 
     * @see Expr#substitute(Expr[],Expr[])
     * @throws Z3Exception on error
     * @return an Expr
     **/
    public Expr substitute(Expr from, Expr to)
    {
        return substitute(new Expr[] { from }, new Expr[] { to });
    }

    /**
     * Substitute the free variables in the expression with the expressions in
     * {@code to} 
     * Remarks:  For every {@code i} smaller than * {@code num_exprs}, the 
     * variable with de-Bruijn index {@code i} * is replaced with term 
     * {@code to[i]}.
     * @throws Z3Exception on error 
     * @throws Z3Exception on error
     * @return an Expr
     **/
    public Expr substituteVars(Expr[] to)
    {

        getContext().checkContextMatch(to);
        return Expr.create(getContext(), Native.substituteVars(getContext().nCtx(),
                getNativeObject(), to.length, Expr.arrayToNative(to)));
    }

    /**
     * Translates (copies) the term to the Context {@code ctx}.
     * 
     * @param ctx A context
     * 
     * @return A copy of the term which is associated with {@code ctx}
     * @throws Z3Exception on error
     **/
    public Expr translate(Context ctx)
    {
        return (Expr) super.translate(ctx);
    }

    /**
     * Returns a string representation of the expression.
     **/
    @Override
    public String toString()
    {
        return super.toString();
    }

    /**
     * Indicates whether the term is a numeral
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isNumeral()
    {
        return Native.isNumeralAst(getContext().nCtx(), getNativeObject());
    }

    /**
     * Indicates whether the term is well-sorted.
     * 
     * @throws Z3Exception on error
     * @return True if the term is well-sorted, false otherwise.
     **/
    public boolean isWellSorted()
    {
        return Native.isWellSorted(getContext().nCtx(), getNativeObject());
    }

    /**
     * The Sort of the term.
     * @throws Z3Exception on error
     * @return a sort
     **/
    public Sort getSort()
    {
        return Sort.create(getContext(),
                Native.getSort(getContext().nCtx(), getNativeObject()));
    }

    /**
     * Indicates whether the term represents a constant.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isConst()
    {
        return isApp() && getNumArgs() == 0 && getFuncDecl().getDomainSize() == 0;
    }

    /**
     * Indicates whether the term is an integer numeral.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isIntNum()
    {
        return isNumeral() && isInt();
    }

    /**
     * Indicates whether the term is a real numeral.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isRatNum()
    {
        return isNumeral() && isReal();
    }

    /**
     * Indicates whether the term is an algebraic number
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isAlgebraicNumber()
    {
        return Native.isAlgebraicNumber(getContext().nCtx(), getNativeObject());
    }

    /**
     * Indicates whether the term has Boolean sort.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBool()
    {
        return (isExpr() && Native.isEqSort(getContext().nCtx(),
                Native.mkBoolSort(getContext().nCtx()),
                Native.getSort(getContext().nCtx(), getNativeObject())));
    }

    /**
     * Indicates whether the term is the constant true.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isTrue()
    {
            return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_TRUE;
    }

    /**
     * Indicates whether the term is the constant false.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isFalse()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_FALSE;
    }

    /**
     * Indicates whether the term is an equality predicate.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isEq()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_EQ;
    }

    /**
     * Indicates whether the term is an n-ary distinct predicate (every argument
     * is mutually distinct).
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isDistinct()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_DISTINCT;
    }

    /**
     * Indicates whether the term is a ternary if-then-else term
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isITE()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_ITE;
    }

    /**
     * Indicates whether the term is an n-ary conjunction
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isAnd()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_AND;
    }

    /**
     * Indicates whether the term is an n-ary disjunction
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isOr()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_OR;
    }

    /**
     * Indicates whether the term is an if-and-only-if (Boolean equivalence,
     * binary)
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isIff()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_IFF;
    }

    /**
     * Indicates whether the term is an exclusive or
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isXor()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_XOR;
    }

    /**
     * Indicates whether the term is a negation
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isNot()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_NOT;
    }

    /**
     * Indicates whether the term is an implication
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isImplies()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_IMPLIES;
    }

    /**
     * Indicates whether the term is of integer sort.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isInt()
    {
        return Native.getSortKind(getContext().nCtx(), Native.getSort(getContext().nCtx(), getNativeObject())) == Z3_sort_kind.Z3_INT_SORT.toInt();
    }

    /**
     * Indicates whether the term is of sort real.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isReal()
    {
        return Native.getSortKind(getContext().nCtx(), Native.getSort(getContext().nCtx(), getNativeObject())) == Z3_sort_kind.Z3_REAL_SORT.toInt();
    }

    /**
     * Indicates whether the term is an arithmetic numeral.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isArithmeticNumeral()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_ANUM;
    }

    /**
     * Indicates whether the term is a less-than-or-equal
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isLE()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_LE;
    }

    /**
     * Indicates whether the term is a greater-than-or-equal
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isGE()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_GE;
    }

    /**
     * Indicates whether the term is a less-than
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isLT()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_LT;
    }

    /**
     * Indicates whether the term is a greater-than
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isGT()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_GT;
    }

    /**
     * Indicates whether the term is addition (binary)
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isAdd()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_ADD;
    }

    /**
     * Indicates whether the term is subtraction (binary)
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isSub()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SUB;
    }

    /**
     * Indicates whether the term is a unary minus
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isUMinus()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_UMINUS;
    }

    /**
     * Indicates whether the term is multiplication (binary)
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isMul()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_MUL;
    }

    /**
     * Indicates whether the term is division (binary)
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isDiv()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_DIV;
    }

    /**
     * Indicates whether the term is integer division (binary)
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isIDiv()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_IDIV;
    }

    /**
     * Indicates whether the term is remainder (binary)
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isRemainder()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_REM;
    }

    /**
     * Indicates whether the term is modulus (binary)
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isModulus()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_MOD;
    }

    /**
     * Indicates whether the term is a coercion of integer to real (unary)
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isIntToReal()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_TO_REAL;
    }

    /**
     * Indicates whether the term is a coercion of real to integer (unary)
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isRealToInt()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_TO_INT;
    }

    /**
     * Indicates whether the term is a check that tests whether a real is
     * integral (unary)
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isRealIsInt()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_IS_INT;
    }

    /**
     * Indicates whether the term is of an array sort.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isArray()
    {
        return (Native.isApp(getContext().nCtx(), getNativeObject()) && Z3_sort_kind
                .fromInt(Native.getSortKind(getContext().nCtx(),
                        Native.getSort(getContext().nCtx(), getNativeObject()))) == Z3_sort_kind.Z3_ARRAY_SORT);
    }

    /**
     * Indicates whether the term is an array store. 
     * Remarks: It satisfies * select(store(a,i,v),j) = if i = j then v else select(a,j). Array store * takes at least 3 arguments. 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isStore()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_STORE;
    }

    /**
     * Indicates whether the term is an array select.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isSelect()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SELECT;
    }

    /**
     * Indicates whether the term is a constant array. 
     * Remarks: For example, * select(const(v),i) = v holds for every v and i. The function is * unary.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isConstantArray()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_CONST_ARRAY;
    }

    /**
     * Indicates whether the term is a default array. 
     * Remarks: For example default(const(v)) = v. The function is unary.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isDefaultArray()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_ARRAY_DEFAULT;
    }

    /**
     * Indicates whether the term is an array map. 
     * Remarks: It satisfies
     * map[f](a1,..,a_n)[i] = f(a1[i],...,a_n[i]) for every i.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isArrayMap()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_ARRAY_MAP;
    }

    /**
     * Indicates whether the term is an as-array term. 
     * Remarks: An as-array term * is n array value that behaves as the function graph of the function * passed as parameter.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isAsArray()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_AS_ARRAY;
    }

    /**
     * Indicates whether the term is set union
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isSetUnion()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SET_UNION;
    }

    /**
     * Indicates whether the term is set intersection
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isSetIntersect()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SET_INTERSECT;
    }

    /**
     * Indicates whether the term is set difference
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isSetDifference()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SET_DIFFERENCE;
    }

    /**
     * Indicates whether the term is set complement
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isSetComplement()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SET_COMPLEMENT;
    }

    /**
     * Indicates whether the term is set subset
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isSetSubset()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SET_SUBSET;
    }

    /**
     * Indicates whether the terms is of bit-vector sort.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBV()
    {
        return Native.getSortKind(getContext().nCtx(),
                Native.getSort(getContext().nCtx(), getNativeObject())) == Z3_sort_kind.Z3_BV_SORT
                .toInt();
    }

    /**
     * Indicates whether the term is a bit-vector numeral
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVNumeral()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BNUM;
    }

    /**
     * Indicates whether the term is a one-bit bit-vector with value one
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVBitOne()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BIT1;
    }

    /**
     * Indicates whether the term is a one-bit bit-vector with value zero
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVBitZero()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BIT0;
    }

    /**
     * Indicates whether the term is a bit-vector unary minus
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVUMinus()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BNEG;
    }

    /**
     * Indicates whether the term is a bit-vector addition (binary)
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVAdd()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BADD;
    }

    /**
     * Indicates whether the term is a bit-vector subtraction (binary)
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVSub()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BSUB;
    }

    /**
     * Indicates whether the term is a bit-vector multiplication (binary)
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVMul()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BMUL;
    }

    /**
     * Indicates whether the term is a bit-vector signed division (binary)
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVSDiv()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BSDIV;
    }

    /**
     * Indicates whether the term is a bit-vector unsigned division (binary)
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVUDiv()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BUDIV;
    }

    /**
     * Indicates whether the term is a bit-vector signed remainder (binary)
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVSRem()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BSREM;
    }

    /**
     * Indicates whether the term is a bit-vector unsigned remainder (binary)
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVURem()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BUREM;
    }

    /**
     * Indicates whether the term is a bit-vector signed modulus
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVSMod()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BSMOD;
    }

    /**
     * Indicates whether the term is a bit-vector signed division by zero
     * @return a boolean
     * @throws Z3Exception on error
     **/
    boolean isBVSDiv0()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BSDIV0;
    }

    /**
     * Indicates whether the term is a bit-vector unsigned division by zero
     * @return a boolean
     * @throws Z3Exception on error
     **/
    boolean isBVUDiv0()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BUDIV0;
    }

    /**
     * Indicates whether the term is a bit-vector signed remainder by zero
     * @return a boolean
     * @throws Z3Exception on error
     **/
    boolean isBVSRem0()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BSREM0;
    }

    /**
     * Indicates whether the term is a bit-vector unsigned remainder by zero
     * @return a boolean
     * @throws Z3Exception on error
     **/
    boolean isBVURem0()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BUREM0;
    }

    /**
     * Indicates whether the term is a bit-vector signed modulus by zero
     * @return a boolean
     * @throws Z3Exception on error
     **/
    boolean isBVSMod0()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BSMOD0;
    }

    /**
     * Indicates whether the term is an unsigned bit-vector less-than-or-equal
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVULE()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_ULEQ;
    }

    /**
     * Indicates whether the term is a signed bit-vector less-than-or-equal
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVSLE()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SLEQ;
    }

    /**
     * Indicates whether the term is an unsigned bit-vector
     * greater-than-or-equal
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVUGE()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_UGEQ;
    }

    /**
     * Indicates whether the term is a signed bit-vector greater-than-or-equal
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVSGE()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SGEQ;
    }

    /**
     * Indicates whether the term is an unsigned bit-vector less-than
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVULT()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_ULT;
    }

    /**
     * Indicates whether the term is a signed bit-vector less-than
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVSLT()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SLT;
    }

    /**
     * Indicates whether the term is an unsigned bit-vector greater-than
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVUGT()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_UGT;
    }

    /**
     * Indicates whether the term is a signed bit-vector greater-than
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVSGT()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SGT;
    }

    /**
     * Indicates whether the term is a bit-wise AND
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVAND()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BAND;
    }

    /**
     * Indicates whether the term is a bit-wise OR
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVOR()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BOR;
    }

    /**
     * Indicates whether the term is a bit-wise NOT
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVNOT()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BNOT;
    }

    /**
     * Indicates whether the term is a bit-wise XOR
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVXOR()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BXOR;
    }

    /**
     * Indicates whether the term is a bit-wise NAND
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVNAND()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BNAND;
    }

    /**
     * Indicates whether the term is a bit-wise NOR
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVNOR()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BNOR;
    }

    /**
     * Indicates whether the term is a bit-wise XNOR
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVXNOR()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BXNOR;
    }

    /**
     * Indicates whether the term is a bit-vector concatenation (binary)
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVConcat()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_CONCAT;
    }

    /**
     * Indicates whether the term is a bit-vector sign extension
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVSignExtension()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SIGN_EXT;
    }

    /**
     * Indicates whether the term is a bit-vector zero extension
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVZeroExtension()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_ZERO_EXT;
    }

    /**
     * Indicates whether the term is a bit-vector extraction
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVExtract()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_EXTRACT;
    }

    /**
     * Indicates whether the term is a bit-vector repetition
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVRepeat()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_REPEAT;
    }

    /**
     * Indicates whether the term is a bit-vector reduce OR
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVReduceOR()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BREDOR;
    }

    /**
     * Indicates whether the term is a bit-vector reduce AND
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVReduceAND()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BREDAND;
    }

    /**
     * Indicates whether the term is a bit-vector comparison
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVComp()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BCOMP;
    }

    /**
     * Indicates whether the term is a bit-vector shift left
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVShiftLeft()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BSHL;
    }

    /**
     * Indicates whether the term is a bit-vector logical shift right
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVShiftRightLogical()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BLSHR;
    }

    /**
     * Indicates whether the term is a bit-vector arithmetic shift left
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVShiftRightArithmetic()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BASHR;
    }

    /**
     * Indicates whether the term is a bit-vector rotate left
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVRotateLeft()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_ROTATE_LEFT;
    }

    /**
     * Indicates whether the term is a bit-vector rotate right
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVRotateRight()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_ROTATE_RIGHT;
    }

    /**
     * Indicates whether the term is a bit-vector rotate left (extended)
     * Remarks: Similar to Z3_OP_ROTATE_LEFT, but it is a binary operator
     * instead of a parametric one.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVRotateLeftExtended()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_EXT_ROTATE_LEFT;
    }

    /**
     * Indicates whether the term is a bit-vector rotate right (extended)
     * Remarks: Similar to Z3_OP_ROTATE_RIGHT, but it is a binary operator
     * instead of a parametric one.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVRotateRightExtended()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_EXT_ROTATE_RIGHT;
    }

    /**
     * Indicates whether the term is a coercion from integer to bit-vector
     * 
     * Remarks: This function is not supported by the decision procedures. Only * the most rudimentary simplification rules are applied to this * function.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isIntToBV()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_INT2BV;
    }

    /**
     * Indicates whether the term is a coercion from bit-vector to integer
     * 
     * Remarks: This function is not supported by the decision procedures. Only * the most rudimentary simplification rules are applied to this * function.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVToInt()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_BV2INT;
    }

    /**
     * Indicates whether the term is a bit-vector carry 
     * Remarks: Compute the * carry bit in a full-adder. The meaning is given by the equivalence (carry * l1 l2 l3) &lt;=&gt; (or (and l1 l2) (and l1 l3) (and l2 l3)))
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVCarry()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_CARRY;
    }

    /**
     * Indicates whether the term is a bit-vector ternary XOR 
     * Remarks: The * meaning is given by the equivalence (xor3 l1 l2 l3) &lt;=&gt; (xor (xor * l1 l2) l3)
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isBVXOR3()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_XOR3;
    }

    /**
     * Indicates whether the term is a label (used by the Boogie Verification
     * condition generator).
     * Remarks: The label has two parameters, a string and
     * a Boolean polarity. It takes one argument, a formula.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isLabel()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_LABEL;
    }

    /**
     * Indicates whether the term is a label literal (used by the Boogie
     * Verification condition generator).
     * Remarks: A label literal has a set of
     * string parameters. It takes no arguments.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isLabelLit()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_LABEL_LIT;
    }

    /**
     * Check whether expression is a string constant.
     * @return a boolean
     */
    public boolean isString() 
    {
        return isApp() && Native.isString(getContext().nCtx(), getNativeObject());
    }

    /**
     * Retrieve string corresponding to string constant.
     * Remark: the expression should be a string constant, (isString() should return true).
     * @throws Z3Exception on error
     * @return a string
     */
    public String getString()
    {
        return Native.getString(getContext().nCtx(), getNativeObject());
    }

    /**
     * Check whether expression is a concatenation
     * @return a boolean
     */
    public boolean isConcat() 
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_SEQ_CONCAT;
    }

    /**
     * Indicates whether the term is a binary equivalence modulo namings.
     * Remarks: This binary predicate is used in proof terms. It captures
     * equisatisfiability and equivalence modulo renamings.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isOEQ()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_OEQ;
    }

    /**
     * Indicates whether the term is a Proof for the expression 'true'.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofTrue()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_TRUE;
    }

    /**
     * Indicates whether the term is a proof for a fact asserted by the user.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofAsserted()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_ASSERTED;
    }

    /**
     * Indicates whether the term is a proof for a fact (tagged as goal)
     * asserted by the user.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofGoal()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_GOAL;
    }

    /**
     * Indicates whether the term is proof via modus ponens
     * Remarks:  Given a
     * proof for p and a proof for (implies p q), produces a proof for q. T1: p
     * T2: (implies p q) [mp T1 T2]: q The second antecedents may also be a
     * proof for (iff p q).
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofModusPonens()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_MODUS_PONENS;
    }

    /**
     * Indicates whether the term is a proof for (R t t), where R is a reflexive
     * relation.
     * Remarks: This proof object has no antecedents. The only
     * reflexive relations that are used are equivalence modulo namings,
     * equality and equivalence. That is, R is either '~', '=' or
     * 'iff'.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofReflexivity()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_REFLEXIVITY;
    }

    /**
     * Indicates whether the term is proof by symmetricity of a relation
     * 
     * Remarks:  Given an symmetric relation R and a proof for (R t s), produces * a proof for (R s t). T1: (R t s) [symmetry T1]: (R s t) T1 is the * antecedent of this proof object. 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofSymmetry()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_SYMMETRY;
    }

    /**
     * Indicates whether the term is a proof by transitivity of a relation
     * 
     * Remarks:  Given a transitive relation R, and proofs for (R t s) and (R s * u), produces a proof for (R t u). T1: (R t s) T2: (R s u) [trans T1 T2]: * (R t u) 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofTransitivity()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_TRANSITIVITY;
    }

    /**
     * Indicates whether the term is a proof by condensed transitivity of a
     * relation
     * Remarks:  Condensed transitivity proof. It combines several symmetry
     * and transitivity proofs. Example: T1: (R a b) T2: (R c b) T3: (R c d)
     * [trans* T1 T2 T3]: (R a d) R must be a symmetric and transitive relation.
     * 
     * Assuming that this proof object is a proof for (R s t), then a proof
     * checker must check if it is possible to prove (R s t) using the
     * antecedents, symmetry and transitivity. That is, if there is a path from
     * s to t, if we view every antecedent (R a b) as an edge between a and b.
     * 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofTransitivityStar()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_TRANSITIVITY_STAR;
    }

    /**
     * Indicates whether the term is a monotonicity proof object.
     * Remarks:  T1:
     * (R t_1 s_1) ... Tn: (R t_n s_n) [monotonicity T1 ... Tn]: (R (f t_1 ...
     * t_n) (f s_1 ... s_n)) Remark: if t_i == s_i, then the antecedent Ti is
     * suppressed. That is, reflexivity proofs are suppressed to save space.
     * 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofMonotonicity()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_MONOTONICITY;
    }

    /**
     * Indicates whether the term is a quant-intro proof 
     * Remarks:  Given a proof * for (~ p q), produces a proof for (~ (forall (x) p) (forall (x) q)). T1: * (~ p q) [quant-intro T1]: (~ (forall (x) p) (forall (x) q)) 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofQuantIntro()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_QUANT_INTRO;
    }

    /**
     * Indicates whether the term is a distributivity proof object.
     * Remarks: 
     * Given that f (= or) distributes over g (= and), produces a proof for (=
     * (f a (g c d)) (g (f a c) (f a d))) If f and g are associative, this proof
     * also justifies the following equality: (= (f (g a b) (g c d)) (g (f a c)
     * (f a d) (f b c) (f b d))) where each f and g can have arbitrary number of
     * arguments.
     * 
     * This proof object has no antecedents. Remark. This rule is used by the
     * CNF conversion pass and instantiated by f = or, and g = and. 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofDistributivity()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_DISTRIBUTIVITY;
    }

    /**
     * Indicates whether the term is a proof by elimination of AND 
     * Remarks:  * Given a proof for (and l_1 ... l_n), produces a proof for l_i T1: (and * l_1 ... l_n) [and-elim T1]: l_i 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofAndElimination()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_AND_ELIM;
    }

    /**
     * Indicates whether the term is a proof by elimination of not-or
     * Remarks:  * Given a proof for (not (or l_1 ... l_n)), produces a proof for (not l_i). * T1: (not (or l_1 ... l_n)) [not-or-elim T1]: (not l_i) 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofOrElimination()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_NOT_OR_ELIM;
    }

    /**
     * Indicates whether the term is a proof by rewriting
     * Remarks:  A proof for
     * a local rewriting step (= t s). The head function symbol of t is
     * interpreted.
     * 
     * This proof object has no antecedents. The conclusion of a rewrite rule is
     * either an equality (= t s), an equivalence (iff t s), or
     * equi-satisfiability (~ t s). Remark: if f is bool, then = is iff.
     * 
     * Examples: (= (+ x 0) x) (= (+ x 1 2) (+ 3 x)) (iff (or x false) x)
     * 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofRewrite()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_REWRITE;
    }

    /**
     * Indicates whether the term is a proof by rewriting
     * Remarks:  A proof for
     * rewriting an expression t into an expression s. This proof object can have n
     * antecedents. The antecedents are proofs for equalities used as
     * substitution rules. The object is used in a few cases . The cases are: - When applying contextual
     * simplification (CONTEXT_SIMPLIFIER=true) - When converting bit-vectors to
     * Booleans (BIT2BOOL=true) 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofRewriteStar()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_REWRITE_STAR;
    }

    /**
     * Indicates whether the term is a proof for pulling quantifiers out.
     * Remarks:  A proof for (iff (f (forall (x) q(x)) r) (forall (x) (f (q x)
     * r))). This proof object has no antecedents. 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofPullQuant()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_PULL_QUANT;
    }


    /**
     * Indicates whether the term is a proof for pushing quantifiers in.
     * Remarks:  A proof for: (iff (forall (x_1 ... x_m) (and p_1[x_1 ... x_m]
     * ... p_n[x_1 ... x_m])) (and (forall (x_1 ... x_m) p_1[x_1 ... x_m]) ...
     * (forall (x_1 ... x_m) p_n[x_1 ... x_m]))) This proof object has no
     * antecedents 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofPushQuant()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_PUSH_QUANT;
    }

    /**
     * Indicates whether the term is a proof for elimination of unused
     * variables.
     * Remarks:  A proof for (iff (forall (x_1 ... x_n y_1 ... y_m)
     * p[x_1 ... x_n]) (forall (x_1 ... x_n) p[x_1 ... x_n]))
     * 
     * It is used to justify the elimination of unused variables. This proof
     * object has no antecedents. 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofElimUnusedVars()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_ELIM_UNUSED_VARS;
    }

    /**
     * Indicates whether the term is a proof for destructive equality resolution
     * Remarks:  A proof for destructive equality resolution: (iff (forall (x)
     * (or (not (= x t)) P[x])) P[t]) if x does not occur in t.
     * 
     * This proof object has no antecedents.
     * 
     * Several variables can be eliminated simultaneously. 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofDER()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_DER;
    }

    /**
     * Indicates whether the term is a proof for quantifier instantiation
     * 
     * Remarks:  A proof of (or (not (forall (x) (P x))) (P a)) 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofQuantInst()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_QUANT_INST;
    }

    /**
     * Indicates whether the term is a hypothesis marker.
     * Remarks: Mark a
     * hypothesis in a natural deduction style proof.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofHypothesis()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_HYPOTHESIS;
    }

    /**
     * Indicates whether the term is a proof by lemma
     * Remarks:  T1: false [lemma
     * T1]: (or (not l_1) ... (not l_n))
     * 
     * This proof object has one antecedent: a hypothetical proof for false. It
     * converts the proof in a proof for (or (not l_1) ... (not l_n)), when T1
     * contains the hypotheses: l_1, ..., l_n. 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofLemma()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_LEMMA;
    }

    /**
     * Indicates whether the term is a proof by unit resolution 
     * Remarks:  T1: * (or l_1 ... l_n l_1' ... l_m') T2: (not l_1) ... T(n+1): (not l_n) * [unit-resolution T1 ... T(n+1)]: (or l_1' ... l_m') 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofUnitResolution()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_UNIT_RESOLUTION;
    }

    /**
     * Indicates whether the term is a proof by iff-true
     * Remarks:  T1: p
     * [iff-true T1]: (iff p true) 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofIFFTrue()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_IFF_TRUE;
    }

    /**
     * Indicates whether the term is a proof by iff-false
     * Remarks:  T1: (not p)
     * [iff-false T1]: (iff p false) 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofIFFFalse()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_IFF_FALSE;
    }

    /**
     * Indicates whether the term is a proof by commutativity
     * Remarks:  [comm]:
     * (= (f a b) (f b a))
     * 
     * f is a commutative operator.
     * 
     * This proof object has no antecedents. Remark: if f is bool, then = is
     * iff. 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofCommutativity()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_COMMUTATIVITY;
    }

    /**
     * Indicates whether the term is a proof for Tseitin-like axioms
     * Remarks: 
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
     * 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofDefAxiom()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_DEF_AXIOM;
    }

    /**
     * Indicates whether the term is a proof for introduction of a name
     * Remarks:  Introduces a name for a formula/term. Suppose e is an
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
     * Otherwise: [def-intro]: (= n e) 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofDefIntro()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_DEF_INTRO;
    }

    /**
     * Indicates whether the term is a proof for application of a definition
     * Remarks:  [apply-def T1]: F ~ n F is 'equivalent' to n, given that T1 is
     * a proof that n is a name for F. 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofApplyDef()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_APPLY_DEF;
    }

    /**
     * Indicates whether the term is a proof iff-oeq
     * Remarks:  T1: (iff p q)
     * [iff~ T1]: (~ p q) 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofIFFOEQ()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_IFF_OEQ;
    }

    /**
     * Indicates whether the term is a proof for a positive NNF step
     * Remarks: 
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
     * Boolean connectives 'and' and 'or'. 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofNNFPos()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_NNF_POS;
    }

    /**
     * Indicates whether the term is a proof for a negative NNF step
     * Remarks: 
     * Proof for a (negative) NNF step. Examples:
     * 
     * T1: (not s_1) ~ r_1 ... Tn: (not s_n) ~ r_n [nnf-neg T1 ... Tn]: (not
     * (and s_1 ... s_n)) ~ (or r_1 ... r_n) and T1: (not s_1) ~ r_1 ... Tn:
     * (not s_n) ~ r_n [nnf-neg T1 ... Tn]: (not (or s_1 ... s_n)) ~ (and r_1
     * ... r_n) and T1: (not s_1) ~ r_1 T2: (not s_2) ~ r_2 T3: s_1 ~ r_1' T4:
     * s_2 ~ r_2' [nnf-neg T1 T2 T3 T4]: (~ (not (iff s_1 s_2)) (and (or r_1
     * r_2) (or r_1' r_2'))) 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofNNFNeg()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_NNF_NEG;
    }


    /**
     * Indicates whether the term is a proof for a Skolemization step
     * Remarks: 
     * Proof for:
     * 
     * [sk]: (~ (not (forall x (p x y))) (not (p (sk y) y))) [sk]: (~ (exists x
     * (p x y)) (p (sk y) y))
     * 
     * This proof object has no antecedents. 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofSkolemize()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_SKOLEMIZE;
    }

    /**
     * Indicates whether the term is a proof by modus ponens for
     * equi-satisfiability.
     * Remarks:  Modus ponens style rule for
     * equi-satisfiability. T1: p T2: (~ p q) [mp~ T1 T2]: q 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofModusPonensOEQ()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_MODUS_PONENS_OEQ;
    }

    /**
     * Indicates whether the term is a proof for theory lemma
     * Remarks:  Generic
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
     * arithmetic lemma that uses a gcd test. 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isProofTheoryLemma()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_TH_LEMMA;
    }

    /**
     * Indicates whether the term is of an array sort.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isRelation()
    {
        return (Native.isApp(getContext().nCtx(), getNativeObject()) && Native
                .getSortKind(getContext().nCtx(),
                        Native.getSort(getContext().nCtx(), getNativeObject())) == Z3_sort_kind.Z3_RELATION_SORT
                .toInt());
    }

    /**
     * Indicates whether the term is an relation store
     * Remarks:  Insert a record
     * into a relation. The function takes {@code n+1} arguments, where the
     * first argument is the relation and the remaining {@code n} elements
     * correspond to the {@code n} columns of the relation. 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isRelationStore()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_STORE;
    }

    /**
     * Indicates whether the term is an empty relation
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isEmptyRelation()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_EMPTY;
    }

    /**
     * Indicates whether the term is a test for the emptiness of a relation
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isIsEmptyRelation()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_IS_EMPTY;
    }

    /**
     * Indicates whether the term is a relational join
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isRelationalJoin()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_JOIN;
    }

    /**
     * Indicates whether the term is the union or convex hull of two relations.
     * 
     * Remarks: The function takes two arguments.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isRelationUnion()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_UNION;
    }

    /**
     * Indicates whether the term is the widening of two relations
     * Remarks: The
     * function takes two arguments.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isRelationWiden()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_WIDEN;
    }

    /**
     * Indicates whether the term is a projection of columns (provided as
     * numbers in the parameters).
     * Remarks: The function takes one
     * argument.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isRelationProject()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_PROJECT;
    }

    /**
     * Indicates whether the term is a relation filter
     * Remarks:  Filter
     * (restrict) a relation with respect to a predicate. The first argument is
     * a relation. The second argument is a predicate with free de-Bruijn
     * indices corresponding to the columns of the relation. So the first column
     * in the relation has index 0. 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isRelationFilter()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_FILTER;
    }

    /**
     * Indicates whether the term is an intersection of a relation with the
     * negation of another.
     * Remarks:  Intersect the first relation with respect
     * to negation of the second relation (the function takes two arguments).
     * Logically, the specification can be described by a function
     * 
     * target = filter_by_negation(pos, neg, columns)
     * 
     * where columns are pairs c1, d1, .., cN, dN of columns from pos and neg,
     * such that target are elements in x in pos, such that there is no y in neg
     * that agrees with x on the columns c1, d1, .., cN, dN. 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isRelationNegationFilter()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_NEGATION_FILTER;
    }

    /**
     * Indicates whether the term is the renaming of a column in a relation
     * Remarks:  The function takes one argument. The parameters contain the
     * renaming as a cycle. 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isRelationRename()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_RENAME;
    }

    /**
     * Indicates whether the term is the complement of a relation
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isRelationComplement()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_COMPLEMENT;
    }

    /**
     * Indicates whether the term is a relational select
     * Remarks:  Check if a
     * record is an element of the relation. The function takes {@code n+1}
     * arguments, where the first argument is a relation, and the remaining
     * {@code n} arguments correspond to a record. 
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isRelationSelect()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_SELECT;
    }

    /**
     * Indicates whether the term is a relational clone (copy)
     * Remarks:  Create
     * a fresh copy (clone) of a relation. The function is logically the
     * identity, but in the context of a register machine allows for terms of
     * kind {@code isRelationUnion} to perform destructive updates to
     * the first argument.
     * @see #isRelationUnion
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isRelationClone()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_RA_CLONE;
    }

    /**
     * Indicates whether the term is of an array sort.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isFiniteDomain()
    {
        return (Native.isApp(getContext().nCtx(), getNativeObject()) && Native
                .getSortKind(getContext().nCtx(),
                        Native.getSort(getContext().nCtx(), getNativeObject())) == Z3_sort_kind.Z3_FINITE_DOMAIN_SORT
                .toInt());
    }

    /**
     * Indicates whether the term is a less than predicate over a finite domain.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isFiniteDomainLT()
    {
        return isApp() && getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_FD_LT;
    }

    /**
     * The de-Bruijn index of a bound variable.
     * Remarks:  Bound variables are
     * indexed by de-Bruijn indices. It is perhaps easiest to explain the
     * meaning of de-Bruijn indices by indicating the compilation process from
     * non-de-Bruijn formulas to de-Bruijn format. {@code 
     * abs(forall (x1) phi) = forall (x1) abs1(phi, x1, 0)
     * abs(forall (x1, x2) phi) = abs(forall (x1) abs(forall (x2) phi))
     * abs1(x, x, n) = b_n
     * abs1(y, x, n) = y
     * abs1(f(t1,...,tn), x, n) = f(abs1(t1,x,n), ..., abs1(tn,x,n))
     * abs1(forall (x1) phi, x, n) = forall (x1) (abs1(phi, x, n+1))
     * } The last line is significant: the index of a bound variable is
     * different depending on the scope in which it appears. The deeper x
     * appears, the higher is its index. 
     * @throws Z3Exception on error
     * @return an int
     **/
    public int getIndex()
    {
        if (!isVar()) {
            throw new Z3Exception("Term is not a bound variable.");
        }

        return Native.getIndexValue(getContext().nCtx(), getNativeObject());
    }

    /**
     * Constructor for Expr
     * @throws Z3Exception on error
     **/
    protected Expr(Context ctx, long obj) {
        super(ctx, obj);
    }

    @Override
    void checkNativeObject(long obj) {
        if (!Native.isApp(getContext().nCtx(), obj) && 
            Native.getAstKind(getContext().nCtx(), obj) != Z3_ast_kind.Z3_VAR_AST.toInt() &&
            Native.getAstKind(getContext().nCtx(), obj) != Z3_ast_kind.Z3_QUANTIFIER_AST.toInt()) {
            throw new Z3Exception("Underlying object is not a term");
        }
        super.checkNativeObject(obj);
    }

    static Expr create(Context ctx, FuncDecl f, Expr ... arguments)
           
    {
        long obj = Native.mkApp(ctx.nCtx(), f.getNativeObject(),
                AST.arrayLength(arguments), AST.arrayToNative(arguments));
        return create(ctx, obj);
    }

    static Expr create(Context ctx, long obj)
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
            case Z3_FLOATING_POINT_SORT:
                return new FPNum(ctx, obj);
            case Z3_ROUNDING_MODE_SORT:
                return new FPRMNum(ctx, obj);
            case Z3_FINITE_DOMAIN_SORT:
                return new FiniteDomainNum(ctx, obj);
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
        case Z3_FLOATING_POINT_SORT:
            return new FPExpr(ctx, obj);
        case Z3_ROUNDING_MODE_SORT:
            return new FPRMExpr(ctx, obj);
        case Z3_FINITE_DOMAIN_SORT:
            return new FiniteDomainExpr(ctx, obj);
        case Z3_SEQ_SORT:
            return new SeqExpr(ctx, obj);
        case Z3_RE_SORT:
            return new ReExpr(ctx, obj);
        default: ;
        }

        return new Expr(ctx, obj);
    }
}
