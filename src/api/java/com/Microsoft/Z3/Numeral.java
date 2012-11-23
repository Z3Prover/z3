/**
 * This file was automatically generated from Numeral.cs 
 **/

package com.Microsoft.Z3;
/* using System; */

/* using System.Numerics; */

    /**
     * Integer Numerals
     **/
    public class IntNum extends IntExpr
    {

        IntNum(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }


        /**
         * Retrieve the 64-bit unsigned integer value.
         **/
        public UInt64 UInt64() 
            {
                UInt64 res = 0;
                if (Native.getNumeralLong64(Context.nCtx, NativeObject, res) == 0)
                    throw new Z3Exception("Numeral is not a 64 bit unsigned");
                return res;
            }

        /**
         * Retrieve the int value.
         **/
        public int Int() 
            {
                int res = 0;
                if (Native.getNumeralInt(Context.nCtx, NativeObject, res) == 0)
                    throw new Z3Exception("Numeral is not an int");
                return res;
            }

        /**
         * Retrieve the 64-bit int value.
         **/
        public Int64 Int64() 
            {
                Int64 res = 0;
                if (Native.getNumeralInt64(Context.nCtx, NativeObject, res) == 0)
                    throw new Z3Exception("Numeral is not an int64");
                return res;
            }

        /**
         * Retrieve the int value.
         **/
        public long UInt() 
            {
                long res = 0;
                if (Native.getNumeralLong(Context.nCtx, NativeObject, res) == 0)
                    throw new Z3Exception("Numeral is not a long");
                return res;
            }

        /**
         * Retrieve the BigInteger value.
         **/
        public BigInteger BigInteger() 
            {  
                return BigInteger.Parse(this.toString());
            }

        /**
         * Returns a string representation of the numeral.
         **/
        public String toString()
        {
            return Native.getNumeralString(Context.nCtx, NativeObject);
        }
    }

    /**
     * Rational Numerals
     **/
    public class RatNum extends RealExpr
    {
        /**
         * The numerator of a rational numeral.
         **/
        public IntNum Numerator()  {
                

                return new IntNum(Context, Native.getNumerator(Context.nCtx, NativeObject)); }
        }

        /**
         * The denominator of a rational numeral.
         **/
        public IntNum Denominator()  {
                

                return new IntNum(Context, Native.getDenominator(Context.nCtx, NativeObject)); }
        }

        /**
         * Converts the numerator of the rational to a BigInteger
         **/
        public BigInteger BigIntNumerator() 
            {                
                IntNum n = Numerator;
                return BigInteger.Parse(n.toString());
            }

        /**
         * Converts the denominator of the rational to a BigInteger
         **/
        public BigInteger BigIntDenominator() 
            {
                IntNum n = Denominator;
                return BigInteger.Parse(n.toString());
            }

        /**
         * Returns a string representation in decimal notation.
         * <remarks>The result has at most <paramref name="precision"/> decimal places.</remarks>    
         **/
        public String ToDecimalString(long precision)
        {
            return Native.getNumeralDecimalString(Context.nCtx, NativeObject, precision);
        }

        /**
         * Returns a string representation of the numeral.
         **/
        public String toString()
        {
            return Native.getNumeralString(Context.nCtx, NativeObject);
        }

        RatNum(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }
    }


    /**
     * Bit-vector numerals
     **/
    public class BitVecNum extends BitVecExpr
    {
        /**
         * Retrieve the 64-bit unsigned integer value.
         **/
        public UInt64 UInt64() 
            {
                UInt64 res = 0;
                if (Native.getNumeralLong64(Context.nCtx, NativeObject, res) == 0)
                    throw new Z3Exception("Numeral is not a 64 bit unsigned");
                return res;
            }

        /**
         * Retrieve the int value.
         **/
        public int Int() 
            {
                int res = 0;
                if (Native.getNumeralInt(Context.nCtx, NativeObject, res) == 0)
                    throw new Z3Exception("Numeral is not an int");
                return res;
            }

        /**
         * Retrieve the 64-bit int value.
         **/
        public Int64 Int64() 
            {
                Int64 res = 0;
                if (Native.getNumeralInt64(Context.nCtx, NativeObject, res) == 0)
                    throw new Z3Exception("Numeral is not an int64");
                return res;
            }

        /**
         * Retrieve the int value.
         **/
        public long UInt() 
            {
                long res = 0;
                if (Native.getNumeralLong(Context.nCtx, NativeObject, res) == 0)
                    throw new Z3Exception("Numeral is not a long");
                return res;
            }

        /**
         * Retrieve the BigInteger value.
         **/
        public BigInteger BigInteger() 
            {
                return BigInteger.Parse(this.toString());
            }

        /**
         * Returns a string representation of the numeral.
         **/
        public String toString()
        {
            return Native.getNumeralString(Context.nCtx, NativeObject);
        }

        BitVecNum(Context ctx, IntPtr obj) { super(ctx, obj);  }
    }

    /**
     * Algebraic numbers
     **/
    public class AlgebraicNum extends ArithExpr
    {
        /**
         * Return a upper bound for a given real algebraic number. 
         * The interval isolating the number is smaller than 1/10^<paramref name="precision"/>.    
         * <seealso cref="Expr.IsAlgebraicNumber"/>   
         * <param name="precision">the precision of the result</param>
         * @return A numeral Expr of sort Real
         **/
        public RatNum ToUpper(long precision)
        {
            

            return new RatNum(Context, Native.getAlgebraicNumberUpper(Context.nCtx, NativeObject, precision));
        }

        /**
         * Return a lower bound for the given real algebraic number. 
         * The interval isolating the number is smaller than 1/10^<paramref name="precision"/>.    
         * <seealso cref="Expr.IsAlgebraicNumber"/>
         * <param name="precision"></param>
         * @return A numeral Expr of sort Real
         **/
        public RatNum ToLower(long precision)
        {
            

            return new RatNum(Context, Native.getAlgebraicNumberLower(Context.nCtx, NativeObject, precision));
        }

        /**
         * Returns a string representation in decimal notation.
         * <remarks>The result has at most <paramref name="precision"/> decimal places.</remarks>    
         **/
        public String ToDecimal(long precision)
        {
            

            return Native.getNumeralDecimalString(Context.nCtx, NativeObject, precision);
        }

        AlgebraicNum(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }
    }
