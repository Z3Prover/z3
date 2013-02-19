/**
 * This file was automatically generated from FuncInterp.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * A function interpretation is represented as a finite map and an 'else' value.
 * Each entry in the finite map represents the value of a function given a set
 * of arguments.
 **/
public class FuncInterp extends Z3Object
{
	/**
	 * An Entry object represents an element in the finite map used to encode a
	 * function interpretation.
	 **/
	public class Entry extends Z3Object
	{
		/**
		 * Return the (symbolic) value of this entry.
		 * 
		 * @throws Z3Exception
		 **/
		public Expr getValue() throws Z3Exception
		{
			return Expr.create(getContext(),
					Native.funcEntryGetValue(getContext().nCtx(), getNativeObject()));
		}

		/**
		 * The number of arguments of the entry.
		 **/
		public int getNumArgs() throws Z3Exception
		{
			return Native.funcEntryGetNumArgs(getContext().nCtx(), getNativeObject());
		}

		/**
		 * The arguments of the function entry.
		 * 
		 * @throws Z3Exception
		 **/
		public Expr[] getArgs() throws Z3Exception
		{
			int n = getNumArgs();
			Expr[] res = new Expr[n];
			for (int i = 0; i < n; i++)
				res[i] = Expr.create(getContext(), Native.funcEntryGetArg(
						getContext().nCtx(), getNativeObject(), i));
			return res;
		}

		/**
		 * A string representation of the function entry.
		 **/
		public String toString()
		{
			try
			{
				int n = getNumArgs();
				String res = "[";
				Expr[] args = getArgs();
				for (int i = 0; i < n; i++)
					res += args[i] + ", ";
				return res + getValue() + "]";
			} catch (Z3Exception e)
			{
				return new String("Z3Exception: " + e.getMessage());
			}
		}

		Entry(Context ctx, long obj) throws Z3Exception
		{
			super(ctx, obj);
		}

		void incRef(long o) throws Z3Exception
		{
			getContext().funcEntry_DRQ().incAndClear(getContext(), o);
			super.incRef(o);
		}

		void decRef(long o) throws Z3Exception
		{
			getContext().funcEntry_DRQ().add(o);
			super.decRef(o);
		}
	};

	/**
	 * The number of entries in the function interpretation.
	 **/
	public int getNumEntries() throws Z3Exception
	{
		return Native.funcInterpGetNumEntries(getContext().nCtx(), getNativeObject());
	}

	/**
	 * The entries in the function interpretation
	 * 
	 * @throws Z3Exception
	 **/
	public Entry[] getEntries() throws Z3Exception
	{
		int n = getNumEntries();
		Entry[] res = new Entry[n];
		for (int i = 0; i < n; i++)
			res[i] = new Entry(getContext(), Native.funcInterpGetEntry(getContext()
					.nCtx(), getNativeObject(), i));
		return res;
	}

	/**
	 * The (symbolic) `else' value of the function interpretation.
	 * 
	 * @throws Z3Exception
	 **/
	public Expr getElse() throws Z3Exception
	{
		return Expr.create(getContext(),
				Native.funcInterpGetElse(getContext().nCtx(), getNativeObject()));
	}

	/**
	 * The arity of the function interpretation
	 **/
	public int getArity() throws Z3Exception
	{
		return Native.funcInterpGetArity(getContext().nCtx(), getNativeObject());
	}

	/**
	 * A string representation of the function interpretation.
	 **/
	public String toString()
	{
		try
		{
			String res = "";
			res += "[";
			for (Entry e : getEntries())
			{
				int n = e.getNumArgs();
				if (n > 1)
					res += "[";
				Expr[] args = e.getArgs();
				for (int i = 0; i < n; i++)
				{
					if (i != 0)
						res += ", ";
					res += args[i];
				}
				if (n > 1)
					res += "]";
				res += " -> " + e.getValue() + ", ";
			}
			res += "else -> " + getElse();
			res += "]";
			return res;
		} catch (Z3Exception e)
		{
			return new String("Z3Exception: " + e.getMessage());
		}
	}

	FuncInterp(Context ctx, long obj) throws Z3Exception
	{
		super(ctx, obj);
	}

	void incRef(long o) throws Z3Exception
	{
		getContext().funcInterp_DRQ().incAndClear(getContext(), o);
		super.incRef(o);
	}

	void decRef(long o) throws Z3Exception
	{
		getContext().funcInterp_DRQ().add(o);
		super.decRef(o);
	}
}
