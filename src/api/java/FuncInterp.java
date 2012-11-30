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
		public Expr Value() throws Z3Exception
		{
			return Expr.Create(Context(),
					Native.funcEntryGetValue(Context().nCtx(), NativeObject()));
		}

		/**
		 * The number of arguments of the entry.
		 **/
		public int NumArgs() throws Z3Exception
		{
			return Native.funcEntryGetNumArgs(Context().nCtx(), NativeObject());
		}

		/**
		 * The arguments of the function entry.
		 * 
		 * @throws Z3Exception
		 **/
		public Expr[] Args() throws Z3Exception
		{
			int n = NumArgs();
			Expr[] res = new Expr[n];
			for (int i = 0; i < n; i++)
				res[i] = Expr.Create(Context(), Native.funcEntryGetArg(
						Context().nCtx(), NativeObject(), i));
			return res;
		}

		/**
		 * A string representation of the function entry.
		 **/
		public String toString()
		{
			try
			{
				int n = NumArgs();
				String res = "[";
				Expr[] args = Args();
				for (int i = 0; i < n; i++)
					res += args[i] + ", ";
				return res + Value() + "]";
			} catch (Z3Exception e)
			{
				return new String("Z3Exception: " + e.getMessage());
			}
		}

		Entry(Context ctx, long obj) throws Z3Exception
		{
			super(ctx, obj);
		}

		void IncRef(long o) throws Z3Exception
		{
			Context().FuncEntry_DRQ().IncAndClear(Context(), o);
			super.IncRef(o);
		}

		void DecRef(long o) throws Z3Exception
		{
			Context().FuncEntry_DRQ().Add(o);
			super.DecRef(o);
		}
	};

	/**
	 * The number of entries in the function interpretation.
	 **/
	public int NumEntries() throws Z3Exception
	{
		return Native.funcInterpGetNumEntries(Context().nCtx(), NativeObject());
	}

	/**
	 * The entries in the function interpretation
	 * 
	 * @throws Z3Exception
	 **/
	public Entry[] Entries() throws Z3Exception
	{
		int n = NumEntries();
		Entry[] res = new Entry[n];
		for (int i = 0; i < n; i++)
			res[i] = new Entry(Context(), Native.funcInterpGetEntry(Context()
					.nCtx(), NativeObject(), i));
		return res;
	}

	/**
	 * The (symbolic) `else' value of the function interpretation.
	 * 
	 * @throws Z3Exception
	 **/
	public Expr Else() throws Z3Exception
	{
		return Expr.Create(Context(),
				Native.funcInterpGetElse(Context().nCtx(), NativeObject()));
	}

	/**
	 * The arity of the function interpretation
	 **/
	public int Arity() throws Z3Exception
	{
		return Native.funcInterpGetArity(Context().nCtx(), NativeObject());
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
			for (Entry e : Entries())
			{
				int n = e.NumArgs();
				if (n > 1)
					res += "[";
				Expr[] args = e.Args();
				for (int i = 0; i < n; i++)
				{
					if (i != 0)
						res += ", ";
					res += args[i];
				}
				if (n > 1)
					res += "]";
				res += " -> " + e.Value() + ", ";
			}
			res += "else -> " + Else();
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

	void IncRef(long o) throws Z3Exception
	{
		Context().FuncInterp_DRQ().IncAndClear(Context(), o);
		super.IncRef(o);
	}

	void DecRef(long o) throws Z3Exception
	{
		Context().FuncInterp_DRQ().Add(o);
		super.DecRef(o);
	}
}
