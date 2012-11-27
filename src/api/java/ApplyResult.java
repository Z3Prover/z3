/**
 * This file was automatically generated from ApplyResult.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.Microsoft.Z3;

/**
 * ApplyResult objects represent the result of an application of a tactic to a
 * goal. It contains the subgoals that were produced.
 **/
public class ApplyResult extends Z3Object
{
	/**
	 * The number of Subgoals.
	 **/
	public int NumSubgoals()
	{
		return Native.applyResultGetNumSubgoals(Context().nCtx(),
				NativeObject());
	}

	/**
	 * Retrieves the subgoals from the ApplyResult.
	 * @throws Z3Exception 
	 **/
	public Goal[] Subgoals() throws Z3Exception
	{
	    int n = NumSubgoals();
		Goal[] res = new Goal[n];
		for (int i = 0; i < n; i++)
			res[i] = new Goal(Context(), Native.applyResultGetSubgoal(Context()
					.nCtx(), NativeObject(), i));
		return res;
	}

	/**
	 * Convert a model for the subgoal <paramref name="i"/> into a model for the
	 * original goal <code>g</code>, that the ApplyResult was obtained from.
	 * 
	 * @return A model for <code>g</code>
	 * @throws Z3Exception 
	 **/
	public Model ConvertModel(int i, Model m) throws Z3Exception
	{
		return new Model(Context(), Native.applyResultConvertModel(Context()
				.nCtx(), NativeObject(), i, m.NativeObject()));
	}

	/**
	 * A string representation of the ApplyResult.
	 **/
	public String toString()
	{
		return Native.applyResultToString(Context().nCtx(), NativeObject());
	}

	ApplyResult(Context ctx, long obj) throws Z3Exception
	{
		super(ctx, obj);
	}

	void IncRef(long o) throws Z3Exception
	{
		Context().ApplyResult_DRQ().IncAndClear(Context(), o);
		super.IncRef(o);
	}

	void DecRef(long o) throws Z3Exception
	{
		Context().ApplyResult_DRQ().Add(o);
		super.DecRef(o);
	}
}
