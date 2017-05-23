/*++
Copyright (<c>) 2016 Microsoft Corporation

Module Name:

    Contracts.cs

Abstract:

    Z3 Managed API: Dummy Code Contracts class for .NET
    frameworks that don't support them (e.g., CoreCLR).

Author:

    Christoph Wintersteiger (cwinter) 2016-10-06

Notes:

--*/

namespace System.Diagnostics.Contracts
{
    public class ContractClass : Attribute
    {
        public ContractClass(Type t) { }
    }

    public class ContractClassFor : Attribute
    {
        public ContractClassFor(Type t) { }
    }

    public class ContractInvariantMethod : Attribute
    {
        public ContractInvariantMethod() { }
    }

    public class ContractVerification : Attribute
    {
        public ContractVerification(bool b) { }
    }

    public class Pure : Attribute { }

    public static class Contract
    {
        [Conditional("false")]
        public static void Ensures(bool b) { }
        [Conditional("false")]
        public static void Requires(bool b) { }
        [Conditional("false")]
        public static void Assume(bool b, string msg) { }
        [Conditional("false")]
        public static void Assert(bool b) { }
        public static bool ForAll(bool b) { return true; }
        public static bool ForAll(Object c, Func<Object, bool> p) { return true; }
        public static bool ForAll(int from, int to, Predicate<int> p) { return true; }
        [Conditional("false")]
        public static void Invariant(bool b) { }
        public static T[] Result<T>() { return new T[1]; }
        [Conditional("false")]
        public static void EndContractBlock() { }
        public static T ValueAtReturn<T>(out T v) { T[] t = new T[1]; v = t[0]; return v; }
    }
}
