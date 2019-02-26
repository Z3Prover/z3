/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Exception.cs

Abstract:

    Z3 Managed API: Exceptions

Author:

    Christoph Wintersteiger (cwinter) 2012-03-15

Notes:

--*/

using System.Diagnostics;
using System;

namespace Microsoft.Z3
{
    /// <summary>
    /// The exception base class for error reporting from Z3
    /// </summary>
#if !DOTNET_CORE
  [Serializable]
#endif
    public class Z3Exception : Exception
  {
    /// <summary>
    /// Constructor.
    /// </summary>
    public Z3Exception() : base() { }

    /// <summary>
    /// Constructor.
    /// </summary>
    public Z3Exception(string message) : base(message) { }

    /// <summary>
    /// Constructor.
    /// </summary>
    public Z3Exception(string message, System.Exception inner) : base(message, inner) { }
  }
}
