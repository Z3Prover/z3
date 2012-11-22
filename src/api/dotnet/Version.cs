/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Version.cs

Abstract:

    Z3 Managed API: Version information

Author:

    Christoph Wintersteiger (cwinter) 2012-03-16

Notes:
    
--*/

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// Version information.
    /// </summary>
    /// <remarks>Note that this class is static.</remarks>
    [ContractVerification(true)]
    public static class Version
    {
        static Version() { }

        /// <summary>
        /// The major version
        /// </summary>
        public static uint Major
        {
            get
            {
                uint major = 0, minor = 0, build = 0, revision = 0;
                Native.Z3_get_version(ref major, ref minor, ref build, ref revision);
                return major;
            }
        }

        /// <summary>
        /// The minor version
        /// </summary>
        public static uint Minor
        {
            get
            {
                uint major = 0, minor = 0, build = 0, revision = 0;
                Native.Z3_get_version(ref major, ref minor, ref build, ref revision);
                return minor;
            }
        }

        /// <summary>
        /// The build version
        /// </summary>
        public static uint Build
        {
            get
            {
                uint major = 0, minor = 0, build = 0, revision = 0;
                Native.Z3_get_version(ref major, ref minor, ref build, ref revision);
                return build;
            }
        }

        /// <summary>
        /// The revision
        /// </summary>
        public static uint Revision
        {
            get
            {
                uint major = 0, minor = 0, build = 0, revision = 0;
                Native.Z3_get_version(ref major, ref minor, ref build, ref revision);
                return revision;
            }
        }

        /// <summary>
        /// A string representation of the version information.
        /// </summary>
        new public static string ToString()
        {
            Contract.Ensures(Contract.Result<string>() != null);

            uint major = 0, minor = 0, build = 0, revision = 0;
            Native.Z3_get_version(ref major, ref minor, ref build, ref revision);
            return major.ToString() + "." + minor.ToString() + "." + build.ToString() + "." + revision.ToString();
        }
    }
}
