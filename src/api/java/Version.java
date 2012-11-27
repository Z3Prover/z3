/**
 * This file was automatically generated from Version.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.Microsoft.Z3;

/**
 * Version information. <remarks>Note that this class is static.</remarks>
 **/
public final class Version
{
    Version()
    {
    }

    /**
     * The major version
     **/
    public int Major()
    {
        Native.IntPtr major = new Native.IntPtr(), minor = new Native.IntPtr(), build = new Native.IntPtr(), revision = new Native.IntPtr();
        Native.getVersion(major, minor, build, revision);
        return major.value;
    }

    /**
     * The minor version
     **/
    public int Minor()
    {
        Native.IntPtr major = new Native.IntPtr(), minor = new Native.IntPtr(), build = new Native.IntPtr(), revision = new Native.IntPtr();
        Native.getVersion(major, minor, build, revision);
        return minor.value;
    }

    /**
     * The build version
     **/
    public int Build()
    {
        Native.IntPtr major = new Native.IntPtr(), minor = new Native.IntPtr(), build = new Native.IntPtr(), revision = new Native.IntPtr();
        Native.getVersion(major, minor, build, revision);
        return build.value;
    }

    /**
     * The revision
     **/
    public int Revision()
    {
        Native.IntPtr major = new Native.IntPtr(), minor = new Native.IntPtr(), build = new Native.IntPtr(), revision = new Native.IntPtr();
        Native.getVersion(major, minor, build, revision);
        return revision.value;
    }

    /**
     * A string representation of the version information.
     **/
    public String toString()
    {
        Native.IntPtr major = new Native.IntPtr(), minor = new Native.IntPtr(), build = new Native.IntPtr(), revision = new Native.IntPtr();
        Native.getVersion(major, minor, build, revision);
        return Integer.toString(major.value) + "." + Integer.toString(minor.value) + "."
                + Integer.toString(build.value) + "." + Integer.toString(revision.value);
    }
}
