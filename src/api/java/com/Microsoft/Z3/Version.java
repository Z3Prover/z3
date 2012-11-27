/**
 * This file was automatically generated from Version.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;
import com.Microsoft.Z3.Enumerations.*;

/* using System; */

    /**
     * Version information.
     * <remarks>Note that this class is static.</remarks>
     **/
    public final class Version
    {
         Version() { }

        /**
         * The major version
         **/
        public  int Major() 
            {
                int major = 0, minor = 0, build = 0, revision = 0;
                Native.getVersion(major, minor, build, revision);
                return major;
            }

        /**
         * The minor version
         **/
        public  int Minor() 
            {
                int major = 0, minor = 0, build = 0, revision = 0;
                Native.getVersion(major, minor, build, revision);
                return minor;
            }

        /**
         * The build version
         **/
        public  int Build() 
            {
                int major = 0, minor = 0, build = 0, revision = 0;
                Native.getVersion(major, minor, build, revision);
                return build;
            }

        /**
         * The revision
         **/
        public  int Revision() 
            {
                int major = 0, minor = 0, build = 0, revision = 0;
                Native.getVersion(major, minor, build, revision);
                return revision;
            }

        /**
         * A string representation of the version information.
         **/
        public  String toString()
        {
            

            int major = 0, minor = 0, build = 0, revision = 0;
            Native.getVersion(major, minor, build, revision);
            return Integer.toString(major) + "." + Integer.toString(minor) + "." + Integer.toString(build) + "." + Integer.toString(revision);
        }
    }
