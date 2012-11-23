/**
 * This file was automatically generated from Version.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;

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
        public  long Major() 
            {
                long major = 0, minor = 0, build = 0, revision = 0;
                Native.getVersion(major, minor, build, revision);
                return major;
            }

        /**
         * The minor version
         **/
        public  long Minor() 
            {
                long major = 0, minor = 0, build = 0, revision = 0;
                Native.getVersion(major, minor, build, revision);
                return minor;
            }

        /**
         * The build version
         **/
        public  long Build() 
            {
                long major = 0, minor = 0, build = 0, revision = 0;
                Native.getVersion(major, minor, build, revision);
                return build;
            }

        /**
         * The revision
         **/
        public  long Revision() 
            {
                long major = 0, minor = 0, build = 0, revision = 0;
                Native.getVersion(major, minor, build, revision);
                return revision;
            }

        /**
         * A string representation of the version information.
         **/
        public  String toString()
        {
            

            long major = 0, minor = 0, build = 0, revision = 0;
            Native.getVersion(major, minor, build, revision);
            return major.ToString() + "." + minor.ToString() + "." + build.ToString() + "." + revision.ToString();
        }
    }
