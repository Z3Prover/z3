/**
 * This file was automatically generated from Version.cs 
 **/

package com.Microsoft.Z3;

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
        public  Integer Major() 
            {
                Integer major = 0, minor = 0, build = 0, revision = 0;
                Native.getVersion(major, minor, build, revision);
                return major;
        }

        /**
         * The minor version
         **/
        public  Integer Minor() 
            {
                Integer major = 0, minor = 0, build = 0, revision = 0;
                Native.getVersion(major, minor, build, revision);
                return minor;
        }

        /**
         * The build version
         **/
        public  Integer Build() 
            {
                Integer major = 0, minor = 0, build = 0, revision = 0;
                Native.getVersion(major, minor, build, revision);
                return build;
        }

        /**
         * The revision
         **/
        public  Integer Revision() 
            {
                Integer major = 0, minor = 0, build = 0, revision = 0;
                Native.getVersion(major, minor, build, revision);
                return revision;
        }

        /**
         * A string representation of the version information.
         **/
        public  String toString()
        {
            

            Integer major = 0, minor = 0, build = 0, revision = 0;
            Native.getVersion(major, minor, build, revision);
            return major.toString() + "." + minor.toString() + "." + build.toString() + "." + revision.toString();
        }
    }
