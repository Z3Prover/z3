#!/usr/bin/env python
"""
Reads a list of Z3 API header files and
generate the constant declarations need
by one or more Z3 language bindings
"""
import mk_genfile_common
import argparse
import logging
import os
import sys


def main(args):
    logging.basicConfig(level=logging.INFO)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("api_files", nargs="+")
    parser.add_argument("--z3py-output-dir", dest="z3py_output_dir", default=None)
    parser.add_argument("--dotnet-output-dir", dest="dotnet_output_dir", default=None)
    parser.add_argument("--java-output-dir", dest="java_output_dir", default=None)
    parser.add_argument("--java-package-name",
                        dest="java_package_name",
                        default=None,
                        help="Name to give the Java package (e.g. ``com.microsoft.z3``).")
    pargs = parser.parse_args(args)

    if not mk_genfile_common.check_files_exist(pargs.api_files):
        logging.error('One or more API files do not exist')
        return 1

    count = 0

    if pargs.z3py_output_dir:
        if not mk_genfile_common.check_dir_exists(pargs.z3py_output_dir):
            return 1
        output = mk_genfile_common.mk_z3consts_py_internal(pargs.api_files, pargs.z3py_output_dir)
        logging.info('Generated "{}"'.format(output))
        count += 1

    if pargs.dotnet_output_dir:
        if not mk_genfile_common.check_dir_exists(pargs.dotnet_output_dir):
            return 1
        output = mk_genfile_common.mk_z3consts_dotnet_internal(
            pargs.api_files,
            pargs.dotnet_output_dir)
        logging.info('Generated "{}"'.format(output))
        count += 1

    if pargs.java_output_dir:
        if pargs.java_package_name == None:
            logging.error('Java package name must be specified')
            return 1
        if not mk_genfile_common.check_dir_exists(pargs.java_output_dir):
            return 1
        outputs = mk_genfile_common.mk_z3consts_java_internal(
            pargs.api_files,
            pargs.java_package_name,
            pargs.java_output_dir)
        for generated_file in outputs:
            logging.info('Generated "{}"'.format(generated_file))
        count += 1

    if count == 0:
        logging.info('No files generated. You need to specific an output directory'
                     ' for the relevant langauge bindings')
    # TODO: Add support for other bindings
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
