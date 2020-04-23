#!/usr/bin/env python
"""
Determines the available tactics from a list of header files and generates a
``install_tactic.cpp`` file in the destination directory that defines a
function ``void install_tactics(tactic_manager& ctx)``.
"""
import mk_genfile_common
import argparse
import logging
import os
import sys

def main(args):
    logging.basicConfig(level=logging.INFO)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination_dir", help="destination directory")
    parser.add_argument("deps", help="file with header file names to parse")
    pargs = parser.parse_args(args)

    if not mk_genfile_common.check_dir_exists(pargs.destination_dir):
        return 1

    if not mk_genfile_common.check_files_exist([pargs.deps]):
        return 1

    with open(pargs.deps, 'r') as f:
        lines = f.read().split('\n')
        h_files_full_path = [os.path.abspath(header_file)
                                for header_file in lines if header_file]

    if not mk_genfile_common.check_files_exist(h_files_full_path):
        return 1

    output = mk_genfile_common.mk_install_tactic_cpp_internal(
        h_files_full_path,
        pargs.destination_dir
    )
    logging.info('Generated "{}"'.format(output))
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
