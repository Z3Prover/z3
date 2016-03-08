#!/usr/bin/env python
"""
Determines the available tactics
in header files in the list of source directions
and generates a ``install_tactic.cpp`` file in
the destination directory that defines a function
``void install_tactics(tactic_manager& ctx)``.
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
    parser.add_argument("source_dirs", nargs="+",
                        help="One or more source directories to search")
    pargs = parser.parse_args(args)

    if not mk_genfile_common.check_dir_exists(pargs.destination_dir):
        return 1

    for source_dir in pargs.source_dirs:
        if not mk_genfile_common.check_dir_exists(source_dir):
            return 1

    output = mk_genfile_common.mk_install_tactic_cpp_internal(
        pargs.source_dirs,
        pargs.destination_dir
    )
    logging.info('Generated "{}"'.format(output))
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
