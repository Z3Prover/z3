#!/usr/bin/env python
"""
Scans the listed header files for
memory initializers and finalizers and
emits and implementation of
``void mem_initialize()`` and
``void mem_finalize()`` into ``mem_initializer.cpp``
in the destination directory.
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
    parser.add_argument("header_files", nargs="+",
                        help="One or more header files to parse")
    pargs = parser.parse_args(args)

    if not mk_genfile_common.check_dir_exists(pargs.destination_dir):
        return 1

    h_files_full_path = []
    for header_file in pargs.header_files:
        h_files_full_path.append(os.path.abspath(header_file))

    output = mk_genfile_common.mk_mem_initializer_cpp_internal(
        h_files_full_path,
        pargs.destination_dir
    )
    logging.info('Generated "{}"'.format(output))
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))

