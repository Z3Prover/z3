#!/usr/bin/env python
"""
Reads a pyg file and emits the corresponding
C++ header file into the specified destination
directory.
"""
import mk_genfile_common
import argparse
import logging
import os
import sys

def main(args):
    logging.basicConfig(level=logging.INFO)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pyg_file", help="pyg file")
    parser.add_argument("destination_dir", help="destination directory")
    pargs = parser.parse_args(args)

    if not os.path.exists(pargs.pyg_file):
        logging.error('"{}" does not exist'.format(pargs.pyg_file))
        return 1

    if not mk_genfile_common.check_dir_exists(pargs.destination_dir):
        return 1

    pyg_full_path = os.path.abspath(pargs.pyg_file)
    destination_dir_full_path = os.path.abspath(pargs.destination_dir)
    logging.info('Using {}'.format(pyg_full_path))
    output = mk_genfile_common.mk_hpp_from_pyg(pyg_full_path, destination_dir_full_path)
    logging.info('Generated "{}"'.format(output))
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))

