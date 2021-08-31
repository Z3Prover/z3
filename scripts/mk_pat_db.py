# -- /usr/bin/env python
"""
Reads a pattern database and generates the corresponding
header file.
"""
import mk_genfile_common
import argparse
import logging
import os
import sys

def main(args):
    logging.basicConfig(level=logging.INFO)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("db_file", help="pattern database file")
    parser.add_argument("output_file", help="output header file path")
    pargs = parser.parse_args(args)

    if not os.path.exists(pargs.db_file):
        logging.error('"{}" does not exist'.format(pargs.db_file))
        return 1

    mk_genfile_common.mk_pat_db_internal(pargs.db_file, pargs.output_file)
    logging.info('Generated "{}"'.format(pargs.output_file))
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))

