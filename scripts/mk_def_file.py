#  - /usr/bin/env python
"""
Reads a list of Z3 API header files and
generate a ``.def`` file to define the
exported symbols of a dll. This file
can be passed to the ``/DEF`` to the
linker used by MSVC.
"""
import mk_genfile_common
import argparse
import logging
import os
import sys

def main(args):
    logging.basicConfig(level=logging.INFO)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output_file", help="output def file path")
    parser.add_argument("dllname", help="dllname to use in def file")
    parser.add_argument("api_files", nargs="+")
    pargs = parser.parse_args(args)

    if not mk_genfile_common.check_files_exist(pargs.api_files):
        logging.error('One or more api files do not exist')
        return 1

    mk_genfile_common.mk_def_file_internal(
        pargs.output_file,
        pargs.dllname,
        pargs.api_files)
    logging.info('Generated "{}"'.format(pargs.output_file))
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))

