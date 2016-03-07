#!/usr/bin/env python
"""
Reads a list of Z3 API header files and
generate the constant declarations need
by one or more Z3 language bindings
"""
import mk_util
import argparse
import logging
import os
import sys

def check_dir(output_dir):
  if not os.path.isdir(output_dir):
    logging.error('"{}" is not an existing directory'.format(output_dir))
    return 1
  return 0

def main(args):
  logging.basicConfig(level=logging.INFO)
  parser = argparse.ArgumentParser(description=__doc__)
  parser.add_argument("api_files", nargs="+")
  parser.add_argument("--z3py-output-dir", dest="z3py_output_dir", default=None)
  pargs = parser.parse_args(args)

  for api_file in pargs.api_files:
    if not os.path.exists(api_file):
      logging.error('"{}" does not exist'.format(api_file))
      return 1

  count = 0

  if pargs.z3py_output_dir:
    if check_dir(pargs.z3py_output_dir) != 0:
      return 1
    mk_util.mk_z3consts_py_internal(pargs.api_files, pargs.z3py_output_dir)
    count += 1

  if count == 0:
    logging.info('No files generated. You need to specific an output directory'
                 ' for the relevant langauge bindings')
  # TODO: Add support for other bindings
  return 0

if __name__ == '__main__':
  sys.exit(main(sys.argv[1:]))

