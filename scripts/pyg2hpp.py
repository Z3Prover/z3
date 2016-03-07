#!/usr/bin/env python
"""
Reads a pyg file and emits the corresponding
C++ header file into the specified destination
directory.
"""
import mk_util
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

  if not os.path.exists(pargs.destination_dir):
    logging.error('"{}" does not exist'.format(pargs.destination_dir))
    return 1

  if not os.path.isdir(pargs.destination_dir):
    logging.error('"{}" is not a directory'.format(pargs.destination_dir))
    return 1

  pyg_full_path = os.path.abspath(pargs.pyg_file)
  destination_dir_full_path = os.path.abspath(pargs.destination_dir)
  logging.info('Using {}'.format(pyg_full_path))
  # Use the existing infrastructure to do this
  mk_util.CURRENT_PYG_HPP_DEST_DIR = destination_dir_full_path
  mk_util._execfile(pyg_full_path, mk_util.PYG_GLOBALS)
  return 0

if __name__ == '__main__':
  sys.exit(main(sys.argv[1:]))

