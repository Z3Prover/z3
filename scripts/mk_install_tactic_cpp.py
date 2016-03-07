#!/usr/bin/env python
"""
Determines the available tactics
in header files in the list of source directions
and generates a ``install_tactic.cpp`` file in
the destination directory that defines a function
``void install_tactics(tactic_manager& ctx)``.
"""
import mk_util
import argparse
import logging
import os
import sys

def check_dir(path):
  if not os.path.exists(path):
    logging.error('"{}" does not exist'.format(path))
    return 1

  if not os.path.isdir(path):
    logging.error('"{}" is not a directory'.format(path))
    return 1

  return 0


def main(args):
  logging.basicConfig(level=logging.INFO)
  parser = argparse.ArgumentParser(description=__doc__)
  parser.add_argument("destination_dir", help="destination directory")
  parser.add_argument("source_dirs", nargs="+",
                      help="One or more source directories to search")
  pargs = parser.parse_args(args)

  if check_dir(pargs.destination_dir) != 0:
    return 1

  for source_dir in pargs.source_dirs:
    if check_dir(source_dir) != 0:
      return 1

  mk_util.mk_install_tactic_cpp_internal(pargs.source_dirs, pargs.destination_dir)
  return 0

if __name__ == '__main__':
  sys.exit(main(sys.argv[1:]))

