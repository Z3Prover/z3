#!/usr/bin/env python
"""
This script is an artifact of compromise that was
made when the CMake build system was first introduced
(see #461).

This script now does nothing. It remains only to not
break out-of-tree scripts that build Z3 using CMake.

Eventually this script will be removed.
"""
import argparse
import logging
import os
import pprint
import shutil
import sys

def main(args):
  logging.basicConfig(level=logging.INFO)
  parser = argparse.ArgumentParser(description=__doc__)
  parser.add_argument('mode',
    choices=['create', 'remove'],
    help='The mode to use')
  parser.add_argument("-l","--log-level",
    type=str,
    default="info",
    dest="log_level",
    choices=['debug','info','warning','error']
  )
  parser.add_argument("-H", "--hard-link",
    action='store_true',
    default=False,
    dest='hard_link',
    help='When using the create mode create hard links instead of copies'
  )
  pargs = parser.parse_args(args)

  logLevel = getattr(logging, pargs.log_level.upper(),None)
  logging.basicConfig(level=logLevel)
  logging.warning('Use of this script is deprecated. The script will be removed in the future')
  logging.warning('Action "{}" ignored'.format(pargs.mode))
  if pargs.hard_link:
    logging.warning('Hard link option ignored')
  return 0

if __name__ == '__main__':
  sys.exit(main(sys.argv[1:]))
