#!/usr/bin/env python
"""
This script is used to copy or delete the
CMake build system files from the contrib/cmake
folder into the their correct location in the Z3
repository.

It offers two modes

* create - This will symlink the ``cmake`` directory and copy (or hard link)
the appropriate files into their correct locations in the repository.

* remove - This will remove the symlinked ``cmake``
directory and remove the files added by the above
methods.

This has the advantage
that editing the hard link edits the underlying file
(making development easier because copying files is
not neccessary) and CMake will regenerate correctly
because the modification time stamps will be correct.

"""
import argparse
import logging
import os
import pprint
import shutil
import sys

def get_full_path_to_script():
  return os.path.abspath(__file__)

def get_cmake_contrib_dir():
  return os.path.dirname(get_full_path_to_script())

def get_repo_root_dir():
  r = os.path.dirname(os.path.dirname(get_cmake_contrib_dir()))
  assert os.path.isdir(r)
  return r

# These are paths that should be ignored when checking if a folder
# in the ``contrib/cmake`` exists in the root of the repository
verificationExceptions = {
  os.path.join(get_repo_root_dir(), 'cmake'),
  os.path.join(get_repo_root_dir(), 'cmake', 'modules')
}

def contribPathToRepoPath(path):
  assert path.startswith(get_cmake_contrib_dir())
  stripped = path[len(get_cmake_contrib_dir()) + 1:] # Plus one is to remove leading slash
  assert not os.path.isabs(stripped)
  logging.debug('stripped:{}'.format(stripped))
  r = os.path.join(get_repo_root_dir(), stripped)
  assert os.path.isabs(r)
  logging.debug('Converted contrib path "{}" to repo path "{}"'.format(path, r))
  return r

def verify_mirrored_directory_struture():
  """
  Check that the directories contained in ``contrib/cmake`` exist
  in the root of the repo.
  """
  for (dirpath, _, _) in os.walk(get_cmake_contrib_dir()):
    expectedDir = contribPathToRepoPath(dirpath)
    logging.debug('expectedDir:{}'.format(expectedDir))
    if (not (os.path.exists(expectedDir) and os.path.isdir(expectedDir)) and
        expectedDir not in verificationExceptions):
      logging.error(('Expected to find directory "{}" but it does not exist'
                     ' or is not a directory').format(expectedDir))
      return 1

  return 0

def mk_sym_link(target, linkName):
  logging.info('Making symbolic link target="{}", linkName="{}"'.format(target, linkName))
  if os.path.exists(linkName):
    logging.info('Removing existing link "{}"'.format(linkName))
    if not os.path.islink(linkName):
      logging.warning('"{}" overwriting file that is not a symlink'.format(linkName))
    delete_path(linkName)
  if os.name == 'posix':
    os.symlink(target, linkName)
  else:
    # TODO: Windows does support symlinks but the implementation to do that
    # from python is a little complicated so for now lets just copy everyting
    logging.warning('Creating symbolic links is not supported. Just making a copy instead')
    if os.path.isdir(target):
      # Recursively copy directory
      shutil.copytree(src=target, dst=linkName, symlinks=False)
    else:
      # Copy file
      assert os.path.isfile(target)
      shutil.copy2(src=target, dst=linkName)

def delete_path(path):
  logging.info('Removing "{}"'.format(path))
  if not os.path.exists(path):
    logging.warning('"{}" does not exist'.format(path))
    return
  if os.path.isdir(path) and not os.path.islink(path):
    # FIXME: If we can get symbolic link support on Windows we
    # can disallow this completely.
    assert os.name == 'nt'
    shutil.rmtree(path)
  else:
    os.remove(path)

def shouldSkipFile(path):
  # Skip this script
  if path == get_full_path_to_script():
    return True
  # Skip the maintainers file
  if path == os.path.join(get_cmake_contrib_dir(), 'maintainers.txt'):
    return True
  # Skip Vim temporary files
  if os.path.basename(path).startswith('.') and path.endswith('.swp'):
    return True
  return False


def create(useHardLinks):
  """
    Copy or hard link files in the CMake contrib directory
    into the repository where they are intended to live.

    Note that symbolic links for the CMakeLists.txt files
    are not appropriate because they won't have the right
    file modification time when the files they point to
    are modified. This would prevent CMake from correctly
    reconfiguring when it detects this is required.
  """

  # Make the ``cmake`` directory a symbolic link.
  # We treat this one specially as it is the only directory
  # that doesn't already exist in the repository root so
  # we can just use a symlink here
  linkName = os.path.join(get_repo_root_dir(), 'cmake')
  target = os.path.join(get_cmake_contrib_dir(), 'cmake')
  specialDir = target
  mk_sym_link(target, linkName)

  for (dirPath,_ , fileNames) in os.walk(get_cmake_contrib_dir()):
    # Skip the special directory and its children
    if dirPath.startswith(specialDir):
      logging.info('Skipping directory "{}"'.format(dirPath))
      continue

    for fileName in fileNames:
      fileInContrib = os.path.join(dirPath, fileName)
      # Skip files
      if shouldSkipFile(fileInContrib):
        logging.info('Skipping "{}"'.format(fileInContrib))
        continue
      fileInRepo = contribPathToRepoPath(fileInContrib)
      logging.info('"{}" => "{}"'.format(fileInContrib, fileInRepo))
      if useHardLinks:
        if not os.name == 'posix':
          logging.error('Hard links are not supported on your platform')
          return False
        if os.path.exists(fileInRepo):
          delete_path(fileInRepo)
        os.link(fileInContrib, fileInRepo)
      else:
        try:
          shutil.copy2(src=fileInContrib, dst=fileInRepo)
        except shutil.Error as e:
          # Can hit this if used created hard links first and then run again without
          # wanting hard links
          if sys.version_info.major <= 2:
            logging.error(e.message)
          else:
            # Python >= 3
            if isinstance(e, shutil.SameFileError):
              logging.error('Trying to copy "{}" to "{}" but they are the same file'.format(
                fileInContrib, fileInRepo))
            else:
              logging.error(e)
          logging.error('You should remove the files using the "remove" mode '
                        'and try to create again. You probably are mixing the '
                        'hard-link and non-hard-link create modes')
          return False
  return True

def remove():
  """
    Remove the CMake files from their intended location in
    the repository. This is used to remove
    the files created by the ``create()`` function.
  """
  # This directory is treated specially as it is normally
  # a symlink.
  linkName = os.path.join(get_repo_root_dir(), 'cmake')
  delete_path(linkName)
  specialDir = os.path.join(get_cmake_contrib_dir(), 'cmake')

  for (dirPath,_ , fileNames) in os.walk(get_cmake_contrib_dir()):
    # Skip the special directory and its children
    if dirPath.startswith(specialDir):
      logging.info('Skipping directory "{}"'.format(dirPath))
      continue
    for fileName in fileNames:
      fileInContrib = os.path.join(dirPath, fileName)
      # Skip files
      if shouldSkipFile(fileInContrib):
        logging.info('Skipping "{}"'.format(fileInContrib))
        continue
      fileInRepo = contribPathToRepoPath(fileInContrib)
      if os.path.exists(fileInRepo):
        logging.info('Removing "{}"'.format(fileInRepo))
        delete_path(fileInRepo)
  return True

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

  # Before we start make sure we can transplant the CMake files on to
  # repository
  if verify_mirrored_directory_struture() != 0:
    logging.error('"{}" does not mirror "{}"'.format(get_cmake_contrib_dir(), get_repo_root_dir()))
    return 1

  if pargs.mode == "create":
    if not create(useHardLinks=pargs.hard_link):
      logging.error("Failed to create")
      return 1
  elif pargs.mode == "create_hard_link":
    if not create(useHardLinks=True):
      logging.error("Failed to create_hard_link")
      return 1
  elif pargs.mode == "remove":
    if not remove():
      logging.error("Failed to remove")
      return 1
  else:
    logging.error('Unknown mode "{}"'.format(pargs.mode))

  return 0

if __name__ == '__main__':
  sys.exit(main(sys.argv[1:]))
