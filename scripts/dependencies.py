############################################
# Copyright (c) 2012 Microsoft Corporation
# 
# Scripts for extracting dependencies in 
# C/C++ files
#
# Author: Leonardo de Moura (leonardo)
############################################
import re
import os
import sets
from mk_exception import *

# Return a list containing a file names included using '#include' in
# the given C/C++ file named fname.
def extract_c_includes(fname):
    result = []
    # We look for well behaved #include directives
    std_inc_pat     = re.compile("[ \t]*#include[ \t]*\"(.*)\"[ \t]*")
    system_inc_pat  = re.compile("[ \t]*#include[ \t]*\<.*\>[ \t]*")
    # We should generate and error for any occurrence of #include that does not match the previous pattern.
    non_std_inc_pat = re.compile(".*#include.*")
    
    f = open(fname, 'r')
    linenum = 1
    for line in f:
        m1 = std_inc_pat.match(line)
        if m1:
            result.append(m1.group(1))
        elif not system_inc_pat.match(line) and non_std_inc_pat.match(line):
            raise MKException("Invalid #include directive at '%s':%s" % (fname, line))
        linenum = linenum + 1
    return result

# Return src_dir/path/fname
def mk_full_fname(src_dir, path, fname):
    # return '%s%s%s%s%s' % (src_dir, os.sep, path, os.sep, fname)
    return '%s/%s/%s' % (src_dir, path, fname)

# Return True if the file src_dir/path/fname exists.
# Otherwise return False.
def has_file(src_dir, path, fname):
    try:
        with open(mk_full_fname(src_dir, path, fname)) as f: pass
        return True
    except IOError as e:
        return False

# Search a file named fname at:
#   src_dir/path
#   for each p in search_path
#      src_dir/p
def find_file(src_dir, path, search_path, fname):
    if has_file(src_dir, path, fname):
        return mk_full_fname(src_dir, path, fname)
    for path in search_path:
        if has_file(src_dir, path, fname):
            return mk_full_fname(src_dir, path, fname)
    return None

# Extract the dependency list of the C/C++ file fname (basename)
# located at path relative to src_dir. search_path is 
# a list of paths relative to src_dir where we should look for 
# include files.
# Remark: this method returns the transitive closure of the dependencies.
def extract_c_dependencies(src_dir, path, fname, search_path):
    result = []
    processed = sets.Set()
    full_fname = mk_full_fname(src_dir, path, fname)
    processed.add(full_fname)
    todo = [full_fname]
    while todo:
        curr = todo[-1]
        todo.pop()
        deps = extract_c_includes(curr)
        for dep in deps:
            full_dep = find_file(src_dir, path, search_path, dep)
            if full_dep == None:
                raise MKException("File '%s' was not found when processing '%s' for '%s'. Remark: system files should be included using #include<...>." % (dep, curr, fname))
            if not full_dep in processed:
                processed.add(full_dep)
                todo.append(full_dep)
                result.append(full_dep)
    return result

