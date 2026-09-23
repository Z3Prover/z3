############################################
# Copyright (c) 2013 Microsoft Corporation
#
# Helpers shared by mk_unix_dist.py and mk_win_dist.py.
#
# Author: Leonardo de Moura (leonardo)
############################################

import os
import subprocess
import sys
from mk_exception import *

def getenv(name, default):
    try:
        return os.environ[name].strip(' "\'')
    except:
        return default

def check_output(cmd):
    out = subprocess.Popen(cmd, stdout=subprocess.PIPE).communicate()[0]
    if out != None:
        enc = sys.getdefaultencoding()
        if enc != None: return out.decode(enc).rstrip('\r\n')
        else: return out.rstrip('\r\n')
    else:
        return ""

def get_git_hash():
    try:
        branch = check_output(['git', 'rev-parse', '--abbrev-ref', 'HEAD'])
        r = check_output(['git', 'show-ref', '--abbrev=12', 'refs/heads/%s' % branch])
    except:
        raise MKException("Failed to retrieve git hash")
    ls = r.split(' ')
    if len(ls) != 2:
        raise MKException("Unexpected git output " + r)
    return ls[0]
