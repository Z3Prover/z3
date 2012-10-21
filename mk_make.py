############################################
# Copyright (c) 2012 Microsoft Corporation
# 
# Scripts for generate Makefiles and Visual 
# Studio project files.
#
# Author: Leonardo de Moura (leonardo)
############################################
from mk_util import *

BUILD_DIR='build-test'
SRC_DIR='src'
MODES=['Debug', 'Release']
PLATFORMS=['Win32', 'x64']
VS_COMMON_OPTIONS='WIN32;_WINDOWS;ASYNC_COMMANDS'
VS_DBG_OPTIONS='Z3DEBUG;_TRACE;_DEBUG'
VS_RELEASE_OPTIONS='NDEBUG;_EXTERNAL_RELEASE'

# Initialization
mk_dir(BUILD_DIR)

add_lib('util', [])
add_lib('polynomial', ['util'])
add_lib('sat', ['util', 'sat_core'])
add_lib('nlsat', ['util', 'sat_core', 'polynomial'])
add_lib('subpaving', ['util'])
add_lib('ast', ['util', 'polynomial'])
add_lib('rewriter', ['util', 'ast', 'polynomial'])
# Simplifier module will be deleted in the future.
# It has been replaced with rewriter module.
add_lib('simplifier', ['util', 'ast', 'rewriter'])
# Model module should not depend on simplifier module. 
# We must replace all occurrences of simplifier with rewriter.
add_lib('model', ['util', 'ast', 'rewriter', 'simplifier'])
add_lib('tactic', ['util', 'ast'])

