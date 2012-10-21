############################################
# Copyright (c) 2012 Microsoft Corporation
# 
# Scripts for generate Makefiles and Visual 
# Studio project files.
#
# Author: Leonardo de Moura (leonardo)
############################################
from mk_util import *

set_build_dir('build-test')
set_src_dir('src')
set_modes(['Debug', 'Release'])
set_platforms(['Win32', 'x64'])
set_vs_options('WIN32;_WINDOWS;ASYNC_COMMANDS',
               'Z3DEBUG;_TRACE;_DEBUG',
               'NDEBUG;_EXTERNAL_RELEASE')

add_lib('util', [])
add_lib('polynomial', ['util'])
add_lib('sat', ['util', 'sat_core'])
add_lib('nlsat', ['util', 'sat_core', 'polynomial'])
add_lib('subpaving', ['util'])
add_lib('ast', ['util', 'polynomial'])
add_lib('rewriter', ['util', 'ast', 'polynomial'])
# Old (non-modular) parameter framework. It has been subsumed by util\params.h.
# However, it is still used by many old components.
add_lib('old_params', ['util', 'ast', 'model'])
# Simplifier module will be deleted in the future.
# It has been replaced with rewriter module.
add_lib('simplifier', ['util', 'ast', 'rewriter', 'old_params'])
# Model module should not depend on simplifier module. 
# We must replace all occurrences of simplifier with rewriter.
add_lib('model', ['util', 'ast', 'rewriter', 'simplifier', 'old_params'])
add_lib('framework', ['util', 'ast', 'model', 'old_params', 'simplifier', 'rewriter'])
# Assertion set is the old tactic framework used in Z3 3.x. It will be deleted as soon as we finish the porting old
# code to the new tactic framework.
add_lib('assertion_set', ['util', 'ast', 'framework', 'model', 'rewriter', 'old_params'])
add_lib('normal_forms', ['util', 'ast', 'old_params', 'simplifier', 'rewriter', 'assertion_set', 'framework', 'model'])
add_lib('smt', ['util', 'ast', 'assertion_set'])
add_lib('pattern', ['util', 'ast'])
add_lib('spc', ['util', 'ast', 'simplifier', 'pattern', 'model', 'old_params', 'normal_forms', 'rewriter'])
