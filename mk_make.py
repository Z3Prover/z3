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

add_header('api_headers')
add_lib('util', [])
add_lib('polynomial', ['util'])
add_lib('sat', ['util'])
# nlsat only reuses the file sat_types.h from sat
add_lib('nlsat', ['polynomial', 'sat'])
add_lib('subpaving', ['util'])
add_lib('ast', ['util', 'polynomial'])
add_lib('rewriter', ['ast', 'polynomial'])
# Simplifier module will be deleted in the future.
# It has been replaced with rewriter module.
add_lib('simplifier', ['rewriter'])
# Model module should not depend on simplifier module. 
# We must replace all occurrences of simplifier with rewriter.
add_lib('model', ['rewriter', 'simplifier'])
# Old (non-modular) parameter framework. It has been subsumed by util\params.h.
# However, it is still used by many old components.
add_lib('old_params', ['model', 'simplifier'])
add_lib('framework', ['rewriter', 'model', 'old_params', 'simplifier'])
# Assertion set is the old tactic framework used in Z3 3.x. It will be deleted as soon as we finish the porting old
# code to the new tactic framework.
add_lib('assertion_set', ['framework'])
add_lib('substitution', ['ast'])
add_lib('normal_forms', ['framework', 'assertion_set'])
add_lib('pattern', ['normal_forms'])
add_lib('spc', ['simplifier', 'substitution', 'old_params', 'pattern'])
add_lib('parser_util', ['ast'])
add_lib('smt2parser', ['framework', 'parser_util'])
add_lib('macros', ['simplifier', 'old_params'])
add_lib('grobner', ['ast'])
add_lib('euclid', ['util'])
add_lib('proof_checker', ['rewriter', 'spc'])
add_lib('bit_blaster', ['rewriter', 'simplifier', 'old_params', 'framework', 'assertion_set'])
add_lib('smt', ['assertion_set', 'bit_blaster', 'macros', 'normal_forms', 'framework', 
                'substitution', 'grobner', 'euclid', 'proof_checker', 'pattern', 'parser_util'])
add_lib('user_plugin', ['smt'])
add_lib('core_tactics', ['framework', 'normal_forms'])
add_lib('arith_tactics', ['core_tactics', 'assertion_set'])
add_lib('sat_tactic', ['framework', 'sat'])
add_lib('sat_strategy', ['assertion_set', 'sat_tactic'])
# TODO: split muz_qe into muz, qe. Perhaps, we should also consider breaking muz into muz and pdr.
add_lib('muz_qe', ['smt', 'sat', 'smt2parser'])
add_lib('aig', ['framework', 'assertion_set'])
# TODO: delete SMT 1.0 frontend
add_lib('smtparser', ['api_headers', 'smt', 'spc'])
