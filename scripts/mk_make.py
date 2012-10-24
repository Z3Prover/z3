############################################
# Copyright (c) 2012 Microsoft Corporation
# 
# Scripts for generating Makefiles and Visual 
# Studio project files.
#
# Author: Leonardo de Moura (leonardo)
############################################
from mk_util import *

parse_options()

# set_build_dir('build')
# set_src_dir('src')
# set_modes(['Debug', 'Release'])
# set_platforms(['Win32', 'x64'])
# set_vs_options('WIN32;_WINDOWS;ASYNC_COMMANDS',
#                'Z3DEBUG;_TRACE;_DEBUG',
#                'NDEBUG;_EXTERNAL_RELEASE')

add_lib('util', [])
add_lib('polynomial', ['util'], 'math/polynomial')
add_lib('sat', ['util'])
# nlsat only reuses the file sat_types.h from sat
add_lib('nlsat', ['polynomial', 'sat'])
add_lib('subpaving', ['util'], 'math/subpaving')
add_lib('ast', ['util', 'polynomial'])
add_lib('rewriter', ['ast', 'polynomial'], 'ast/rewriter')
# array_property is only used in test exe
add_lib('array_property', ['ast', 'rewriter'], 'ast/array_property')
# Simplifier module will be deleted in the future.
# It has been replaced with rewriter module.
add_lib('simplifier', ['rewriter'], 'ast/simplifier')
# Model module should not depend on simplifier module. 
# We must replace all occurrences of simplifier with rewriter.
add_lib('model', ['rewriter', 'simplifier'])
add_lib('tactic', ['ast', 'model'])
# Old (non-modular) parameter framework. It has been subsumed by util\params.h.
# However, it is still used by many old components.
add_lib('old_params', ['model', 'simplifier'])
add_lib('cmd_context', ['tactic', 'rewriter', 'model', 'old_params', 'simplifier'])
# Assertion set is the old tactic framework used in Z3 3.x. It will be deleted as soon as we finish the porting old
# code to the new tactic framework.
add_lib('assertion_set', ['cmd_context'])
add_lib('substitution', ['ast'], 'ast/substitution')
add_lib('normal_forms', ['tactic', 'old_params'])
add_lib('pattern', ['normal_forms'], 'ast/pattern')
add_lib('spc', ['simplifier', 'substitution', 'old_params', 'pattern'])
add_lib('parser_util', ['ast'])
add_lib('smt2parser', ['cmd_context', 'parser_util'])
add_lib('macros', ['simplifier', 'old_params'], 'ast/macros')
add_lib('grobner', ['ast'], 'math/grobner')
add_lib('euclid', ['util'], 'math/euclid')
add_lib('proof_checker', ['rewriter', 'spc'], 'ast/proof_checker')
add_lib('bit_blaster', ['rewriter', 'simplifier', 'old_params', 'tactic'], 'tactic/bit_blaster')
add_lib('smt', ['assertion_set', 'bit_blaster', 'macros', 'normal_forms', 'cmd_context', 
                'substitution', 'grobner', 'euclid', 'proof_checker', 'pattern', 'parser_util'])
add_lib('user_plugin', ['smt'], 'smt/user_plugin')
add_lib('core_tactics', ['tactic', 'normal_forms'], 'tactic/core_tactics')
add_lib('sat_tactic', ['tactic', 'sat'], 'tactic/sat_tactic')
add_lib('sat_strategy', ['assertion_set', 'sat_tactic'], 'assertion_set/sat_strategy')
add_lib('arith_tactics', ['core_tactics', 'assertion_set', 'sat', 'sat_strategy'], 'tactic/arith_tactics')
add_lib('nlsat_tactic', ['nlsat', 'sat_tactic', 'arith_tactics'], 'tactic/nlsat_tactic')
add_lib('subpaving_tactic', ['core_tactics', 'subpaving'], 'math/subpaving/tactic')
add_lib('bv_tactics', ['tactic', 'bit_blaster'], 'tactic/bv_tactics')
add_lib('fuzzing', ['ast'], 'test/fuzzing')
add_lib('fpa', ['core_tactics', 'bv_tactics', 'sat_tactic'], 'tactic/fpa')
add_lib('smt_tactic', ['smt'], 'smt/tactic')
add_lib('extra_cmds', ['cmd_context', 'subpaving_tactic', 'arith_tactics'], 'cmd_context/extra_cmds')
add_lib('sls_tactic', ['tactic', 'normal_forms', 'core_tactics', 'bv_tactics'], 'tactic/sls_tactic')
add_lib('aig', ['cmd_context', 'assertion_set'], 'tactic/aig')
# TODO: split muz_qe into muz, qe. Perhaps, we should also consider breaking muz into muz and pdr.
add_lib('muz_qe', ['smt', 'sat', 'smt2parser'])
add_lib('smtlogic_tactics', ['arith_tactics', 'bv_tactics', 'nlsat_tactic', 'smt_tactic', 'aig', 'muz_qe'], 'tactic/smtlogic_tactics')
# TODO: rewrite ufbv_strategy as a tactic and move to smtlogic_tactics.
add_lib('ufbv_tactic', ['normal_forms', 'core_tactics', 'macros', 'smt_tactic', 'rewriter'], 'tactic/ufbv_tactic')
add_lib('portfolio', ['smtlogic_tactics', 'ufbv_tactic', 'fpa', 'aig', 'muz_qe', 'sls_tactic', 'subpaving_tactic'], 'tactic/portfolio')
# TODO: delete SMT 1.0 frontend
add_lib('api', ['portfolio', 'user_plugin'])
add_exe('shell', ['api', 'sat', 'extra_cmds'], exe_name='z3')
add_exe('test', ['api', 'fuzzing', 'array_property'], exe_name='test-z3')

# mk_vs_solution()

mk_makefile()
