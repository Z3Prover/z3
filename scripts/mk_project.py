############################################
# Copyright (c) 2012 Microsoft Corporation
# 
# Z3 project configuration files
#
# Author: Leonardo de Moura (leonardo)
############################################
from mk_util import *

# Z3 Project definition
def init_project_def():
    set_version(4, 8, 1, 0)
    add_lib('util', [], includes2install = ['z3_version.h'])
    add_lib('polynomial', ['util'], 'math/polynomial')
    add_lib('sat', ['util'])
    add_lib('nlsat', ['polynomial', 'sat'])
    add_lib('lp', ['util','nlsat'], 'util/lp')
    add_lib('hilbert', ['util'], 'math/hilbert')
    add_lib('simplex', ['util'], 'math/simplex')
    add_lib('automata', ['util'], 'math/automata')
    add_lib('interval', ['util'], 'math/interval')
    add_lib('realclosure', ['interval'], 'math/realclosure')
    add_lib('subpaving', ['interval'], 'math/subpaving')
    add_lib('ast', ['util', 'polynomial'])
    add_lib('rewriter', ['ast', 'polynomial', 'automata'], 'ast/rewriter')
    add_lib('macros', ['rewriter'], 'ast/macros')
    add_lib('normal_forms', ['rewriter'], 'ast/normal_forms')
    add_lib('model', ['rewriter'])
    add_lib('tactic', ['ast', 'model'])
    add_lib('substitution', ['ast', 'rewriter'], 'ast/substitution')
    add_lib('parser_util', ['ast'], 'parsers/util')
    add_lib('grobner', ['ast'], 'math/grobner')
    add_lib('euclid', ['util'], 'math/euclid')
    add_lib('core_tactics', ['tactic', 'macros', 'normal_forms', 'rewriter'], 'tactic/core')
    add_lib('proofs', ['rewriter', 'util'], 'ast/proofs')
    add_lib('solver', ['model', 'tactic', 'proofs'])
    add_lib('sat_tactic', ['tactic', 'sat', 'solver'], 'sat/tactic')
    add_lib('arith_tactics', ['core_tactics', 'sat'], 'tactic/arith')
    add_lib('nlsat_tactic', ['nlsat', 'sat_tactic', 'arith_tactics'], 'nlsat/tactic')
    add_lib('subpaving_tactic', ['core_tactics', 'subpaving'], 'math/subpaving/tactic')
    add_lib('aig_tactic', ['tactic'], 'tactic/aig')
    add_lib('ackermannization', ['model', 'rewriter', 'ast', 'solver', 'tactic'], 'ackermannization')
    add_lib('cmd_context', ['solver', 'rewriter'])
    add_lib('smt2parser', ['cmd_context', 'parser_util'], 'parsers/smt2')
    add_lib('fpa', ['ast', 'util', 'rewriter', 'model'], 'ast/fpa')
    add_lib('pattern', ['normal_forms', 'smt2parser', 'rewriter'], 'ast/pattern')
    add_lib('bit_blaster', ['rewriter', 'rewriter'], 'ast/rewriter/bit_blaster')
    add_lib('smt_params', ['ast', 'rewriter', 'pattern', 'bit_blaster'], 'smt/params')
    add_lib('proto_model', ['model', 'rewriter', 'smt_params'], 'smt/proto_model')
    add_lib('smt', ['bit_blaster', 'macros', 'normal_forms', 'cmd_context', 'proto_model',
                    'substitution', 'grobner', 'euclid', 'simplex', 'proofs', 'pattern', 'parser_util', 'fpa', 'lp'])
    add_lib('bv_tactics', ['tactic', 'bit_blaster', 'core_tactics'], 'tactic/bv')
    add_lib('fuzzing', ['ast'], 'test/fuzzing')
    add_lib('smt_tactic', ['smt'], 'smt/tactic')
    add_lib('sls_tactic', ['tactic', 'normal_forms', 'core_tactics', 'bv_tactics'], 'tactic/sls')
    add_lib('qe', ['smt','sat','nlsat','tactic','nlsat_tactic'], 'qe')
    add_lib('sat_solver', ['solver', 'core_tactics', 'aig_tactic', 'bv_tactics', 'arith_tactics', 'sat_tactic'], 'sat/sat_solver')
    add_lib('fd_solver', ['core_tactics', 'arith_tactics', 'sat_solver'], 'tactic/fd_solver') 
    add_lib('muz', ['smt', 'sat', 'smt2parser', 'aig_tactic', 'qe'], 'muz/base')
    add_lib('dataflow', ['muz'], 'muz/dataflow')
    add_lib('transforms', ['muz', 'hilbert', 'dataflow'], 'muz/transforms')
    add_lib('rel', ['muz', 'transforms'], 'muz/rel')
    add_lib('spacer', ['muz', 'transforms', 'arith_tactics', 'smt_tactic'], 'muz/spacer')
    add_lib('clp', ['muz', 'transforms'], 'muz/clp')
    add_lib('tab', ['muz', 'transforms'], 'muz/tab')
    add_lib('ddnf', ['muz', 'transforms', 'rel'], 'muz/ddnf')
    add_lib('bmc', ['muz', 'transforms', 'fd_solver'], 'muz/bmc')
    add_lib('fp',  ['muz', 'clp', 'tab', 'rel', 'bmc', 'ddnf', 'spacer'], 'muz/fp')
    add_lib('ufbv_tactic', ['normal_forms', 'core_tactics', 'macros', 'smt_tactic', 'rewriter'], 'tactic/ufbv')
    add_lib('smtlogic_tactics', ['ackermannization', 'sat_solver', 'arith_tactics', 'bv_tactics', 'nlsat_tactic', 'smt_tactic', 'aig_tactic', 'fp', 'muz','qe'], 'tactic/smtlogics')
    add_lib('fpa_tactics', ['fpa', 'core_tactics', 'bv_tactics', 'sat_tactic', 'smt_tactic', 'arith_tactics', 'smtlogic_tactics'], 'tactic/fpa')
    add_lib('portfolio', ['smtlogic_tactics', 'sat_solver', 'ufbv_tactic', 'fpa_tactics', 'aig_tactic', 'fp',  'fd_solver', 'qe','sls_tactic', 'subpaving_tactic'], 'tactic/portfolio')
    add_lib('opt', ['smt', 'smtlogic_tactics', 'sls_tactic', 'sat_solver'], 'opt')
    API_files = ['z3_api.h', 'z3_ast_containers.h', 'z3_algebraic.h', 'z3_polynomial.h', 'z3_rcf.h', 'z3_fixedpoint.h', 'z3_optimization.h', 'z3_fpa.h', 'z3_spacer.h']
    add_lib('api', ['portfolio',  'realclosure', 'opt'],
            includes2install=['z3.h', 'z3_v1.h', 'z3_macros.h'] + API_files)
    add_lib('extra_cmds', ['cmd_context', 'subpaving_tactic', 'qe', 'arith_tactics'], 'cmd_context/extra_cmds')
    add_exe('shell', ['api', 'sat', 'extra_cmds','opt'], exe_name='z3')
    add_exe('test', ['api', 'fuzzing', 'simplex'], exe_name='test-z3', install=False)
    _libz3Component = add_dll('api_dll', ['api', 'sat', 'extra_cmds'], 'api/dll',
                              reexports=['api'],
                              dll_name='libz3',
                              static=build_static_lib(),
                              export_files=API_files,
                              staging_link='python')
    add_dot_net_dll('dotnet', ['api_dll'], 'api/dotnet', dll_name='Microsoft.Z3', assembly_info_dir='Properties', default_key_file='src/api/dotnet/Microsoft.Z3.snk')
    add_java_dll('java', ['api_dll'], 'api/java', dll_name='libz3java', package_name="com.microsoft.z3", manifest_file='manifest')
    add_ml_lib('ml', ['api_dll'], 'api/ml', lib_name='libz3ml')
    add_hlib('cpp', 'api/c++', includes2install=['z3++.h'])
    set_z3py_dir('api/python')
    add_python(_libz3Component)
    add_python_install(_libz3Component)
    add_js()
    # Examples
    add_cpp_example('cpp_example', 'c++') 
    add_cpp_example('z3_tptp', 'tptp') 
    add_c_example('c_example', 'c')
    add_c_example('maxsat')
    add_dotnet_example('dotnet_example', 'dotnet')
    add_java_example('java_example', 'java')
    add_ml_example('ml_example', 'ml')
    add_z3py_example('py_example', 'python')
    return API_files


