############################################
# Copyright (c) 2012 Microsoft Corporation
# 
# Scripts for generating Makefiles and Visual 
# Studio project files.
#
# Author: Leonardo de Moura (leonardo)
############################################
from mk_util import *
from mk_project import *

parse_options()
check_eol()
API_files = init_project_def()

update_version()
mk_auto_src()
mk_bindings(API_files)
mk_vs_proj('z3', ['shell'])
mk_makefile()


