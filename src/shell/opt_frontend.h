/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    opt_frontend.h

Author:

    Nikolaj Bjorner (nbjorner) 2014-10-10.

--*/
#pragma once

enum opt_format { opb_t, wcnf_t, lp_t };

unsigned parse_opt(char const* file_name, opt_format f);



