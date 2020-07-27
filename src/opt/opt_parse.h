/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    opt_parse.h

Abstract:

    Parse utilities for optimization.

Author:

    Nikolaj Bjorner (nbjorner) 2017-11-19

Revision History:

--*/
#pragma once

void parse_wcnf(opt::context& opt, std::istream& is, unsigned_vector& h);

void parse_opb(opt::context& opt, std::istream& is, unsigned_vector& h);

void parse_lp(opt::context& opt, std::istream& is, unsigned_vector& h);



