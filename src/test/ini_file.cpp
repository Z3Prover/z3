/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ini_file.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-05-10.

Revision History:

--*/
#include<sstream>
#include"ini_file.h"
#include"debug.h"

static void tst1() {
    ini_params p;
    int p1; 
    p.register_int_param("ipar1", 0, 100, p1);
    int p2;
    p.register_int_param("ipar2", -100, 100, p2);
    bool p3;
    p.register_bool_param("bpar1", p3);
    bool p4;
    p.register_bool_param("bpar2", p4);
    unsigned p5;
    p.register_unsigned_param("upar1", 0, 100, p5);
    double p6;
    p.register_percentage_param("ppar1", p6);
    std::istringstream in("ipar1 = 100 ipar2=-30 bpar1 = true ;; COMMENT\n  bpar2 = false  upar1=30 ppar1 = 10");
    p.read_ini_file(in);
    SASSERT(p1 == 100);
    SASSERT(p2 == -30);
    SASSERT(p3);
    SASSERT(!p4);
    SASSERT(p5 == 30);
    SASSERT(p6 == 0.1);
}

void tst_ini_file() {
    tst1();
}

