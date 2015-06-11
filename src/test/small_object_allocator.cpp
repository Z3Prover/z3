
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include<iostream>
#include"util.h"
#include"trace.h"
#include"small_object_allocator.h"

void tst_small_object_allocator() {
    small_object_allocator soa;

    char * p1 = new (soa) char[13];
    char * q1 = new (soa) char[14];
    char * p2 = new (soa) char[13];
    TRACE("small_object_allocator", 
          tout << "p1: " << (void*)p1 << " q1: " << (void*)q1 << " p2: " << (void*)p2 << "\n";);
    soa.deallocate(13,p1);
    char * p3 = new (soa) char[13];
    TRACE("small_object_allocator", tout << "p3: " << (void*)p3 << "\n";);

    char * r1 = new (soa) char[1];
    char * r2 = new (soa) char[1];
    char * r3 = new (soa) char[1];
    char * r4 = new (soa) char[1];
    TRACE("small_object_allocator", 
          tout << "r1: " << (void*)r1 << " r2: " << (void*)r2 << " r3: " << (void*)r3 << " r4: " << (void*)r4 << "\n";);

    soa.deallocate(1,r1);
    soa.deallocate(1,r3);
    r1 = new (soa) char[1];
    soa.deallocate(1,r4);
    r4 = new (soa) char[1];
    r3 = new (soa) char[1];
    TRACE("small_object_allocator", 
          tout << "r1: " << (void*)r1 << " r2: " << (void*)r2 << " r3: " << (void*)r3 << " r4: " << (void*)r4 << "\n";);

}
