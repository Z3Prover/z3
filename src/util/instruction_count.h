/*++
Copyright (c) 2009 Microsoft Corporation

Module Name:

    instruction_count.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2009-03-04.

Revision History:

--*/
#ifndef _INSTRUCTION_COUNT_H_
#define _INSTRUCTION_COUNT_H_


/**
   \brief Wrapper for an instruction counter.
*/
class instruction_count {
    unsigned long long m_count;
public:
    instruction_count() : m_count(0) {}

    ~instruction_count() {}

    void start();

    double get_num_instructions();

    bool is_instruction_maxed(double max_instr) { 
        return max_instr > 0.0 && get_num_instructions() > max_instr; 
    }
};

#endif /* _INSTRUcTION_COUNT_H_ */

