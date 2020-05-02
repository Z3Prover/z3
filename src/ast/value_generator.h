/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   value_generatorr.h

  Abstract:
   
    Generate mostly different values using index as seed.

  Author:

    Nikolaj Bjorner 2020-04-25
  
--*/

#pragma once

#include "util/scoped_ptr_vector.h"
#include "ast/ast.h"


class value_generator_core {
 public:        
    virtual ~value_generator_core() {}
    virtual family_id get_fid() const = 0;
    virtual expr_ref get_value(sort* s, unsigned index) = 0;
};

class value_generator {
    ast_manager& m;
    scoped_ptr_vector<value_generator_core> m_plugins;
    void add_plugin(value_generator_core* g);
    void init();
 public:
    value_generator(ast_manager& m);
    expr_ref get_value(sort* s, unsigned index);    
};
