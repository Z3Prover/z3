#pragma once

namespace smt {

    class value_generator_core {
    public:        
        virtual expr* get_value(sort* s, unsigned index) = 0;
    };
    
    class value_generator {
        scoped_ptr_vector<value_generator_core> m_plugins;
    public:
        value_generator(ast_manager& m);
        expr* get_value(sort* s, unsigned index);
        
    };
}
