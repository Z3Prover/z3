#include "parser_params.h"

parser_params::parser_params() :
    m_dump_goal_as_smt(false),
    m_display_error_for_vs(false) {
}

void parser_params::register_params(ini_params & p) {
    p.register_bool_param("DUMP_GOAL_AS_SMT", m_dump_goal_as_smt, "write goal back to output in SMT format");
    p.register_bool_param("DISPLAY_ERROR_FOR_VISUAL_STUDIO", m_display_error_for_vs, "display error messages in Visual Studio format");
}



