#ifdef _WINDOWS
#include "z3.h"
#include "z3_private.h"
#include <iostream>
#include "util.h"
#include "trace.h"
#include <map>
#include "trace.h"

void bv_invariant() {

#define SET(_i, _v) m[_i] = _v
#define GET(_ty,_i) reinterpret_cast<_ty>(m[_i])

 std::map<int, void*> m;
 Z3_config cfg = Z3_mk_config();
 Z3_set_param_value(cfg,"MODEL","true");
 Z3_context ctx = Z3_mk_context(cfg);
 Z3_model _m = 0;
 enable_trace("after_internalization"); 
 enable_trace("final_check"); 
 enable_trace("bv"); 
 enable_trace("propagate_atoms"); 
 enable_trace("assign_core"); 
 enable_trace("bv_bug"); 
 enable_trace("bv_bit_prop"); 
 enable_trace("mark_as_relevant_core");
{SET(0x03BC7FD8, Z3_mk_bv_sort(ctx,32));}
{SET(0x03BCCD88, Z3_mk_int(ctx,0,GET(Z3_sort,0x03BC7FD8)));}
{SET(0x03BCCE08, Z3_mk_int(ctx,1,GET(Z3_sort,0x03BC7FD8)));}
{SET(0x03BC9428, Z3_mk_eq(ctx,GET(Z3_ast,0x03BCCD88),GET(Z3_ast,0x03BCCD88)));}
{SET(0x03CEC820, Z3_get_app_decl(ctx,GET(Z3_app,0x03BC9428)));}
{Z3_mk_string_symbol(ctx,"null");}
{Z3_mk_string_symbol(ctx,"isnull");}
{SET(0x03CEC870, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"null"),Z3_mk_string_symbol(ctx,"isnull"),0,0,0,0));}
{Z3_mk_string_symbol(ctx,"ArgumentException");}
{Z3_mk_string_symbol(ctx,"isArgumentException");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE130[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE160[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE190[1] = {0, }; SET(0x03CEC8C0, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"ArgumentException"),Z3_mk_string_symbol(ctx,"isArgumentException"),1,args03CEE130,args03CEE160,args03CEE190));}
{Z3_mk_string_symbol(ctx,"String");}
{Z3_mk_string_symbol(ctx,"isString");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE130[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE160[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE190[1] = {0, }; SET(0x03CEC910, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"String"),Z3_mk_string_symbol(ctx,"isString"),1,args03CEE130,args03CEE160,args03CEE190));}
{Z3_mk_string_symbol(ctx,"MethodBase");}
{Z3_mk_string_symbol(ctx,"isMethodBase");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE130[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE160[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE190[1] = {0, }; SET(0x03CEC960, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"MethodBase"),Z3_mk_string_symbol(ctx,"isMethodBase"),1,args03CEE130,args03CEE160,args03CEE190));}
{Z3_mk_string_symbol(ctx,"Exception");}
{Z3_mk_string_symbol(ctx,"isException");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE130[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE160[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE190[1] = {0, }; SET(0x03CEC9B0, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"Exception"),Z3_mk_string_symbol(ctx,"isException"),1,args03CEE130,args03CEE160,args03CEE190));}
{Z3_mk_string_symbol(ctx,"Object");}
{Z3_mk_string_symbol(ctx,"isObject");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE130[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE160[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE190[1] = {0, }; SET(0x03CECA00, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"Object"),Z3_mk_string_symbol(ctx,"isObject"),1,args03CEE130,args03CEE160,args03CEE190));}
{Z3_mk_string_symbol(ctx,"Box");}
{Z3_mk_string_symbol(ctx,"isBox");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE160[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE190[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE1C0[1] = {0, }; SET(0x03CECA50, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"Box"),Z3_mk_string_symbol(ctx,"isBox"),1,args03CEE160,args03CEE190,args03CEE1C0));}
{Z3_mk_string_symbol(ctx,"Term");}
{Z3_mk_string_symbol(ctx,"isTerm");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE160[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE190[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE1C0[1] = {0, }; SET(0x03BE9430, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"Term"),Z3_mk_string_symbol(ctx,"isTerm"),1,args03CEE160,args03CEE190,args03CEE1C0));}
{Z3_mk_string_symbol(ctx,"Box");}
{Z3_mk_string_symbol(ctx,"isBox");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE160[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE190[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE1C0[1] = {0, }; SET(0x03BE9480, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"Box"),Z3_mk_string_symbol(ctx,"isBox"),1,args03CEE160,args03CEE190,args03CEE1C0));}
{Z3_mk_string_symbol(ctx,"SystemException");}
{Z3_mk_string_symbol(ctx,"isSystemException");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE160[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE190[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE1C0[1] = {0, }; SET(0x03BE9520, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"SystemException"),Z3_mk_string_symbol(ctx,"isSystemException"),1,args03CEE160,args03CEE190,args03CEE1C0));}
{Z3_mk_string_symbol(ctx,"RuntimeFieldHandle");}
{Z3_mk_string_symbol(ctx,"isRuntimeFieldHandle");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE160[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE190[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE1C0[1] = {0, }; SET(0x03BE94D0, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"RuntimeFieldHandle"),Z3_mk_string_symbol(ctx,"isRuntimeFieldHandle"),1,args03CEE160,args03CEE190,args03CEE1C0));}
{Z3_mk_string_symbol(ctx,"Box");}
{Z3_mk_string_symbol(ctx,"isBox");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE160[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE190[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE1C0[1] = {0, }; SET(0x03BE9570, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"Box"),Z3_mk_string_symbol(ctx,"isBox"),1,args03CEE160,args03CEE190,args03CEE1C0));}
{Z3_mk_string_symbol(ctx,"RuntimeTypeHandle");}
{Z3_mk_string_symbol(ctx,"isRuntimeTypeHandle");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE160[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE190[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE1C0[1] = {0, }; SET(0x03BE95C0, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"RuntimeTypeHandle"),Z3_mk_string_symbol(ctx,"isRuntimeTypeHandle"),1,args03CEE160,args03CEE190,args03CEE1C0));}
{Z3_mk_string_symbol(ctx,"Box");}
{Z3_mk_string_symbol(ctx,"isBox");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE160[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE190[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE1C0[1] = {0, }; SET(0x03BE9610, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"Box"),Z3_mk_string_symbol(ctx,"isBox"),1,args03CEE160,args03CEE190,args03CEE1C0));}
{Z3_mk_string_symbol(ctx,"NullReferenceException");}
{Z3_mk_string_symbol(ctx,"isNullReferenceException");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE160[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE190[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE1C0[1] = {0, }; SET(0x03BE9660, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"NullReferenceException"),Z3_mk_string_symbol(ctx,"isNullReferenceException"),1,args03CEE160,args03CEE190,args03CEE1C0));}
{Z3_mk_string_symbol(ctx,"InvalidCastException");}
{Z3_mk_string_symbol(ctx,"isInvalidCastException");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE160[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE190[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE1C0[1] = {0, }; SET(0x03BE96B0, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"InvalidCastException"),Z3_mk_string_symbol(ctx,"isInvalidCastException"),1,args03CEE160,args03CEE190,args03CEE1C0));}
{Z3_mk_string_symbol(ctx,"IndexOutOfRangeException");}
{Z3_mk_string_symbol(ctx,"isIndexOutOfRangeException");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE160[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE190[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE1C0[1] = {0, }; SET(0x03BE9700, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"IndexOutOfRangeException"),Z3_mk_string_symbol(ctx,"isIndexOutOfRangeException"),1,args03CEE160,args03CEE190,args03CEE1C0));}
{Z3_mk_string_symbol(ctx,"StackOverflowException");}
{Z3_mk_string_symbol(ctx,"isStackOverflowException");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE160[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE190[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE1C0[1] = {0, }; SET(0x03BE9750, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"StackOverflowException"),Z3_mk_string_symbol(ctx,"isStackOverflowException"),1,args03CEE160,args03CEE190,args03CEE1C0));}
{Z3_mk_string_symbol(ctx,"ExecutionEngineException");}
{Z3_mk_string_symbol(ctx,"isExecutionEngineException");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE160[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE190[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE1C0[1] = {0, }; SET(0x03BE97A0, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"ExecutionEngineException"),Z3_mk_string_symbol(ctx,"isExecutionEngineException"),1,args03CEE160,args03CEE190,args03CEE1C0));}
{Z3_mk_string_symbol(ctx,"Box");}
{Z3_mk_string_symbol(ctx,"isBox");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE160[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE190[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE1C0[1] = {0, }; SET(0x03BE97F0, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"Box"),Z3_mk_string_symbol(ctx,"isBox"),1,args03CEE160,args03CEE190,args03CEE1C0));}
{Z3_mk_string_symbol(ctx,"Value");}
{Z3_mk_string_symbol(ctx,"isValue");}
{Z3_mk_string_symbol(ctx,"value");}
{Z3_symbol args03CEE160[1] = {Z3_mk_string_symbol(ctx,"value"), }; Z3_sort args03CEE190[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE1C0[1] = {0, }; SET(0x03BE9840, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"Value"),Z3_mk_string_symbol(ctx,"isValue"),1,args03CEE160,args03CEE190,args03CEE1C0));}
{Z3_mk_string_symbol(ctx,"Value");}
{Z3_mk_string_symbol(ctx,"isValue");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE160[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE190[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE1C0[1] = {0, }; SET(0x03BE9890, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"Value"),Z3_mk_string_symbol(ctx,"isValue"),1,args03CEE160,args03CEE190,args03CEE1C0));}
{Z3_mk_string_symbol(ctx,"Int32[]");}
{Z3_mk_string_symbol(ctx,"isInt32[]");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE160[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE190[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE1C0[1] = {0, }; SET(0x03BE98E0, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"Int32[]"),Z3_mk_string_symbol(ctx,"isInt32[]"),1,args03CEE160,args03CEE190,args03CEE1C0));}
{Z3_mk_string_symbol(ctx,"Add");}
{Z3_mk_string_symbol(ctx,"isAdd");}
{Z3_mk_string_symbol(ctx,"left");}
{Z3_mk_string_symbol(ctx,"right");}
{Z3_symbol args03BEA4A0[2] = {Z3_mk_string_symbol(ctx,"left"), Z3_mk_string_symbol(ctx,"right"), }; Z3_sort args03BEA548[2] = {GET(Z3_sort,0x00000000), GET(Z3_sort,0x00000000), }; unsigned args03BEA580[2] = {0, 0, }; SET(0x03BE9930, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"Add"),Z3_mk_string_symbol(ctx,"isAdd"),2,args03BEA4A0,args03BEA548,args03BEA580));}
{Z3_mk_string_symbol(ctx,"Add");}
{Z3_mk_string_symbol(ctx,"isAdd");}
{Z3_mk_string_symbol(ctx,"refId");}
{Z3_symbol args03CEE190[1] = {Z3_mk_string_symbol(ctx,"refId"), }; Z3_sort args03CEE1C0[1] = {GET(Z3_sort,0x03BC7FD8), }; unsigned args03CEE1F0[1] = {0, }; SET(0x03BE9980, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"Add"),Z3_mk_string_symbol(ctx,"isAdd"),1,args03CEE190,args03CEE1C0,args03CEE1F0));}
{Z3_mk_string_symbol(ctx,"address");}
{Z3_mk_string_symbol(ctx,"isaddress");}
{Z3_mk_string_symbol(ctx,"enc");}
{Z3_mk_string_symbol(ctx,"value1");}
{Z3_mk_string_symbol(ctx,"value2");}
{Z3_symbol args03BEA580[3] = {Z3_mk_string_symbol(ctx,"enc"), Z3_mk_string_symbol(ctx,"value1"), Z3_mk_string_symbol(ctx,"value2"), }; Z3_sort args03BEA628[3] = {GET(Z3_sort,0x03BC7FD8), GET(Z3_sort,0x00000000), GET(Z3_sort,0x00000000), }; unsigned args03BEA660[3] = {0, 0, 0, }; SET(0x03BE99D0, Z3_mk_constructor(ctx,Z3_mk_string_symbol(ctx,"address"),Z3_mk_string_symbol(ctx,"isaddress"),3,args03BEA580,args03BEA628,args03BEA660));}
{Z3_mk_string_symbol(ctx,"object");}
{Z3_constructor args03BEAC18[25] = {GET(Z3_constructor,0x03CEC870), GET(Z3_constructor,0x03CEC8C0), GET(Z3_constructor,0x03CEC910), GET(Z3_constructor,0x03CEC960), GET(Z3_constructor,0x03CEC9B0), GET(Z3_constructor,0x03CECA00), GET(Z3_constructor,0x03CECA50), GET(Z3_constructor,0x03BE9430), GET(Z3_constructor,0x03BE9480), GET(Z3_constructor,0x03BE9520), GET(Z3_constructor,0x03BE94D0), GET(Z3_constructor,0x03BE9570), GET(Z3_constructor,0x03BE95C0), GET(Z3_constructor,0x03BE9610), GET(Z3_constructor,0x03BE9660), GET(Z3_constructor,0x03BE96B0), GET(Z3_constructor,0x03BE9700), GET(Z3_constructor,0x03BE9750), GET(Z3_constructor,0x03BE97A0), GET(Z3_constructor,0x03BE97F0), GET(Z3_constructor,0x03BE9840), GET(Z3_constructor,0x03BE9890), GET(Z3_constructor,0x03BE98E0), GET(Z3_constructor,0x03BE9930), GET(Z3_constructor,0x03BE9980), }; SET(0x03CEE1C0, Z3_mk_constructor_list(ctx,25,args03BEAC18));}
{Z3_mk_string_symbol(ctx,"address");}
{Z3_constructor args03CEE1F0[1] = {GET(Z3_constructor,0x03BE99D0), }; SET(0x03CEE220, Z3_mk_constructor_list(ctx,1,args03CEE1F0));}
{Z3_symbol args03BEA580[2] = {Z3_mk_string_symbol(ctx,"object"), Z3_mk_string_symbol(ctx,"address"), }; Z3_sort args03BEA660[2] = {GET(Z3_sort,0x03BCD088), GET(Z3_sort,0x03BCD0C8), }; Z3_constructor_list args03BEA628[2] = {GET(Z3_constructor_list,0x03CEE1C0), GET(Z3_constructor_list,0x03CEE220), }; Z3_mk_datatypes(ctx,2, args03BEA580, args03BEA660, args03BEA628);SET(0x03BCD088, args03BEA660[0]);SET(0x03BCD0C8, args03BEA660[1]);}
{Z3_del_constructor_list(ctx,GET(Z3_constructor_list,0x03CEE1C0));}
{Z3_del_constructor_list(ctx,GET(Z3_constructor_list,0x03CEE220));}
{Z3_func_decl out002DE0DC; Z3_func_decl out002DE0E0; Z3_query_constructor(ctx,GET(Z3_constructor,0x03CEC870), 0, &out002DE0DC, &out002DE0E0, 0);SET(0x03BEAC30, out002DE0DC);SET(0x03BEB2F0, out002DE0E0);}
{Z3_func_decl out002DE0E0; Z3_func_decl out002DE0E4; Z3_func_decl args03CEE220[1] = {GET(Z3_func_decl,0x03BEB380), }; Z3_query_constructor(ctx,GET(Z3_constructor,0x03BE9840), 1, &out002DE0E0, &out002DE0E4, args03CEE220);SET(0x03BEB1D0, out002DE0E0);SET(0x03BEB338, out002DE0E4);SET(0x03BEB380, args03CEE220[0]);}
{Z3_func_decl out002DE0E0; Z3_func_decl out002DE0E4; Z3_func_decl args03BEA580[2] = {0, GET(Z3_func_decl,0x03BEC478), }; Z3_query_constructor(ctx,GET(Z3_constructor,0x03BE9930), 2, &out002DE0E0, &out002DE0E4, args03BEA580);SET(0x03BE9A20, out002DE0E0);SET(0x03BEB3C8, out002DE0E4);SET(0x03BEC430, args03BEA580[0]);SET(0x03BEC478, args03BEA580[1]); }
{Z3_func_decl out002DE0DC; Z3_func_decl out002DE0E0; Z3_func_decl args03BEA580[3] = {GET(Z3_func_decl,0x03BEC508), GET(Z3_func_decl,0x03BEC550), GET(Z3_func_decl,0x03BEC598), }; Z3_query_constructor(ctx,GET(Z3_constructor,0x03BE99D0), 3, &out002DE0DC, &out002DE0E0, args03BEA580);SET(0x03BE9A70, out002DE0DC);SET(0x03BEC4C0, out002DE0E0);SET(0x03BEC508, args03BEA580[0]);SET(0x03BEC550, args03BEA580[1]);SET(0x03BEC598, args03BEA580[2]);}
{SET(0x03BEB7F0, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BEAC30),0,0));}
{SET(0x03BCD088, Z3_get_domain(ctx,GET(Z3_func_decl,0x03BEC430),0));}
{SET(0x03BEB4F0, Z3_mk_bound(ctx,0,GET(Z3_sort,0x03BCD088)));}
{Z3_ast args03CEE220[1] = {GET(Z3_ast,0x03BEB4F0), }; SET(0x03BEC5E0, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BEC430),1,args03CEE220));}
{SET(0x03BEB4F0, Z3_get_app_arg(ctx,GET(Z3_app,0x03BEC5E0),0));}
{SET(0x03BEC628, Z3_mk_eq(ctx,GET(Z3_ast,0x03BEC5E0),GET(Z3_ast,0x03BEB7F0)));}
{SET(0x03BE9AC0, Z3_get_app_decl(ctx,GET(Z3_app,0x03BEC628)));}
{Z3_ast args03CEE220[1] = {GET(Z3_ast,0x03BEC5E0), }; SET(0x03BEC670, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BEB338),1,args03CEE220));}
{Z3_ast args03CEE220[1] = {GET(Z3_ast,0x03BEC5E0), }; SET(0x03BEC6B8, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BEB3C8),1,args03CEE220));}
{Z3_ast args03BEA580[2] = {GET(Z3_ast,0x03BEC670), GET(Z3_ast,0x03BEC6B8), }; SET(0x03BEC700, Z3_mk_or(ctx,2,args03BEA580));}
{SET(0x03BEC670, Z3_get_app_arg(ctx,GET(Z3_app,0x03BEC700),0));}
{SET(0x03BEC6B8, Z3_get_app_arg(ctx,GET(Z3_app,0x03BEC700),1));}
{Z3_ast args03BEA580[3] = {GET(Z3_ast,0x03BEC670), GET(Z3_ast,0x03BEC6B8), GET(Z3_ast,0x03BEC628), }; SET(0x03BE9B10, Z3_mk_or(ctx,3,args03BEA580));}
{Z3_mk_string_symbol(ctx,"x0");}
{Z3_sort args03CEE250[1] = {GET(Z3_sort,0x03BCD088), }; Z3_symbol args03CEE1F0[1] = {Z3_mk_string_symbol(ctx,"x0"), }; SET(0x03BED418, Z3_mk_quantifier(ctx,1,0,0,0,1,args03CEE250,args03CEE1F0,GET(Z3_ast,0x03BE9B10)));}
{Z3_assert_cnstr(ctx,GET(Z3_ast,0x03BED418));}
{SET(0x03BCD088, Z3_get_domain(ctx,GET(Z3_func_decl,0x03BEC478),0));}
{Z3_ast args03CEE1F0[1] = {GET(Z3_ast,0x03BEB4F0), }; SET(0x03BEC790, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BEC478),1,args03CEE1F0));}
{Z3_ast args03BEAB30[2] = {GET(Z3_ast,0x03BEC790), GET(Z3_ast,0x03BEB7F0), }; SET(0x03BEC820, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BE9AC0),2,args03BEAB30));}
{Z3_ast args03CEE1F0[1] = {GET(Z3_ast,0x03BEC790), }; SET(0x03BEC868, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BEB338),1,args03CEE1F0));}
{Z3_ast args03CEE1F0[1] = {GET(Z3_ast,0x03BEC790), }; SET(0x03BEC8B0, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BEB3C8),1,args03CEE1F0));}
{Z3_ast args03BEAB30[2] = {GET(Z3_ast,0x03BEC868), GET(Z3_ast,0x03BEC8B0), }; SET(0x03BEC8F8, Z3_mk_or(ctx,2,args03BEAB30));}
{SET(0x03BEC868, Z3_get_app_arg(ctx,GET(Z3_app,0x03BEC8F8),0));}
{SET(0x03BEC8B0, Z3_get_app_arg(ctx,GET(Z3_app,0x03BEC8F8),1));}
{Z3_ast args03BEAB30[3] = {GET(Z3_ast,0x03BEC868), GET(Z3_ast,0x03BEC8B0), GET(Z3_ast,0x03BEC820), }; SET(0x03BE9BB0, Z3_mk_or(ctx,3,args03BEAB30));}
{Z3_mk_string_symbol(ctx,"x0");}
{Z3_sort args03CEE280[1] = {GET(Z3_sort,0x03BCD088), }; Z3_symbol args03CEE2B0[1] = {Z3_mk_string_symbol(ctx,"x0"), }; SET(0x03BEE758, Z3_mk_quantifier(ctx,1,0,0,0,1,args03CEE280,args03CEE2B0,GET(Z3_ast,0x03BE9BB0)));}
{Z3_assert_cnstr(ctx,GET(Z3_ast,0x03BEE758));}
{SET(0x03BEB8F0, Z3_mk_fresh_const(ctx,"x",GET(Z3_sort,0x03BCD088)));}
{Z3_ast args03BEAB30[2] = {GET(Z3_ast,0x03BEB8F0), GET(Z3_ast,0x03BEB7F0), }; SET(0x03BEC9D0, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BE9AC0),2,args03BEAB30));}
{Z3_ast args03CEE2B0[1] = {GET(Z3_ast,0x03BEB8F0), }; SET(0x03BECA18, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BEB338),1,args03CEE2B0));}
{Z3_ast args03CEE2B0[1] = {GET(Z3_ast,0x03BEB8F0), }; SET(0x03BECA60, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BEB3C8),1,args03CEE2B0));}
{Z3_ast args03BEAB30[2] = {GET(Z3_ast,0x03BECA18), GET(Z3_ast,0x03BECA60), }; SET(0x03BECAA8, Z3_mk_or(ctx,2,args03BEAB30));}
{SET(0x03BECA18, Z3_get_app_arg(ctx,GET(Z3_app,0x03BECAA8),0));}
{SET(0x03BECA60, Z3_get_app_arg(ctx,GET(Z3_app,0x03BECAA8),1));}
{Z3_ast args03BEAB30[3] = {GET(Z3_ast,0x03BECA18), GET(Z3_ast,0x03BECA60), GET(Z3_ast,0x03BEC9D0), }; SET(0x03BE9C50, Z3_mk_or(ctx,3,args03BEAB30));}
{Z3_assert_cnstr(ctx,GET(Z3_ast,0x03BE9C50));}
Z3_push(ctx);
{(Z3_check_and_get_model(ctx,0));}
{SET(0x03BFD780, Z3_mk_int(ctx,2,GET(Z3_sort,0x03BC7FD8)));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03BFD780), 10);}
{SET(0x03C0DC08, Z3_mk_not(ctx,GET(Z3_ast,0x03BEC9D0)));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C0DC08), 10);}
{SET(0x03C094A0, Z3_mk_ite(ctx,GET(Z3_ast,0x03BECA18),GET(Z3_ast,0x03BEB8F0),GET(Z3_ast,0x03BEB7F0)));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C094A0), 10);}
{SET(0x03BECA18, Z3_get_app_arg(ctx,GET(Z3_app,0x03C094A0),0));}
{SET(0x03BEB8F0, Z3_get_app_arg(ctx,GET(Z3_app,0x03C094A0),1));}
{SET(0x03BEB7F0, Z3_get_app_arg(ctx,GET(Z3_app,0x03C094A0),2));}
{SET(0x03C0DC50, Z3_mk_not(ctx,GET(Z3_ast,0x03BECA18)));}
{SET(0x03BECA18, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DC50),0));}
{Z3_ast args03C03310[1] = {GET(Z3_ast,0x03BEC9D0), }; SET(0x03C0DC98, Z3_mk_or(ctx,1,args03C03310));}
{SET(0x03C0DCE0, Z3_mk_implies(ctx,GET(Z3_ast,0x03BECA18),GET(Z3_ast,0x03C0DC98)));}
{SET(0x03C0DD28, Z3_mk_not(ctx,GET(Z3_ast,0x03C0DCE0)));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C0DD28), 10);}
{SET(0x03C0DCE0, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DD28),0));}
{SET(0x03BECA18, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DCE0),0));}
{SET(0x03C0DC98, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DCE0),1));}
{SET(0x03BEC9D0, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DC98),0));}
{SET(0x03BEB8F0, Z3_get_app_arg(ctx,GET(Z3_app,0x03BEC9D0),0));}
{SET(0x03BEB7F0, Z3_get_app_arg(ctx,GET(Z3_app,0x03BEC9D0),1));}
{Z3_ast args03C07F90[3] = {GET(Z3_ast,0x03BCCE08), GET(Z3_ast,0x03BEB7F0), GET(Z3_ast,0x03BEB7F0), }; SET(0x03C094F0, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BE9A70),3,args03C07F90));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C094F0), 10);}
{Z3_ast args03C07F90[3] = {GET(Z3_ast,0x03BFD780), GET(Z3_ast,0x03BEB7F0), GET(Z3_ast,0x03BEB7F0), }; SET(0x03C09540, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BE9A70),3,args03C07F90));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C09540), 10);}
{SET(0x03BECA18, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DCE0),0));}
{SET(0x03C0DC98, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DCE0),1));}
{SET(0x03BEC9D0, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DC98),0));}
{Z3_pop(ctx,1);}
{Z3_ast args03BFED58[2] = {GET(Z3_ast,0x03BECA18), GET(Z3_ast,0x03BEC9D0), }; SET(0x03BFF5D8, Z3_mk_or(ctx,2,args03BFED58));}
{SET(0x03BECA18, Z3_get_app_arg(ctx,GET(Z3_app,0x03BFF5D8),0));}
{SET(0x03BEC9D0, Z3_get_app_arg(ctx,GET(Z3_app,0x03BFF5D8),1));}
{SET(0x03BEB8F0, Z3_get_app_arg(ctx,GET(Z3_app,0x03BEC9D0),0));}
{SET(0x03BEB7F0, Z3_get_app_arg(ctx,GET(Z3_app,0x03BEC9D0),1));}
Z3_push(ctx);
{Z3_ast args03BC3DF8[1] = {GET(Z3_ast,0x03BEB8F0), }; SET(0x03C0D980, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BEB380),1,args03BC3DF8));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C0D980), 10);}
{Z3_ast args03BFED58[2] = {GET(Z3_ast,0x03C0D980), GET(Z3_ast,0x03BCCE08), }; SET(0x03C0D9C8, Z3_mk_app(ctx,GET(Z3_func_decl,0x03CEC820),2,args03BFED58));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C0D9C8), 10);}
{Z3_ast args03BFED58[2] = {GET(Z3_ast,0x03C0D980), GET(Z3_ast,0x03BFD780), }; SET(0x03C0DD70, Z3_mk_app(ctx,GET(Z3_func_decl,0x03CEC820),2,args03BFED58));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C0DD70), 10);}
{Z3_ast args03BFED58[2] = {GET(Z3_ast,0x03C0D9C8), GET(Z3_ast,0x03C0DD70), }; SET(0x03C0DDB8, Z3_mk_or(ctx,2,args03BFED58));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C0DDB8), 10);}
{SET(0x03C0DCE0, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DD28),0));}
{SET(0x03BECA18, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DCE0),0));}
{SET(0x03C0DC98, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DCE0),1));}
{SET(0x03BEC9D0, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DC98),0));}
{Z3_pop(ctx,1);}
{Z3_ast args03BFED58[2] = {GET(Z3_ast,0x03BECA60), GET(Z3_ast,0x03BEC9D0), }; SET(0x03C0DE00, Z3_mk_or(ctx,2,args03BFED58));}
{SET(0x03BECA60, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DE00),0));}
{SET(0x03BEC9D0, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DE00),1));}
{SET(0x03BEB8F0, Z3_get_app_arg(ctx,GET(Z3_app,0x03BEC9D0),0));}
{SET(0x03BEB7F0, Z3_get_app_arg(ctx,GET(Z3_app,0x03BEC9D0),1));}
Z3_push(ctx);
{Z3_ast args03BC3DF8[1] = {GET(Z3_ast,0x03BEB8F0), }; SET(0x03BFF590, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BEC430),1,args03BC3DF8));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03BFF590), 10);}
{Z3_ast args03BFED58[2] = {GET(Z3_ast,0x03BFF590), GET(Z3_ast,0x03BEB7F0), }; SET(0x03C0DE90, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BE9AC0),2,args03BFED58));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C0DE90), 10);}
{SET(0x03C0DE48, Z3_mk_not(ctx,GET(Z3_ast,0x03C0DE90)));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C0DE48), 10);}
{Z3_ast args03BC3DF8[1] = {GET(Z3_ast,0x03BFF590), }; SET(0x03BFFC08, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BEB338),1,args03BC3DF8));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03BFFC08), 10);}
{SET(0x03C00440, Z3_mk_ite(ctx,GET(Z3_ast,0x03BFFC08),GET(Z3_ast,0x03BFF590),GET(Z3_ast,0x03BEB7F0)));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C00440), 10);}
{SET(0x03BFFC08, Z3_get_app_arg(ctx,GET(Z3_app,0x03C00440),0));}
{SET(0x03BFF590, Z3_get_app_arg(ctx,GET(Z3_app,0x03C00440),1));}
{SET(0x03BEB7F0, Z3_get_app_arg(ctx,GET(Z3_app,0x03C00440),2));}
{SET(0x03C0DED8, Z3_mk_not(ctx,GET(Z3_ast,0x03BFFC08)));}
{SET(0x03BFFC08, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DED8),0));}
{Z3_ast args03BC3DF8[1] = {GET(Z3_ast,0x03C0DE90), }; SET(0x03C0DF20, Z3_mk_or(ctx,1,args03BC3DF8));}
{SET(0x03C0DF68, Z3_mk_implies(ctx,GET(Z3_ast,0x03BFFC08),GET(Z3_ast,0x03C0DF20)));}
{SET(0x03C0DFB0, Z3_mk_not(ctx,GET(Z3_ast,0x03C0DF68)));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C0DFB0), 10);}
{SET(0x03C0DF68, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DFB0),0));}
{SET(0x03BCCE08, Z3_get_app_arg(ctx,GET(Z3_app,0x03C094F0),0));}
{SET(0x03BEB7F0, Z3_get_app_arg(ctx,GET(Z3_app,0x03C094F0),1));}
{SET(0x03BEB7F0, Z3_get_app_arg(ctx,GET(Z3_app,0x03C094F0),2));}
{SET(0x03BFD780, Z3_get_app_arg(ctx,GET(Z3_app,0x03C09540),0));}
{SET(0x03BEB7F0, Z3_get_app_arg(ctx,GET(Z3_app,0x03C09540),1));}
{SET(0x03BEB7F0, Z3_get_app_arg(ctx,GET(Z3_app,0x03C09540),2));}
{SET(0x03BFFC08, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DF68),0));}
{SET(0x03C0DF20, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DF68),1));}
{SET(0x03C0DE90, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DF20),0));}
{Z3_pop(ctx,1);}
{Z3_ast args03BFED58[2] = {GET(Z3_ast,0x03BFFC08), GET(Z3_ast,0x03C0DE90), }; SET(0x03C0DFF8, Z3_mk_or(ctx,2,args03BFED58));}
{SET(0x03BFFC08, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DFF8),0));}
{SET(0x03C0DE90, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DFF8),1));}
{SET(0x03BFF590, Z3_get_app_arg(ctx,GET(Z3_app,0x03BFFC08),0));}
{SET(0x03BEB8F0, Z3_get_app_arg(ctx,GET(Z3_app,0x03BFF590),0));}
{SET(0x03BFF590, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DE90),0));}
{SET(0x03BEB7F0, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DE90),1));}
Z3_push(ctx);
{Z3_ast args03BC3DF8[1] = {GET(Z3_ast,0x03BFF590), }; SET(0x03C0E040, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BEB380),1,args03BC3DF8));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C0E040), 10);}
{Z3_ast args03BFED58[2] = {GET(Z3_ast,0x03C0E040), GET(Z3_ast,0x03BCCE08), }; SET(0x03C0E088, Z3_mk_app(ctx,GET(Z3_func_decl,0x03CEC820),2,args03BFED58));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C0E088), 10);}
{Z3_ast args03BFED58[2] = {GET(Z3_ast,0x03C0E040), GET(Z3_ast,0x03BFD780), }; SET(0x03C0E0D0, Z3_mk_app(ctx,GET(Z3_func_decl,0x03CEC820),2,args03BFED58));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C0E0D0), 10);}
{Z3_ast args03BFED58[2] = {GET(Z3_ast,0x03C0E088), GET(Z3_ast,0x03C0E0D0), }; SET(0x03C0E118, Z3_mk_or(ctx,2,args03BFED58));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C0E118), 10);}
{Z3_ast args03BC3DF8[1] = {GET(Z3_ast,0x03BEB8F0), }; SET(0x03BFF7D0, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BEC478),1,args03BC3DF8));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03BFF7D0), 10);}
{Z3_ast args03BFED58[2] = {GET(Z3_ast,0x03BFF7D0), GET(Z3_ast,0x03BEB7F0), }; SET(0x03C0E1A8, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BE9AC0),2,args03BFED58));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C0E1A8), 10);}
{SET(0x03C0E160, Z3_mk_not(ctx,GET(Z3_ast,0x03C0E1A8)));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C0E160), 10);}
{Z3_ast args03BC3DF8[1] = {GET(Z3_ast,0x03BFF7D0), }; SET(0x03BFF980, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BEB338),1,args03BC3DF8));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03BFF980), 10);}
{SET(0x03C00580, Z3_mk_ite(ctx,GET(Z3_ast,0x03BFF980),GET(Z3_ast,0x03BFF7D0),GET(Z3_ast,0x03BEB7F0)));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C00580), 10);}
{SET(0x03BFF980, Z3_get_app_arg(ctx,GET(Z3_app,0x03C00580),0));}
{SET(0x03BFF7D0, Z3_get_app_arg(ctx,GET(Z3_app,0x03C00580),1));}
{SET(0x03BEB7F0, Z3_get_app_arg(ctx,GET(Z3_app,0x03C00580),2));}
{SET(0x03C0E1F0, Z3_mk_not(ctx,GET(Z3_ast,0x03BFF980)));}
{Z3_ast args03BFED58[2] = {GET(Z3_ast,0x03C0E1A8), GET(Z3_ast,0x03C0E1F0), }; SET(0x03C0E238, Z3_mk_or(ctx,2,args03BFED58));}
{SET(0x03C0E1A8, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0E238),0));}
{SET(0x03C0E1F0, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0E238),1));}
{SET(0x03BFF980, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0E1F0),0));}
{Z3_ast args03BFED58[2] = {GET(Z3_ast,0x03BFF980), GET(Z3_ast,0x03C0E160), }; SET(0x03C0E280, Z3_mk_and(ctx,2,args03BFED58));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C0E280), 10);}
{SET(0x03C0E2C8, Z3_mk_not(ctx,GET(Z3_ast,0x03C0E280)));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C0E2C8), 10);}
{SET(0x03C0E280, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0E2C8),0));}
{SET(0x03BFF980, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0E280),0));}
{SET(0x03C0E160, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0E280),1));}
{SET(0x03C0E1A8, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0E160),0));}
{Z3_pop(ctx,1);}
Z3_push(ctx);
{Z3_pop(ctx,1);}
{SET(0x03C0E280, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0E2C8),0));}
{SET(0x03BFF980, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0E280),0));}
{SET(0x03C0E160, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0E280),1));}
{Z3_ast args03BFED58[2] = {GET(Z3_ast,0x03BFF980), GET(Z3_ast,0x03C0E1A8), }; SET(0x03C0E310, Z3_mk_or(ctx,2,args03BFED58));}
{SET(0x03BFF980, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0E310),0));}
{SET(0x03C0E1A8, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0E310),1));}
{SET(0x03BFF7D0, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0E1A8),0));}
{SET(0x03BEB7F0, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0E1A8),1));}
Z3_push(ctx);
{Z3_ast args03BC3DF8[1] = {GET(Z3_ast,0x03BFF7D0), }; SET(0x03C0E358, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BEB380),1,args03BC3DF8));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C0E358), 10);}
{Z3_ast args03BFED58[2] = {GET(Z3_ast,0x03C0E358), GET(Z3_ast,0x03BCCE08), }; SET(0x03C0E3A0, Z3_mk_app(ctx,GET(Z3_func_decl,0x03CEC820),2,args03BFED58));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C0E3A0), 10);}
{Z3_ast args03BFED58[2] = {GET(Z3_ast,0x03C0E358), GET(Z3_ast,0x03BFD780), }; SET(0x03C0E3E8, Z3_mk_app(ctx,GET(Z3_func_decl,0x03CEC820),2,args03BFED58));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C0E3E8), 10);}
{Z3_ast args03BFED58[2] = {GET(Z3_ast,0x03C0E3A0), GET(Z3_ast,0x03C0E3E8), }; SET(0x03BEEC08, Z3_mk_or(ctx,2,args03BFED58));}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03BEEC08), 10);}
{SET(0x03C0DCE0, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DD28),0));}
{Z3_pop(ctx,1);}
Z3_push(ctx);
{SET(0x03C0E280, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0E2C8),0));}
{SET(0x03BFF980, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0E280),0));}
{SET(0x03C0E160, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0E280),1));}
{Z3_pop(ctx,1);}
{Z3_ast args03BEEC50[7] = {GET(Z3_ast,0x03BFF980), GET(Z3_ast,0x03C0DE48), GET(Z3_ast,0x03C0DFB0), GET(Z3_ast,0x03C0DCE0), GET(Z3_ast,0x03C0E118), GET(Z3_ast,0x03C0E160), GET(Z3_ast,0x03BEEC08), }; SET(0x03BEE6E8, Z3_mk_and(ctx,7,args03BEEC50));}
{Z3_ast args03BFED58[2] = {GET(Z3_ast,0x03C0DD28), GET(Z3_ast,0x03C0DDB8), }; SET(0x03BEEC50, Z3_mk_and(ctx,2,args03BFED58));}
{Z3_ast args03BFED58[2] = {GET(Z3_ast,0x03BEE6E8), GET(Z3_ast,0x03BEEC50), }; SET(0x03BEEC98, Z3_mk_or(ctx,2,args03BFED58));}
{SET(0x03BEE6E8, Z3_get_app_arg(ctx,GET(Z3_app,0x03BEEC98),0));}
{SET(0x03BEEC50, Z3_get_app_arg(ctx,GET(Z3_app,0x03BEEC98),1));}
{SET(0x03C0DD28, Z3_get_app_arg(ctx,GET(Z3_app,0x03BEEC50),0));}
{SET(0x03C0DDB8, Z3_get_app_arg(ctx,GET(Z3_app,0x03BEEC50),1));}
{SET(0x03C0D9C8, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DDB8),0));}
{SET(0x03C0DD70, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DDB8),1));}
{SET(0x03C0D980, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DD70),0));}
{SET(0x03BFD780, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0DD70),1));}
{SET(0x03BEB8F0, Z3_get_app_arg(ctx,GET(Z3_app,0x03C0D980),0));}
Z3_push(ctx);
{Z3_assert_cnstr(ctx,GET(Z3_ast,0x03C0DC08));}
{Z3_assert_cnstr(ctx,GET(Z3_ast,0x03BEEC98));}
Z3_push(ctx);
{(Z3_check_and_get_model(ctx,&_m));}
{Z3_ast out002DE120; Z3_eval(ctx,_m, GET(Z3_ast,0x03BEB8F0), &out002DE120);SET(0x03C14AE8, out002DE120);}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C14AE8), 2);}
{Z3_ast args03C123F8[2] = {GET(Z3_ast,0x03BEB8F0), GET(Z3_ast,0x03C14AE8), }; SET(0x03C14B78, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BE9AC0),2,args03C123F8));}
{Z3_ast args03BC3F18[1] = {GET(Z3_ast,0x03C14B78), }; SET(0x03C14B30, Z3_mk_and(ctx,1,args03BC3F18));}
{SET(0x03C14BC0, Z3_mk_not(ctx,GET(Z3_ast,0x03C14B30)));}
{Z3_assert_cnstr(ctx,GET(Z3_ast,0x03C14BC0));}
{(Z3_check_and_get_model(ctx,&_m));}
{Z3_ast out002DE120; Z3_eval(ctx,_m, GET(Z3_ast,0x03BEB8F0), &out002DE120);SET(0x03C127D0, out002DE120);}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C127D0), 2);}
{Z3_ast args03C037E8[2] = {GET(Z3_ast,0x03BEB8F0), GET(Z3_ast,0x03C127D0), }; SET(0x03C028D0, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BE9AC0),2,args03C037E8));}
{Z3_ast args03BC3EE8[1] = {GET(Z3_ast,0x03C028D0), }; SET(0x03C1F100, Z3_mk_and(ctx,1,args03BC3EE8));}
{SET(0x03C1F148, Z3_mk_not(ctx,GET(Z3_ast,0x03C1F100)));}
{Z3_assert_cnstr(ctx,GET(Z3_ast,0x03C1F148));}
{(Z3_check_and_get_model(ctx,&_m));}
{Z3_ast out002DE120; Z3_eval(ctx,_m, GET(Z3_ast,0x03BEB8F0), &out002DE120);SET(0x03C1F5C8, out002DE120);}
{Z3_persist_ast(ctx,GET(Z3_ast,0x03C1F5C8), 2);}
{Z3_ast args03C05F78[2] = {GET(Z3_ast,0x03BEB8F0), GET(Z3_ast,0x03C1F5C8), }; SET(0x03C23580, Z3_mk_app(ctx,GET(Z3_func_decl,0x03BE9AC0),2,args03C05F78));}
{Z3_ast args03CEE490[1] = {GET(Z3_ast,0x03C23580), }; SET(0x03C23538, Z3_mk_and(ctx,1,args03CEE490));}
{SET(0x03C235C8, Z3_mk_not(ctx,GET(Z3_ast,0x03C23538)));}
{Z3_assert_cnstr(ctx,GET(Z3_ast,0x03C235C8));}
//{Z3_check(ctx);}
}

void test_apps() {
    Z3_config cfg = Z3_mk_config();
    Z3_set_param_value(cfg,"MODEL","true");
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_symbol A = Z3_mk_string_symbol(ctx, "A");
    Z3_symbol F = Z3_mk_string_symbol(ctx, "f");
    Z3_sort SA = Z3_mk_uninterpreted_sort(ctx, A);
    Z3_func_decl f = Z3_mk_func_decl(ctx, F, 1, &SA, SA);
    Z3_symbol X = Z3_mk_string_symbol(ctx, "x");
    Z3_ast x = Z3_mk_const(ctx, X, SA);
    Z3_ast fx = Z3_mk_app(ctx, f, 1, &x);
    Z3_ast ffx = Z3_mk_app(ctx, f, 1, &fx);
    Z3_ast fffx = Z3_mk_app(ctx, f, 1, &ffx);
    Z3_ast ffffx = Z3_mk_app(ctx, f, 1, &fffx);
    Z3_ast fffffx = Z3_mk_app(ctx, f, 1, &ffffx);

    Z3_ast fml = Z3_mk_not(ctx, Z3_mk_eq(ctx, x, fffffx));
    
    Z3_assert_cnstr(ctx, fml);
    Z3_lbool r = Z3_check(ctx);
    std::cout << r << "\n";
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_bvneg() {
    Z3_config cfg = Z3_mk_config();
    Z3_set_param_value(cfg,"MODEL","true");
    Z3_context ctx = Z3_mk_context(cfg);

    {
        Z3_sort bv30 = Z3_mk_bv_sort(ctx, 30);
        Z3_ast  x30 = Z3_mk_fresh_const(ctx, "x", bv30);
        Z3_ast fml = Z3_mk_eq(ctx, Z3_mk_int(ctx, -1, bv30), 
                              Z3_mk_bvadd(ctx, Z3_mk_int(ctx, 0, bv30), 
                                      x30));        
        Z3_assert_cnstr(ctx, fml);
        Z3_lbool r = Z3_check(ctx);
        std::cout << r << "\n";
    }

    {
        Z3_sort bv31 = Z3_mk_bv_sort(ctx, 31);
        Z3_ast  x31 = Z3_mk_fresh_const(ctx, "x", bv31);
        Z3_ast fml = Z3_mk_eq(ctx, Z3_mk_int(ctx, -1, bv31), 
                              Z3_mk_bvadd(ctx, Z3_mk_int(ctx, 0, bv31), 
                                      x31));        
        Z3_assert_cnstr(ctx, fml);
        Z3_lbool r = Z3_check(ctx);
        std::cout << r << "\n";
    }

    {
        Z3_sort bv32 = Z3_mk_bv_sort(ctx, 32);
        Z3_ast  x32 = Z3_mk_fresh_const(ctx, "x", bv32);
        Z3_ast fml = Z3_mk_eq(ctx, 
                              Z3_mk_int(ctx,-1, bv32), 
                              Z3_mk_bvadd(ctx, Z3_mk_int(ctx, 0, bv32), 
                                          x32));        
        Z3_assert_cnstr(ctx, fml);
        Z3_lbool r = Z3_check(ctx);
        std::cout << r << "\n";
    }

    Z3_del_config(cfg);
    Z3_del_context(ctx);    
}

void tst_api() {
    test_apps();
    test_bvneg();
    // bv_invariant();
}
#else
void tst_api() {
}
#endif
