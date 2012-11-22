// Automatically generated file
#include<jni.h>
#include<stdlib.h>
#include"z3.h"
#ifdef __cplusplus
extern "C" {
#endif
JNIEXPORT jlong JNICALL Java_Z3Native_mkConfig(JNIEnv * jenv, jclass cls) {
  Z3_config result = Z3_mk_config();
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_delConfig(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_del_config((Z3_config)a0);
}
JNIEXPORT void JNICALL Java_Z3Native_setParamValue(JNIEnv * jenv, jclass cls, jlong a0, jstring a1, jstring a2) {
  Z3_string _a1 = (Z3_string) jenv->GetStringUTFChars(a1, NULL);
  Z3_string _a2 = (Z3_string) jenv->GetStringUTFChars(a2, NULL);
  Z3_set_param_value((Z3_config)a0, _a1, _a2);
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkContext(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_context result = Z3_mk_context((Z3_config)a0);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkContextRc(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_context result = Z3_mk_context_rc((Z3_config)a0);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_delContext(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_del_context((Z3_context)a0);
}
JNIEXPORT void JNICALL Java_Z3Native_incRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_inc_ref((Z3_context)a0, (Z3_ast)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_decRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_dec_ref((Z3_context)a0, (Z3_ast)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_updateParamValue(JNIEnv * jenv, jclass cls, jlong a0, jstring a1, jstring a2) {
  Z3_string _a1 = (Z3_string) jenv->GetStringUTFChars(a1, NULL);
  Z3_string _a2 = (Z3_string) jenv->GetStringUTFChars(a2, NULL);
  Z3_update_param_value((Z3_context)a0, _a1, _a2);
}
JNIEXPORT jboolean JNICALL Java_Z3Native_getParamValue(JNIEnv * jenv, jclass cls, jlong a0, jstring a1, jobject a2) {
  Z3_string _a1 = (Z3_string) jenv->GetStringUTFChars(a1, NULL);
  Z3_string _a2;
  Z3_bool result = Z3_get_param_value((Z3_context)a0, _a1, &_a2);
  {
     jclass mc    = jenv->GetObjectClass(a2);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a2, fid, (jlong) _a2);
  }
  return (jboolean) result;
}
JNIEXPORT void JNICALL Java_Z3Native_interrupt(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_interrupt((Z3_context)a0);
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkParams(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_params result = Z3_mk_params((Z3_context)a0);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_paramsIncRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_params_inc_ref((Z3_context)a0, (Z3_params)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_paramsDecRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_params_dec_ref((Z3_context)a0, (Z3_params)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_paramsSetBool(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jboolean a3) {
  Z3_params_set_bool((Z3_context)a0, (Z3_params)a1, (Z3_symbol)a2, (Z3_bool)a3);
}
JNIEXPORT void JNICALL Java_Z3Native_paramsSetUint(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jint a3) {
  Z3_params_set_uint((Z3_context)a0, (Z3_params)a1, (Z3_symbol)a2, (unsigned)a3);
}
JNIEXPORT void JNICALL Java_Z3Native_paramsSetDouble(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jdouble a3) {
  Z3_params_set_double((Z3_context)a0, (Z3_params)a1, (Z3_symbol)a2, (double)a3);
}
JNIEXPORT void JNICALL Java_Z3Native_paramsSetSymbol(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jlong a3) {
  Z3_params_set_symbol((Z3_context)a0, (Z3_params)a1, (Z3_symbol)a2, (Z3_symbol)a3);
}
JNIEXPORT jstring JNICALL Java_Z3Native_paramsToString(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_string result = Z3_params_to_string((Z3_context)a0, (Z3_params)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT void JNICALL Java_Z3Native_paramsValidate(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_params_validate((Z3_context)a0, (Z3_params)a1, (Z3_param_descrs)a2);
}
JNIEXPORT void JNICALL Java_Z3Native_paramDescrsIncRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_param_descrs_inc_ref((Z3_context)a0, (Z3_param_descrs)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_paramDescrsDecRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_param_descrs_dec_ref((Z3_context)a0, (Z3_param_descrs)a1);
}
JNIEXPORT jint JNICALL Java_Z3Native_paramDescrsGetKind(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  unsigned result = Z3_param_descrs_get_kind((Z3_context)a0, (Z3_param_descrs)a1, (Z3_symbol)a2);
  return (jint) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_paramDescrsSize(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_param_descrs_size((Z3_context)a0, (Z3_param_descrs)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_paramDescrsGetName(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_symbol result = Z3_param_descrs_get_name((Z3_context)a0, (Z3_param_descrs)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jstring JNICALL Java_Z3Native_paramDescrsToString(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_string result = Z3_param_descrs_to_string((Z3_context)a0, (Z3_param_descrs)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkIntSymbol(JNIEnv * jenv, jclass cls, jlong a0, jint a1) {
  Z3_symbol result = Z3_mk_int_symbol((Z3_context)a0, (int)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkStringSymbol(JNIEnv * jenv, jclass cls, jlong a0, jstring a1) {
  Z3_string _a1 = (Z3_string) jenv->GetStringUTFChars(a1, NULL);
  Z3_symbol result = Z3_mk_string_symbol((Z3_context)a0, _a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkUninterpretedSort(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_sort result = Z3_mk_uninterpreted_sort((Z3_context)a0, (Z3_symbol)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBoolSort(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_sort result = Z3_mk_bool_sort((Z3_context)a0);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkIntSort(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_sort result = Z3_mk_int_sort((Z3_context)a0);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkRealSort(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_sort result = Z3_mk_real_sort((Z3_context)a0);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvSort(JNIEnv * jenv, jclass cls, jlong a0, jint a1) {
  Z3_sort result = Z3_mk_bv_sort((Z3_context)a0, (unsigned)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkFiniteDomainSort(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_sort result = Z3_mk_finite_domain_sort((Z3_context)a0, (Z3_symbol)a1, (__uint64)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkArraySort(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_sort result = Z3_mk_array_sort((Z3_context)a0, (Z3_sort)a1, (Z3_sort)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkTupleSort(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jlongArray a3, jlongArray a4, jobject a5, jlongArray a6) {
  Z3_symbol * _a3 = (Z3_symbol *) jenv->GetLongArrayElements(a3, NULL);
  Z3_sort * _a4 = (Z3_sort *) jenv->GetLongArrayElements(a4, NULL);
  Z3_func_decl _a5;
  Z3_func_decl * _a6 = (Z3_func_decl *) malloc(((unsigned)a2) * sizeof(Z3_func_decl));
  Z3_sort result = Z3_mk_tuple_sort((Z3_context)a0, (Z3_symbol)a1, (unsigned)a2, _a3, _a4, &_a5, _a6);
  jenv->ReleaseLongArrayElements(a3, (jlong *) _a3, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a4, (jlong *) _a4, JNI_ABORT);
  {
     jclass mc    = jenv->GetObjectClass(a5);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a5, fid, (jlong) _a5);
  }
  jenv->SetLongArrayRegion(a6, 0, (jsize)a2, (jlong *) _a6);
  free(_a6);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkEnumerationSort(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jlongArray a3, jlongArray a4, jlongArray a5) {
  Z3_symbol * _a3 = (Z3_symbol *) jenv->GetLongArrayElements(a3, NULL);
  Z3_func_decl * _a4 = (Z3_func_decl *) malloc(((unsigned)a2) * sizeof(Z3_func_decl));
  Z3_func_decl * _a5 = (Z3_func_decl *) malloc(((unsigned)a2) * sizeof(Z3_func_decl));
  Z3_sort result = Z3_mk_enumeration_sort((Z3_context)a0, (Z3_symbol)a1, (unsigned)a2, _a3, _a4, _a5);
  jenv->ReleaseLongArrayElements(a3, (jlong *) _a3, JNI_ABORT);
  jenv->SetLongArrayRegion(a4, 0, (jsize)a2, (jlong *) _a4);
  free(_a4);
  jenv->SetLongArrayRegion(a5, 0, (jsize)a2, (jlong *) _a5);
  free(_a5);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkListSort(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jobject a3, jobject a4, jobject a5, jobject a6, jobject a7, jobject a8) {
  Z3_func_decl _a3;
  Z3_func_decl _a4;
  Z3_func_decl _a5;
  Z3_func_decl _a6;
  Z3_func_decl _a7;
  Z3_func_decl _a8;
  Z3_sort result = Z3_mk_list_sort((Z3_context)a0, (Z3_symbol)a1, (Z3_sort)a2, &_a3, &_a4, &_a5, &_a6, &_a7, &_a8);
  {
     jclass mc    = jenv->GetObjectClass(a3);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a3, fid, (jlong) _a3);
  }
  {
     jclass mc    = jenv->GetObjectClass(a4);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a4, fid, (jlong) _a4);
  }
  {
     jclass mc    = jenv->GetObjectClass(a5);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a5, fid, (jlong) _a5);
  }
  {
     jclass mc    = jenv->GetObjectClass(a6);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a6, fid, (jlong) _a6);
  }
  {
     jclass mc    = jenv->GetObjectClass(a7);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a7, fid, (jlong) _a7);
  }
  {
     jclass mc    = jenv->GetObjectClass(a8);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a8, fid, (jlong) _a8);
  }
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkConstructor(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jint a3, jlongArray a4, jlongArray a5, jintArray a6) {
  Z3_symbol * _a4 = (Z3_symbol *) jenv->GetLongArrayElements(a4, NULL);
  Z3_sort * _a5 = (Z3_sort *) jenv->GetLongArrayElements(a5, NULL);
  unsigned * _a6 = (unsigned *) jenv->GetIntArrayElements(a6, NULL);
  Z3_constructor result = Z3_mk_constructor((Z3_context)a0, (Z3_symbol)a1, (Z3_symbol)a2, (unsigned)a3, _a4, _a5, _a6);
  jenv->ReleaseLongArrayElements(a4, (jlong *) _a4, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a5, (jlong *) _a5, JNI_ABORT);
  jenv->ReleaseIntArrayElements(a6, (jint *) _a6, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_delConstructor(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_del_constructor((Z3_context)a0, (Z3_constructor)a1);
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkDatatype(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jlongArray a3) {
  Z3_constructor * _a3 = (Z3_constructor *) jenv->GetLongArrayElements(a3, NULL);
  Z3_sort result = Z3_mk_datatype((Z3_context)a0, (Z3_symbol)a1, (unsigned)a2, _a3);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkConstructorList(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlongArray a2) {
  Z3_constructor * _a2 = (Z3_constructor *) jenv->GetLongArrayElements(a2, NULL);
  Z3_constructor_list result = Z3_mk_constructor_list((Z3_context)a0, (unsigned)a1, _a2);
  jenv->ReleaseLongArrayElements(a2, (jlong *) _a2, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_delConstructorList(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_del_constructor_list((Z3_context)a0, (Z3_constructor_list)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_mkDatatypes(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlongArray a2, jlongArray a3, jlongArray a4) {
  Z3_symbol * _a2 = (Z3_symbol *) jenv->GetLongArrayElements(a2, NULL);
  Z3_sort * _a3 = (Z3_sort *) malloc(((unsigned)a1) * sizeof(Z3_sort));
  Z3_constructor_list * _a4 = (Z3_constructor_list *) jenv->GetLongArrayElements(a4, NULL);
  Z3_mk_datatypes((Z3_context)a0, (unsigned)a1, _a2, _a3, _a4);
  jenv->ReleaseLongArrayElements(a2, (jlong *) _a2, JNI_ABORT);
  jenv->SetLongArrayRegion(a3, 0, (jsize)a1, (jlong *) _a3);
  free(_a3);
}
JNIEXPORT void JNICALL Java_Z3Native_queryConstructor(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jobject a3, jobject a4, jlongArray a5) {
  Z3_func_decl _a3;
  Z3_func_decl _a4;
  Z3_func_decl * _a5 = (Z3_func_decl *) malloc(((unsigned)a2) * sizeof(Z3_func_decl));
  Z3_query_constructor((Z3_context)a0, (Z3_constructor)a1, (unsigned)a2, &_a3, &_a4, _a5);
  {
     jclass mc    = jenv->GetObjectClass(a3);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a3, fid, (jlong) _a3);
  }
  {
     jclass mc    = jenv->GetObjectClass(a4);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a4, fid, (jlong) _a4);
  }
  jenv->SetLongArrayRegion(a5, 0, (jsize)a2, (jlong *) _a5);
  free(_a5);
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkFuncDecl(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jlongArray a3, jlong a4) {
  Z3_sort * _a3 = (Z3_sort *) jenv->GetLongArrayElements(a3, NULL);
  Z3_func_decl result = Z3_mk_func_decl((Z3_context)a0, (Z3_symbol)a1, (unsigned)a2, _a3, (Z3_sort)a4);
  jenv->ReleaseLongArrayElements(a3, (jlong *) _a3, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkApp(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jlongArray a3) {
  Z3_ast * _a3 = (Z3_ast *) jenv->GetLongArrayElements(a3, NULL);
  Z3_ast result = Z3_mk_app((Z3_context)a0, (Z3_func_decl)a1, (unsigned)a2, _a3);
  jenv->ReleaseLongArrayElements(a3, (jlong *) _a3, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkConst(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_const((Z3_context)a0, (Z3_symbol)a1, (Z3_sort)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkFreshFuncDecl(JNIEnv * jenv, jclass cls, jlong a0, jstring a1, jint a2, jlongArray a3, jlong a4) {
  Z3_string _a1 = (Z3_string) jenv->GetStringUTFChars(a1, NULL);
  Z3_sort * _a3 = (Z3_sort *) jenv->GetLongArrayElements(a3, NULL);
  Z3_func_decl result = Z3_mk_fresh_func_decl((Z3_context)a0, _a1, (unsigned)a2, _a3, (Z3_sort)a4);
  jenv->ReleaseLongArrayElements(a3, (jlong *) _a3, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkFreshConst(JNIEnv * jenv, jclass cls, jlong a0, jstring a1, jlong a2) {
  Z3_string _a1 = (Z3_string) jenv->GetStringUTFChars(a1, NULL);
  Z3_ast result = Z3_mk_fresh_const((Z3_context)a0, _a1, (Z3_sort)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkTrue(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_ast result = Z3_mk_true((Z3_context)a0);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkFalse(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_ast result = Z3_mk_false((Z3_context)a0);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkEq(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_eq((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkDistinct(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlongArray a2) {
  Z3_ast * _a2 = (Z3_ast *) jenv->GetLongArrayElements(a2, NULL);
  Z3_ast result = Z3_mk_distinct((Z3_context)a0, (unsigned)a1, _a2);
  jenv->ReleaseLongArrayElements(a2, (jlong *) _a2, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkNot(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_mk_not((Z3_context)a0, (Z3_ast)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkIte(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jlong a3) {
  Z3_ast result = Z3_mk_ite((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2, (Z3_ast)a3);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkIff(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_iff((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkImplies(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_implies((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkXor(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_xor((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkAnd(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlongArray a2) {
  Z3_ast * _a2 = (Z3_ast *) jenv->GetLongArrayElements(a2, NULL);
  Z3_ast result = Z3_mk_and((Z3_context)a0, (unsigned)a1, _a2);
  jenv->ReleaseLongArrayElements(a2, (jlong *) _a2, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkOr(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlongArray a2) {
  Z3_ast * _a2 = (Z3_ast *) jenv->GetLongArrayElements(a2, NULL);
  Z3_ast result = Z3_mk_or((Z3_context)a0, (unsigned)a1, _a2);
  jenv->ReleaseLongArrayElements(a2, (jlong *) _a2, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkAdd(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlongArray a2) {
  Z3_ast * _a2 = (Z3_ast *) jenv->GetLongArrayElements(a2, NULL);
  Z3_ast result = Z3_mk_add((Z3_context)a0, (unsigned)a1, _a2);
  jenv->ReleaseLongArrayElements(a2, (jlong *) _a2, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkMul(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlongArray a2) {
  Z3_ast * _a2 = (Z3_ast *) jenv->GetLongArrayElements(a2, NULL);
  Z3_ast result = Z3_mk_mul((Z3_context)a0, (unsigned)a1, _a2);
  jenv->ReleaseLongArrayElements(a2, (jlong *) _a2, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkSub(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlongArray a2) {
  Z3_ast * _a2 = (Z3_ast *) jenv->GetLongArrayElements(a2, NULL);
  Z3_ast result = Z3_mk_sub((Z3_context)a0, (unsigned)a1, _a2);
  jenv->ReleaseLongArrayElements(a2, (jlong *) _a2, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkUnaryMinus(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_mk_unary_minus((Z3_context)a0, (Z3_ast)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkDiv(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_div((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkMod(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_mod((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkRem(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_rem((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkPower(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_power((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkLt(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_lt((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkLe(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_le((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkGt(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_gt((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkGe(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_ge((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkInt2real(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_mk_int2real((Z3_context)a0, (Z3_ast)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkReal2int(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_mk_real2int((Z3_context)a0, (Z3_ast)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkIsInt(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_mk_is_int((Z3_context)a0, (Z3_ast)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvnot(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_mk_bvnot((Z3_context)a0, (Z3_ast)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvredand(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_mk_bvredand((Z3_context)a0, (Z3_ast)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvredor(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_mk_bvredor((Z3_context)a0, (Z3_ast)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvand(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvand((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvor(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvor((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvxor(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvxor((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvnand(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvnand((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvnor(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvnor((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvxnor(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvxnor((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvneg(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_mk_bvneg((Z3_context)a0, (Z3_ast)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvadd(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvadd((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvsub(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvsub((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvmul(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvmul((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvudiv(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvudiv((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvsdiv(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvsdiv((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvurem(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvurem((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvsrem(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvsrem((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvsmod(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvsmod((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvult(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvult((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvslt(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvslt((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvule(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvule((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvsle(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvsle((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvuge(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvuge((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvsge(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvsge((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvugt(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvugt((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvsgt(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvsgt((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkConcat(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_concat((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkExtract(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jint a2, jlong a3) {
  Z3_ast result = Z3_mk_extract((Z3_context)a0, (unsigned)a1, (unsigned)a2, (Z3_ast)a3);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkSignExt(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlong a2) {
  Z3_ast result = Z3_mk_sign_ext((Z3_context)a0, (unsigned)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkZeroExt(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlong a2) {
  Z3_ast result = Z3_mk_zero_ext((Z3_context)a0, (unsigned)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkRepeat(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlong a2) {
  Z3_ast result = Z3_mk_repeat((Z3_context)a0, (unsigned)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvshl(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvshl((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvlshr(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvlshr((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvashr(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvashr((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkRotateLeft(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlong a2) {
  Z3_ast result = Z3_mk_rotate_left((Z3_context)a0, (unsigned)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkRotateRight(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlong a2) {
  Z3_ast result = Z3_mk_rotate_right((Z3_context)a0, (unsigned)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkExtRotateLeft(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_ext_rotate_left((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkExtRotateRight(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_ext_rotate_right((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkInt2bv(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlong a2) {
  Z3_ast result = Z3_mk_int2bv((Z3_context)a0, (unsigned)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBv2int(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jboolean a2) {
  Z3_ast result = Z3_mk_bv2int((Z3_context)a0, (Z3_ast)a1, (Z3_bool)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvaddNoOverflow(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jboolean a3) {
  Z3_ast result = Z3_mk_bvadd_no_overflow((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2, (Z3_bool)a3);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvaddNoUnderflow(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvadd_no_underflow((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvsubNoOverflow(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvsub_no_overflow((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvsubNoUnderflow(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jboolean a3) {
  Z3_ast result = Z3_mk_bvsub_no_underflow((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2, (Z3_bool)a3);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvsdivNoOverflow(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvsdiv_no_overflow((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvnegNoOverflow(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_mk_bvneg_no_overflow((Z3_context)a0, (Z3_ast)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvmulNoOverflow(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jboolean a3) {
  Z3_ast result = Z3_mk_bvmul_no_overflow((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2, (Z3_bool)a3);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBvmulNoUnderflow(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_bvmul_no_underflow((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkSelect(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_select((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkStore(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jlong a3) {
  Z3_ast result = Z3_mk_store((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2, (Z3_ast)a3);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkConstArray(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_const_array((Z3_context)a0, (Z3_sort)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkMap(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jlongArray a3) {
  Z3_ast * _a3 = (Z3_ast *) jenv->GetLongArrayElements(a3, NULL);
  Z3_ast result = Z3_mk_map((Z3_context)a0, (Z3_func_decl)a1, (unsigned)a2, _a3);
  jenv->ReleaseLongArrayElements(a3, (jlong *) _a3, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkArrayDefault(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_mk_array_default((Z3_context)a0, (Z3_ast)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkSetSort(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_sort result = Z3_mk_set_sort((Z3_context)a0, (Z3_sort)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkEmptySet(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_mk_empty_set((Z3_context)a0, (Z3_sort)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkFullSet(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_mk_full_set((Z3_context)a0, (Z3_sort)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkSetAdd(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_set_add((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkSetDel(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_set_del((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkSetUnion(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlongArray a2) {
  Z3_ast * _a2 = (Z3_ast *) jenv->GetLongArrayElements(a2, NULL);
  Z3_ast result = Z3_mk_set_union((Z3_context)a0, (unsigned)a1, _a2);
  jenv->ReleaseLongArrayElements(a2, (jlong *) _a2, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkSetIntersect(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlongArray a2) {
  Z3_ast * _a2 = (Z3_ast *) jenv->GetLongArrayElements(a2, NULL);
  Z3_ast result = Z3_mk_set_intersect((Z3_context)a0, (unsigned)a1, _a2);
  jenv->ReleaseLongArrayElements(a2, (jlong *) _a2, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkSetDifference(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_set_difference((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkSetComplement(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_mk_set_complement((Z3_context)a0, (Z3_ast)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkSetMember(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_set_member((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkSetSubset(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_set_subset((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkNumeral(JNIEnv * jenv, jclass cls, jlong a0, jstring a1, jlong a2) {
  Z3_string _a1 = (Z3_string) jenv->GetStringUTFChars(a1, NULL);
  Z3_ast result = Z3_mk_numeral((Z3_context)a0, _a1, (Z3_sort)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkReal(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jint a2) {
  Z3_ast result = Z3_mk_real((Z3_context)a0, (int)a1, (int)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkInt(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlong a2) {
  Z3_ast result = Z3_mk_int((Z3_context)a0, (int)a1, (Z3_sort)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkUnsignedInt(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlong a2) {
  Z3_ast result = Z3_mk_unsigned_int((Z3_context)a0, (unsigned)a1, (Z3_sort)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkInt64(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_int64((Z3_context)a0, (__int64)a1, (Z3_sort)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkUnsignedInt64(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_mk_unsigned_int64((Z3_context)a0, (__uint64)a1, (Z3_sort)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkPattern(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlongArray a2) {
  Z3_ast * _a2 = (Z3_ast *) jenv->GetLongArrayElements(a2, NULL);
  Z3_pattern result = Z3_mk_pattern((Z3_context)a0, (unsigned)a1, _a2);
  jenv->ReleaseLongArrayElements(a2, (jlong *) _a2, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkBound(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlong a2) {
  Z3_ast result = Z3_mk_bound((Z3_context)a0, (unsigned)a1, (Z3_sort)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkForall(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jint a2, jlongArray a3, jint a4, jlongArray a5, jlongArray a6, jlong a7) {
  Z3_pattern * _a3 = (Z3_pattern *) jenv->GetLongArrayElements(a3, NULL);
  Z3_sort * _a5 = (Z3_sort *) jenv->GetLongArrayElements(a5, NULL);
  Z3_symbol * _a6 = (Z3_symbol *) jenv->GetLongArrayElements(a6, NULL);
  Z3_ast result = Z3_mk_forall((Z3_context)a0, (unsigned)a1, (unsigned)a2, _a3, (unsigned)a4, _a5, _a6, (Z3_ast)a7);
  jenv->ReleaseLongArrayElements(a3, (jlong *) _a3, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a5, (jlong *) _a5, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a6, (jlong *) _a6, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkExists(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jint a2, jlongArray a3, jint a4, jlongArray a5, jlongArray a6, jlong a7) {
  Z3_pattern * _a3 = (Z3_pattern *) jenv->GetLongArrayElements(a3, NULL);
  Z3_sort * _a5 = (Z3_sort *) jenv->GetLongArrayElements(a5, NULL);
  Z3_symbol * _a6 = (Z3_symbol *) jenv->GetLongArrayElements(a6, NULL);
  Z3_ast result = Z3_mk_exists((Z3_context)a0, (unsigned)a1, (unsigned)a2, _a3, (unsigned)a4, _a5, _a6, (Z3_ast)a7);
  jenv->ReleaseLongArrayElements(a3, (jlong *) _a3, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a5, (jlong *) _a5, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a6, (jlong *) _a6, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkQuantifier(JNIEnv * jenv, jclass cls, jlong a0, jboolean a1, jint a2, jint a3, jlongArray a4, jint a5, jlongArray a6, jlongArray a7, jlong a8) {
  Z3_pattern * _a4 = (Z3_pattern *) jenv->GetLongArrayElements(a4, NULL);
  Z3_sort * _a6 = (Z3_sort *) jenv->GetLongArrayElements(a6, NULL);
  Z3_symbol * _a7 = (Z3_symbol *) jenv->GetLongArrayElements(a7, NULL);
  Z3_ast result = Z3_mk_quantifier((Z3_context)a0, (Z3_bool)a1, (unsigned)a2, (unsigned)a3, _a4, (unsigned)a5, _a6, _a7, (Z3_ast)a8);
  jenv->ReleaseLongArrayElements(a4, (jlong *) _a4, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a6, (jlong *) _a6, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a7, (jlong *) _a7, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkQuantifierEx(JNIEnv * jenv, jclass cls, jlong a0, jboolean a1, jint a2, jlong a3, jlong a4, jint a5, jlongArray a6, jint a7, jlongArray a8, jint a9, jlongArray a10, jlongArray a11, jlong a12) {
  Z3_pattern * _a6 = (Z3_pattern *) jenv->GetLongArrayElements(a6, NULL);
  Z3_ast * _a8 = (Z3_ast *) jenv->GetLongArrayElements(a8, NULL);
  Z3_sort * _a10 = (Z3_sort *) jenv->GetLongArrayElements(a10, NULL);
  Z3_symbol * _a11 = (Z3_symbol *) jenv->GetLongArrayElements(a11, NULL);
  Z3_ast result = Z3_mk_quantifier_ex((Z3_context)a0, (Z3_bool)a1, (unsigned)a2, (Z3_symbol)a3, (Z3_symbol)a4, (unsigned)a5, _a6, (unsigned)a7, _a8, (unsigned)a9, _a10, _a11, (Z3_ast)a12);
  jenv->ReleaseLongArrayElements(a6, (jlong *) _a6, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a8, (jlong *) _a8, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a10, (jlong *) _a10, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a11, (jlong *) _a11, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkForallConst(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jint a2, jlongArray a3, jint a4, jlongArray a5, jlong a6) {
  Z3_app * _a3 = (Z3_app *) jenv->GetLongArrayElements(a3, NULL);
  Z3_pattern * _a5 = (Z3_pattern *) jenv->GetLongArrayElements(a5, NULL);
  Z3_ast result = Z3_mk_forall_const((Z3_context)a0, (unsigned)a1, (unsigned)a2, _a3, (unsigned)a4, _a5, (Z3_ast)a6);
  jenv->ReleaseLongArrayElements(a3, (jlong *) _a3, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a5, (jlong *) _a5, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkExistsConst(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jint a2, jlongArray a3, jint a4, jlongArray a5, jlong a6) {
  Z3_app * _a3 = (Z3_app *) jenv->GetLongArrayElements(a3, NULL);
  Z3_pattern * _a5 = (Z3_pattern *) jenv->GetLongArrayElements(a5, NULL);
  Z3_ast result = Z3_mk_exists_const((Z3_context)a0, (unsigned)a1, (unsigned)a2, _a3, (unsigned)a4, _a5, (Z3_ast)a6);
  jenv->ReleaseLongArrayElements(a3, (jlong *) _a3, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a5, (jlong *) _a5, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkQuantifierConst(JNIEnv * jenv, jclass cls, jlong a0, jboolean a1, jint a2, jint a3, jlongArray a4, jint a5, jlongArray a6, jlong a7) {
  Z3_app * _a4 = (Z3_app *) jenv->GetLongArrayElements(a4, NULL);
  Z3_pattern * _a6 = (Z3_pattern *) jenv->GetLongArrayElements(a6, NULL);
  Z3_ast result = Z3_mk_quantifier_const((Z3_context)a0, (Z3_bool)a1, (unsigned)a2, (unsigned)a3, _a4, (unsigned)a5, _a6, (Z3_ast)a7);
  jenv->ReleaseLongArrayElements(a4, (jlong *) _a4, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a6, (jlong *) _a6, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkQuantifierConstEx(JNIEnv * jenv, jclass cls, jlong a0, jboolean a1, jint a2, jlong a3, jlong a4, jint a5, jlongArray a6, jint a7, jlongArray a8, jint a9, jlongArray a10, jlong a11) {
  Z3_app * _a6 = (Z3_app *) jenv->GetLongArrayElements(a6, NULL);
  Z3_pattern * _a8 = (Z3_pattern *) jenv->GetLongArrayElements(a8, NULL);
  Z3_ast * _a10 = (Z3_ast *) jenv->GetLongArrayElements(a10, NULL);
  Z3_ast result = Z3_mk_quantifier_const_ex((Z3_context)a0, (Z3_bool)a1, (unsigned)a2, (Z3_symbol)a3, (Z3_symbol)a4, (unsigned)a5, _a6, (unsigned)a7, _a8, (unsigned)a9, _a10, (Z3_ast)a11);
  jenv->ReleaseLongArrayElements(a6, (jlong *) _a6, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a8, (jlong *) _a8, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a10, (jlong *) _a10, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getSymbolKind(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_symbol_kind((Z3_context)a0, (Z3_symbol)a1);
  return (jint) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getSymbolInt(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  int result = Z3_get_symbol_int((Z3_context)a0, (Z3_symbol)a1);
  return (jint) result;
}
JNIEXPORT jstring JNICALL Java_Z3Native_getSymbolString(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_string result = Z3_get_symbol_string((Z3_context)a0, (Z3_symbol)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jlong JNICALL Java_Z3Native_getSortName(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_symbol result = Z3_get_sort_name((Z3_context)a0, (Z3_sort)a1);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getSortId(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_sort_id((Z3_context)a0, (Z3_sort)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_sortToAst(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_sort_to_ast((Z3_context)a0, (Z3_sort)a1);
  return (jlong) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_isEqSort(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_bool result = Z3_is_eq_sort((Z3_context)a0, (Z3_sort)a1, (Z3_sort)a2);
  return (jboolean) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getSortKind(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_sort_kind((Z3_context)a0, (Z3_sort)a1);
  return (jint) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getBvSortSize(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_bv_sort_size((Z3_context)a0, (Z3_sort)a1);
  return (jint) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_getFiniteDomainSortSize(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jobject a2) {
  __uint64 _a2;
  Z3_bool result = Z3_get_finite_domain_sort_size((Z3_context)a0, (Z3_sort)a1, &_a2);
  {
     jclass mc    = jenv->GetObjectClass(a2);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a2, fid, (jlong) _a2);
  }
  return (jboolean) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getArraySortDomain(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_sort result = Z3_get_array_sort_domain((Z3_context)a0, (Z3_sort)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getArraySortRange(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_sort result = Z3_get_array_sort_range((Z3_context)a0, (Z3_sort)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getTupleSortMkDecl(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_func_decl result = Z3_get_tuple_sort_mk_decl((Z3_context)a0, (Z3_sort)a1);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getTupleSortNumFields(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_tuple_sort_num_fields((Z3_context)a0, (Z3_sort)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getTupleSortFieldDecl(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_func_decl result = Z3_get_tuple_sort_field_decl((Z3_context)a0, (Z3_sort)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getDatatypeSortNumConstructors(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_datatype_sort_num_constructors((Z3_context)a0, (Z3_sort)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getDatatypeSortConstructor(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_func_decl result = Z3_get_datatype_sort_constructor((Z3_context)a0, (Z3_sort)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getDatatypeSortRecognizer(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_func_decl result = Z3_get_datatype_sort_recognizer((Z3_context)a0, (Z3_sort)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getDatatypeSortConstructorAccessor(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jint a3) {
  Z3_func_decl result = Z3_get_datatype_sort_constructor_accessor((Z3_context)a0, (Z3_sort)a1, (unsigned)a2, (unsigned)a3);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getRelationArity(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_relation_arity((Z3_context)a0, (Z3_sort)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getRelationColumn(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_sort result = Z3_get_relation_column((Z3_context)a0, (Z3_sort)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_funcDeclToAst(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_func_decl_to_ast((Z3_context)a0, (Z3_func_decl)a1);
  return (jlong) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_isEqFuncDecl(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_bool result = Z3_is_eq_func_decl((Z3_context)a0, (Z3_func_decl)a1, (Z3_func_decl)a2);
  return (jboolean) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getFuncDeclId(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_func_decl_id((Z3_context)a0, (Z3_func_decl)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getDeclName(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_symbol result = Z3_get_decl_name((Z3_context)a0, (Z3_func_decl)a1);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getDeclKind(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_decl_kind((Z3_context)a0, (Z3_func_decl)a1);
  return (jint) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getDomainSize(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_domain_size((Z3_context)a0, (Z3_func_decl)a1);
  return (jint) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getArity(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_arity((Z3_context)a0, (Z3_func_decl)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getDomain(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_sort result = Z3_get_domain((Z3_context)a0, (Z3_func_decl)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getRange(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_sort result = Z3_get_range((Z3_context)a0, (Z3_func_decl)a1);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getDeclNumParameters(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_decl_num_parameters((Z3_context)a0, (Z3_func_decl)a1);
  return (jint) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getDeclParameterKind(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  unsigned result = Z3_get_decl_parameter_kind((Z3_context)a0, (Z3_func_decl)a1, (unsigned)a2);
  return (jint) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getDeclIntParameter(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  int result = Z3_get_decl_int_parameter((Z3_context)a0, (Z3_func_decl)a1, (unsigned)a2);
  return (jint) result;
}
JNIEXPORT jdouble JNICALL Java_Z3Native_getDeclDoubleParameter(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  double result = Z3_get_decl_double_parameter((Z3_context)a0, (Z3_func_decl)a1, (unsigned)a2);
  return (jdouble) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getDeclSymbolParameter(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_symbol result = Z3_get_decl_symbol_parameter((Z3_context)a0, (Z3_func_decl)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getDeclSortParameter(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_sort result = Z3_get_decl_sort_parameter((Z3_context)a0, (Z3_func_decl)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getDeclAstParameter(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_ast result = Z3_get_decl_ast_parameter((Z3_context)a0, (Z3_func_decl)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getDeclFuncDeclParameter(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_func_decl result = Z3_get_decl_func_decl_parameter((Z3_context)a0, (Z3_func_decl)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jstring JNICALL Java_Z3Native_getDeclRationalParameter(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_string result = Z3_get_decl_rational_parameter((Z3_context)a0, (Z3_func_decl)a1, (unsigned)a2);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jlong JNICALL Java_Z3Native_appToAst(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_app_to_ast((Z3_context)a0, (Z3_app)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getAppDecl(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_func_decl result = Z3_get_app_decl((Z3_context)a0, (Z3_app)a1);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getAppNumArgs(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_app_num_args((Z3_context)a0, (Z3_app)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getAppArg(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_ast result = Z3_get_app_arg((Z3_context)a0, (Z3_app)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_isEqAst(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_bool result = Z3_is_eq_ast((Z3_context)a0, (Z3_ast)a1, (Z3_ast)a2);
  return (jboolean) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getAstId(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_ast_id((Z3_context)a0, (Z3_ast)a1);
  return (jint) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getAstHash(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_ast_hash((Z3_context)a0, (Z3_ast)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getSort(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_sort result = Z3_get_sort((Z3_context)a0, (Z3_ast)a1);
  return (jlong) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_isWellSorted(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_bool result = Z3_is_well_sorted((Z3_context)a0, (Z3_ast)a1);
  return (jboolean) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getBoolValue(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_bool_value((Z3_context)a0, (Z3_ast)a1);
  return (jint) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getAstKind(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_ast_kind((Z3_context)a0, (Z3_ast)a1);
  return (jint) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_isApp(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_bool result = Z3_is_app((Z3_context)a0, (Z3_ast)a1);
  return (jboolean) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_isNumeralAst(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_bool result = Z3_is_numeral_ast((Z3_context)a0, (Z3_ast)a1);
  return (jboolean) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_isAlgebraicNumber(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_bool result = Z3_is_algebraic_number((Z3_context)a0, (Z3_ast)a1);
  return (jboolean) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_toApp(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_app result = Z3_to_app((Z3_context)a0, (Z3_ast)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_toFuncDecl(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_func_decl result = Z3_to_func_decl((Z3_context)a0, (Z3_ast)a1);
  return (jlong) result;
}
JNIEXPORT jstring JNICALL Java_Z3Native_getNumeralString(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_string result = Z3_get_numeral_string((Z3_context)a0, (Z3_ast)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jstring JNICALL Java_Z3Native_getNumeralDecimalString(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_string result = Z3_get_numeral_decimal_string((Z3_context)a0, (Z3_ast)a1, (unsigned)a2);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jlong JNICALL Java_Z3Native_getNumerator(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_get_numerator((Z3_context)a0, (Z3_ast)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getDenominator(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_get_denominator((Z3_context)a0, (Z3_ast)a1);
  return (jlong) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_getNumeralSmall(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jobject a2, jobject a3) {
  __int64 _a2;
  __int64 _a3;
  Z3_bool result = Z3_get_numeral_small((Z3_context)a0, (Z3_ast)a1, &_a2, &_a3);
  {
     jclass mc    = jenv->GetObjectClass(a2);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a2, fid, (jlong) _a2);
  }
  {
     jclass mc    = jenv->GetObjectClass(a3);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a3, fid, (jlong) _a3);
  }
  return (jboolean) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_getNumeralInt(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jobject a2) {
  int _a2;
  Z3_bool result = Z3_get_numeral_int((Z3_context)a0, (Z3_ast)a1, &_a2);
  {
     jclass mc    = jenv->GetObjectClass(a2);
     jfieldID fid = jenv->GetFieldID(mc, "value", "I");
     jenv->SetIntField(a2, fid, (jint) _a2);
  }
  return (jboolean) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_getNumeralUint(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jobject a2) {
  unsigned _a2;
  Z3_bool result = Z3_get_numeral_uint((Z3_context)a0, (Z3_ast)a1, &_a2);
  {
     jclass mc    = jenv->GetObjectClass(a2);
     jfieldID fid = jenv->GetFieldID(mc, "value", "I");
     jenv->SetIntField(a2, fid, (jint) _a2);
  }
  return (jboolean) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_getNumeralUint64(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jobject a2) {
  __uint64 _a2;
  Z3_bool result = Z3_get_numeral_uint64((Z3_context)a0, (Z3_ast)a1, &_a2);
  {
     jclass mc    = jenv->GetObjectClass(a2);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a2, fid, (jlong) _a2);
  }
  return (jboolean) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_getNumeralInt64(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jobject a2) {
  __int64 _a2;
  Z3_bool result = Z3_get_numeral_int64((Z3_context)a0, (Z3_ast)a1, &_a2);
  {
     jclass mc    = jenv->GetObjectClass(a2);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a2, fid, (jlong) _a2);
  }
  return (jboolean) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_getNumeralRationalInt64(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jobject a2, jobject a3) {
  __int64 _a2;
  __int64 _a3;
  Z3_bool result = Z3_get_numeral_rational_int64((Z3_context)a0, (Z3_ast)a1, &_a2, &_a3);
  {
     jclass mc    = jenv->GetObjectClass(a2);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a2, fid, (jlong) _a2);
  }
  {
     jclass mc    = jenv->GetObjectClass(a3);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a3, fid, (jlong) _a3);
  }
  return (jboolean) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getAlgebraicNumberLower(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_ast result = Z3_get_algebraic_number_lower((Z3_context)a0, (Z3_ast)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getAlgebraicNumberUpper(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_ast result = Z3_get_algebraic_number_upper((Z3_context)a0, (Z3_ast)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_patternToAst(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_pattern_to_ast((Z3_context)a0, (Z3_pattern)a1);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getPatternNumTerms(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_pattern_num_terms((Z3_context)a0, (Z3_pattern)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getPattern(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_ast result = Z3_get_pattern((Z3_context)a0, (Z3_pattern)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getIndexValue(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_index_value((Z3_context)a0, (Z3_ast)a1);
  return (jint) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_isQuantifierForall(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_bool result = Z3_is_quantifier_forall((Z3_context)a0, (Z3_ast)a1);
  return (jboolean) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getQuantifierWeight(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_quantifier_weight((Z3_context)a0, (Z3_ast)a1);
  return (jint) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getQuantifierNumPatterns(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_quantifier_num_patterns((Z3_context)a0, (Z3_ast)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getQuantifierPatternAst(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_pattern result = Z3_get_quantifier_pattern_ast((Z3_context)a0, (Z3_ast)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getQuantifierNumNoPatterns(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_quantifier_num_no_patterns((Z3_context)a0, (Z3_ast)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getQuantifierNoPatternAst(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_ast result = Z3_get_quantifier_no_pattern_ast((Z3_context)a0, (Z3_ast)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getQuantifierNumBound(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_quantifier_num_bound((Z3_context)a0, (Z3_ast)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getQuantifierBoundName(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_symbol result = Z3_get_quantifier_bound_name((Z3_context)a0, (Z3_ast)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getQuantifierBoundSort(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_sort result = Z3_get_quantifier_bound_sort((Z3_context)a0, (Z3_ast)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getQuantifierBody(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_get_quantifier_body((Z3_context)a0, (Z3_ast)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_simplify(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_simplify((Z3_context)a0, (Z3_ast)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_simplifyEx(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_simplify_ex((Z3_context)a0, (Z3_ast)a1, (Z3_params)a2);
  return (jlong) result;
}
JNIEXPORT jstring JNICALL Java_Z3Native_simplifyGetHelp(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_string result = Z3_simplify_get_help((Z3_context)a0);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jlong JNICALL Java_Z3Native_simplifyGetParamDescrs(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_param_descrs result = Z3_simplify_get_param_descrs((Z3_context)a0);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_updateTerm(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jlongArray a3) {
  Z3_ast * _a3 = (Z3_ast *) jenv->GetLongArrayElements(a3, NULL);
  Z3_ast result = Z3_update_term((Z3_context)a0, (Z3_ast)a1, (unsigned)a2, _a3);
  jenv->ReleaseLongArrayElements(a3, (jlong *) _a3, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_substitute(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jlongArray a3, jlongArray a4) {
  Z3_ast * _a3 = (Z3_ast *) jenv->GetLongArrayElements(a3, NULL);
  Z3_ast * _a4 = (Z3_ast *) jenv->GetLongArrayElements(a4, NULL);
  Z3_ast result = Z3_substitute((Z3_context)a0, (Z3_ast)a1, (unsigned)a2, _a3, _a4);
  jenv->ReleaseLongArrayElements(a3, (jlong *) _a3, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a4, (jlong *) _a4, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_substituteVars(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jlongArray a3) {
  Z3_ast * _a3 = (Z3_ast *) jenv->GetLongArrayElements(a3, NULL);
  Z3_ast result = Z3_substitute_vars((Z3_context)a0, (Z3_ast)a1, (unsigned)a2, _a3);
  jenv->ReleaseLongArrayElements(a3, (jlong *) _a3, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_translate(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_translate((Z3_context)a0, (Z3_ast)a1, (Z3_context)a2);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_modelIncRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_model_inc_ref((Z3_context)a0, (Z3_model)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_modelDecRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_model_dec_ref((Z3_context)a0, (Z3_model)a1);
}
JNIEXPORT jboolean JNICALL Java_Z3Native_modelEval(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jboolean a3, jobject a4) {
  Z3_ast _a4;
  Z3_bool result = Z3_model_eval((Z3_context)a0, (Z3_model)a1, (Z3_ast)a2, (Z3_bool)a3, &_a4);
  {
     jclass mc    = jenv->GetObjectClass(a4);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a4, fid, (jlong) _a4);
  }
  return (jboolean) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_modelGetConstInterp(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_model_get_const_interp((Z3_context)a0, (Z3_model)a1, (Z3_func_decl)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_modelGetFuncInterp(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_func_interp result = Z3_model_get_func_interp((Z3_context)a0, (Z3_model)a1, (Z3_func_decl)a2);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_modelGetNumConsts(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_model_get_num_consts((Z3_context)a0, (Z3_model)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_modelGetConstDecl(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_func_decl result = Z3_model_get_const_decl((Z3_context)a0, (Z3_model)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_modelGetNumFuncs(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_model_get_num_funcs((Z3_context)a0, (Z3_model)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_modelGetFuncDecl(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_func_decl result = Z3_model_get_func_decl((Z3_context)a0, (Z3_model)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_modelGetNumSorts(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_model_get_num_sorts((Z3_context)a0, (Z3_model)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_modelGetSort(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_sort result = Z3_model_get_sort((Z3_context)a0, (Z3_model)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_modelGetSortUniverse(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast_vector result = Z3_model_get_sort_universe((Z3_context)a0, (Z3_model)a1, (Z3_sort)a2);
  return (jlong) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_isAsArray(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_bool result = Z3_is_as_array((Z3_context)a0, (Z3_ast)a1);
  return (jboolean) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getAsArrayFuncDecl(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_func_decl result = Z3_get_as_array_func_decl((Z3_context)a0, (Z3_ast)a1);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_funcInterpIncRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_func_interp_inc_ref((Z3_context)a0, (Z3_func_interp)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_funcInterpDecRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_func_interp_dec_ref((Z3_context)a0, (Z3_func_interp)a1);
}
JNIEXPORT jint JNICALL Java_Z3Native_funcInterpGetNumEntries(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_func_interp_get_num_entries((Z3_context)a0, (Z3_func_interp)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_funcInterpGetEntry(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_func_entry result = Z3_func_interp_get_entry((Z3_context)a0, (Z3_func_interp)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_funcInterpGetElse(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_func_interp_get_else((Z3_context)a0, (Z3_func_interp)a1);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_funcInterpGetArity(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_func_interp_get_arity((Z3_context)a0, (Z3_func_interp)a1);
  return (jint) result;
}
JNIEXPORT void JNICALL Java_Z3Native_funcEntryIncRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_func_entry_inc_ref((Z3_context)a0, (Z3_func_entry)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_funcEntryDecRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_func_entry_dec_ref((Z3_context)a0, (Z3_func_entry)a1);
}
JNIEXPORT jlong JNICALL Java_Z3Native_funcEntryGetValue(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_func_entry_get_value((Z3_context)a0, (Z3_func_entry)a1);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_funcEntryGetNumArgs(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_func_entry_get_num_args((Z3_context)a0, (Z3_func_entry)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_funcEntryGetArg(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_ast result = Z3_func_entry_get_arg((Z3_context)a0, (Z3_func_entry)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_openLog(JNIEnv * jenv, jclass cls, jstring a0) {
  Z3_string _a0 = (Z3_string) jenv->GetStringUTFChars(a0, NULL);
  int result = Z3_open_log(_a0);
  return (jint) result;
}
JNIEXPORT void JNICALL Java_Z3Native_appendLog(JNIEnv * jenv, jclass cls, jstring a0) {
  Z3_string _a0 = (Z3_string) jenv->GetStringUTFChars(a0, NULL);
  Z3_append_log(_a0);
}
JNIEXPORT void JNICALL Java_Z3Native_closeLog(JNIEnv * jenv, jclass cls) {
  Z3_close_log();
}
JNIEXPORT void JNICALL Java_Z3Native_toggleWarningMessages(JNIEnv * jenv, jclass cls, jboolean a0) {
  Z3_toggle_warning_messages((Z3_bool)a0);
}
JNIEXPORT void JNICALL Java_Z3Native_setAstPrintMode(JNIEnv * jenv, jclass cls, jlong a0, jint a1) {
  Z3_set_ast_print_mode((Z3_context)a0, (Z3_ast_print_mode)a1);
}
JNIEXPORT jstring JNICALL Java_Z3Native_astToString(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_string result = Z3_ast_to_string((Z3_context)a0, (Z3_ast)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jstring JNICALL Java_Z3Native_patternToString(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_string result = Z3_pattern_to_string((Z3_context)a0, (Z3_pattern)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jstring JNICALL Java_Z3Native_sortToString(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_string result = Z3_sort_to_string((Z3_context)a0, (Z3_sort)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jstring JNICALL Java_Z3Native_funcDeclToString(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_string result = Z3_func_decl_to_string((Z3_context)a0, (Z3_func_decl)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jstring JNICALL Java_Z3Native_modelToString(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_string result = Z3_model_to_string((Z3_context)a0, (Z3_model)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jstring JNICALL Java_Z3Native_benchmarkToSmtlibString(JNIEnv * jenv, jclass cls, jlong a0, jstring a1, jstring a2, jstring a3, jstring a4, jint a5, jlongArray a6, jlong a7) {
  Z3_string _a1 = (Z3_string) jenv->GetStringUTFChars(a1, NULL);
  Z3_string _a2 = (Z3_string) jenv->GetStringUTFChars(a2, NULL);
  Z3_string _a3 = (Z3_string) jenv->GetStringUTFChars(a3, NULL);
  Z3_string _a4 = (Z3_string) jenv->GetStringUTFChars(a4, NULL);
  Z3_ast * _a6 = (Z3_ast *) jenv->GetLongArrayElements(a6, NULL);
  Z3_string result = Z3_benchmark_to_smtlib_string((Z3_context)a0, _a1, _a2, _a3, _a4, (unsigned)a5, _a6, (Z3_ast)a7);
  jenv->ReleaseLongArrayElements(a6, (jlong *) _a6, JNI_ABORT);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jlong JNICALL Java_Z3Native_parseSmtlib2String(JNIEnv * jenv, jclass cls, jlong a0, jstring a1, jint a2, jlongArray a3, jlongArray a4, jint a5, jlongArray a6, jlongArray a7) {
  Z3_string _a1 = (Z3_string) jenv->GetStringUTFChars(a1, NULL);
  Z3_symbol * _a3 = (Z3_symbol *) jenv->GetLongArrayElements(a3, NULL);
  Z3_sort * _a4 = (Z3_sort *) jenv->GetLongArrayElements(a4, NULL);
  Z3_symbol * _a6 = (Z3_symbol *) jenv->GetLongArrayElements(a6, NULL);
  Z3_func_decl * _a7 = (Z3_func_decl *) jenv->GetLongArrayElements(a7, NULL);
  Z3_ast result = Z3_parse_smtlib2_string((Z3_context)a0, _a1, (unsigned)a2, _a3, _a4, (unsigned)a5, _a6, _a7);
  jenv->ReleaseLongArrayElements(a3, (jlong *) _a3, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a4, (jlong *) _a4, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a6, (jlong *) _a6, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a7, (jlong *) _a7, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_parseSmtlib2File(JNIEnv * jenv, jclass cls, jlong a0, jstring a1, jint a2, jlongArray a3, jlongArray a4, jint a5, jlongArray a6, jlongArray a7) {
  Z3_string _a1 = (Z3_string) jenv->GetStringUTFChars(a1, NULL);
  Z3_symbol * _a3 = (Z3_symbol *) jenv->GetLongArrayElements(a3, NULL);
  Z3_sort * _a4 = (Z3_sort *) jenv->GetLongArrayElements(a4, NULL);
  Z3_symbol * _a6 = (Z3_symbol *) jenv->GetLongArrayElements(a6, NULL);
  Z3_func_decl * _a7 = (Z3_func_decl *) jenv->GetLongArrayElements(a7, NULL);
  Z3_ast result = Z3_parse_smtlib2_file((Z3_context)a0, _a1, (unsigned)a2, _a3, _a4, (unsigned)a5, _a6, _a7);
  jenv->ReleaseLongArrayElements(a3, (jlong *) _a3, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a4, (jlong *) _a4, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a6, (jlong *) _a6, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a7, (jlong *) _a7, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_parseSmtlibString(JNIEnv * jenv, jclass cls, jlong a0, jstring a1, jint a2, jlongArray a3, jlongArray a4, jint a5, jlongArray a6, jlongArray a7) {
  Z3_string _a1 = (Z3_string) jenv->GetStringUTFChars(a1, NULL);
  Z3_symbol * _a3 = (Z3_symbol *) jenv->GetLongArrayElements(a3, NULL);
  Z3_sort * _a4 = (Z3_sort *) jenv->GetLongArrayElements(a4, NULL);
  Z3_symbol * _a6 = (Z3_symbol *) jenv->GetLongArrayElements(a6, NULL);
  Z3_func_decl * _a7 = (Z3_func_decl *) jenv->GetLongArrayElements(a7, NULL);
  Z3_parse_smtlib_string((Z3_context)a0, _a1, (unsigned)a2, _a3, _a4, (unsigned)a5, _a6, _a7);
  jenv->ReleaseLongArrayElements(a3, (jlong *) _a3, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a4, (jlong *) _a4, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a6, (jlong *) _a6, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a7, (jlong *) _a7, JNI_ABORT);
}
JNIEXPORT void JNICALL Java_Z3Native_parseSmtlibFile(JNIEnv * jenv, jclass cls, jlong a0, jstring a1, jint a2, jlongArray a3, jlongArray a4, jint a5, jlongArray a6, jlongArray a7) {
  Z3_string _a1 = (Z3_string) jenv->GetStringUTFChars(a1, NULL);
  Z3_symbol * _a3 = (Z3_symbol *) jenv->GetLongArrayElements(a3, NULL);
  Z3_sort * _a4 = (Z3_sort *) jenv->GetLongArrayElements(a4, NULL);
  Z3_symbol * _a6 = (Z3_symbol *) jenv->GetLongArrayElements(a6, NULL);
  Z3_func_decl * _a7 = (Z3_func_decl *) jenv->GetLongArrayElements(a7, NULL);
  Z3_parse_smtlib_file((Z3_context)a0, _a1, (unsigned)a2, _a3, _a4, (unsigned)a5, _a6, _a7);
  jenv->ReleaseLongArrayElements(a3, (jlong *) _a3, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a4, (jlong *) _a4, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a6, (jlong *) _a6, JNI_ABORT);
  jenv->ReleaseLongArrayElements(a7, (jlong *) _a7, JNI_ABORT);
}
JNIEXPORT jint JNICALL Java_Z3Native_getSmtlibNumFormulas(JNIEnv * jenv, jclass cls, jlong a0) {
  unsigned result = Z3_get_smtlib_num_formulas((Z3_context)a0);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getSmtlibFormula(JNIEnv * jenv, jclass cls, jlong a0, jint a1) {
  Z3_ast result = Z3_get_smtlib_formula((Z3_context)a0, (unsigned)a1);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getSmtlibNumAssumptions(JNIEnv * jenv, jclass cls, jlong a0) {
  unsigned result = Z3_get_smtlib_num_assumptions((Z3_context)a0);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getSmtlibAssumption(JNIEnv * jenv, jclass cls, jlong a0, jint a1) {
  Z3_ast result = Z3_get_smtlib_assumption((Z3_context)a0, (unsigned)a1);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getSmtlibNumDecls(JNIEnv * jenv, jclass cls, jlong a0) {
  unsigned result = Z3_get_smtlib_num_decls((Z3_context)a0);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getSmtlibDecl(JNIEnv * jenv, jclass cls, jlong a0, jint a1) {
  Z3_func_decl result = Z3_get_smtlib_decl((Z3_context)a0, (unsigned)a1);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getSmtlibNumSorts(JNIEnv * jenv, jclass cls, jlong a0) {
  unsigned result = Z3_get_smtlib_num_sorts((Z3_context)a0);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getSmtlibSort(JNIEnv * jenv, jclass cls, jlong a0, jint a1) {
  Z3_sort result = Z3_get_smtlib_sort((Z3_context)a0, (unsigned)a1);
  return (jlong) result;
}
JNIEXPORT jstring JNICALL Java_Z3Native_getSmtlibError(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_string result = Z3_get_smtlib_error((Z3_context)a0);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jint JNICALL Java_Z3Native_getErrorCode(JNIEnv * jenv, jclass cls, jlong a0) {
  unsigned result = Z3_get_error_code((Z3_context)a0);
  return (jint) result;
}
JNIEXPORT void JNICALL Java_Z3Native_setError(JNIEnv * jenv, jclass cls, jlong a0, jint a1) {
  Z3_set_error((Z3_context)a0, (Z3_error_code)a1);
}
JNIEXPORT jstring JNICALL Java_Z3Native_getErrorMsg(JNIEnv * jenv, jclass cls, jint a0) {
  Z3_string result = Z3_get_error_msg((Z3_error_code)a0);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jstring JNICALL Java_Z3Native_getErrorMsgEx(JNIEnv * jenv, jclass cls, jlong a0, jint a1) {
  Z3_string result = Z3_get_error_msg_ex((Z3_context)a0, (Z3_error_code)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT void JNICALL Java_Z3Native_getVersion(JNIEnv * jenv, jclass cls, jobject a0, jobject a1, jobject a2, jobject a3) {
  unsigned _a0;
  unsigned _a1;
  unsigned _a2;
  unsigned _a3;
  Z3_get_version(&_a0, &_a1, &_a2, &_a3);
  {
     jclass mc    = jenv->GetObjectClass(a0);
     jfieldID fid = jenv->GetFieldID(mc, "value", "I");
     jenv->SetIntField(a0, fid, (jint) _a0);
  }
  {
     jclass mc    = jenv->GetObjectClass(a1);
     jfieldID fid = jenv->GetFieldID(mc, "value", "I");
     jenv->SetIntField(a1, fid, (jint) _a1);
  }
  {
     jclass mc    = jenv->GetObjectClass(a2);
     jfieldID fid = jenv->GetFieldID(mc, "value", "I");
     jenv->SetIntField(a2, fid, (jint) _a2);
  }
  {
     jclass mc    = jenv->GetObjectClass(a3);
     jfieldID fid = jenv->GetFieldID(mc, "value", "I");
     jenv->SetIntField(a3, fid, (jint) _a3);
  }
}
JNIEXPORT void JNICALL Java_Z3Native_enableTrace(JNIEnv * jenv, jclass cls, jstring a0) {
  Z3_string _a0 = (Z3_string) jenv->GetStringUTFChars(a0, NULL);
  Z3_enable_trace(_a0);
}
JNIEXPORT void JNICALL Java_Z3Native_disableTrace(JNIEnv * jenv, jclass cls, jstring a0) {
  Z3_string _a0 = (Z3_string) jenv->GetStringUTFChars(a0, NULL);
  Z3_disable_trace(_a0);
}
JNIEXPORT void JNICALL Java_Z3Native_resetMemory(JNIEnv * jenv, jclass cls) {
  Z3_reset_memory();
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkFixedpoint(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_fixedpoint result = Z3_mk_fixedpoint((Z3_context)a0);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_fixedpointIncRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_fixedpoint_inc_ref((Z3_context)a0, (Z3_fixedpoint)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_fixedpointDecRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_fixedpoint_dec_ref((Z3_context)a0, (Z3_fixedpoint)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_fixedpointAddRule(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jlong a3) {
  Z3_fixedpoint_add_rule((Z3_context)a0, (Z3_fixedpoint)a1, (Z3_ast)a2, (Z3_symbol)a3);
}
JNIEXPORT void JNICALL Java_Z3Native_fixedpointAddFact(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jint a3, jintArray a4) {
  unsigned * _a4 = (unsigned *) jenv->GetIntArrayElements(a4, NULL);
  Z3_fixedpoint_add_fact((Z3_context)a0, (Z3_fixedpoint)a1, (Z3_func_decl)a2, (unsigned)a3, _a4);
  jenv->ReleaseIntArrayElements(a4, (jint *) _a4, JNI_ABORT);
}
JNIEXPORT void JNICALL Java_Z3Native_fixedpointAssert(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_fixedpoint_assert((Z3_context)a0, (Z3_fixedpoint)a1, (Z3_ast)a2);
}
JNIEXPORT jint JNICALL Java_Z3Native_fixedpointQuery(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  int result = Z3_fixedpoint_query((Z3_context)a0, (Z3_fixedpoint)a1, (Z3_ast)a2);
  return (jint) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_fixedpointQueryRelations(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jlongArray a3) {
  Z3_func_decl * _a3 = (Z3_func_decl *) jenv->GetLongArrayElements(a3, NULL);
  int result = Z3_fixedpoint_query_relations((Z3_context)a0, (Z3_fixedpoint)a1, (unsigned)a2, _a3);
  jenv->ReleaseLongArrayElements(a3, (jlong *) _a3, JNI_ABORT);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_fixedpointGetAnswer(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_fixedpoint_get_answer((Z3_context)a0, (Z3_fixedpoint)a1);
  return (jlong) result;
}
JNIEXPORT jstring JNICALL Java_Z3Native_fixedpointGetReasonUnknown(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_string result = Z3_fixedpoint_get_reason_unknown((Z3_context)a0, (Z3_fixedpoint)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT void JNICALL Java_Z3Native_fixedpointUpdateRule(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jlong a3) {
  Z3_fixedpoint_update_rule((Z3_context)a0, (Z3_fixedpoint)a1, (Z3_ast)a2, (Z3_symbol)a3);
}
JNIEXPORT jint JNICALL Java_Z3Native_fixedpointGetNumLevels(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  unsigned result = Z3_fixedpoint_get_num_levels((Z3_context)a0, (Z3_fixedpoint)a1, (Z3_func_decl)a2);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_fixedpointGetCoverDelta(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jlong a3) {
  Z3_ast result = Z3_fixedpoint_get_cover_delta((Z3_context)a0, (Z3_fixedpoint)a1, (int)a2, (Z3_func_decl)a3);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_fixedpointAddCover(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jlong a3, jlong a4) {
  Z3_fixedpoint_add_cover((Z3_context)a0, (Z3_fixedpoint)a1, (int)a2, (Z3_func_decl)a3, (Z3_ast)a4);
}
JNIEXPORT jlong JNICALL Java_Z3Native_fixedpointGetStatistics(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_stats result = Z3_fixedpoint_get_statistics((Z3_context)a0, (Z3_fixedpoint)a1);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_fixedpointRegisterRelation(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_fixedpoint_register_relation((Z3_context)a0, (Z3_fixedpoint)a1, (Z3_func_decl)a2);
}
JNIEXPORT void JNICALL Java_Z3Native_fixedpointSetPredicateRepresentation(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jint a3, jlongArray a4) {
  Z3_symbol * _a4 = (Z3_symbol *) jenv->GetLongArrayElements(a4, NULL);
  Z3_fixedpoint_set_predicate_representation((Z3_context)a0, (Z3_fixedpoint)a1, (Z3_func_decl)a2, (unsigned)a3, _a4);
  jenv->ReleaseLongArrayElements(a4, (jlong *) _a4, JNI_ABORT);
}
JNIEXPORT jlong JNICALL Java_Z3Native_fixedpointGetRules(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast_vector result = Z3_fixedpoint_get_rules((Z3_context)a0, (Z3_fixedpoint)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_fixedpointGetAssertions(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast_vector result = Z3_fixedpoint_get_assertions((Z3_context)a0, (Z3_fixedpoint)a1);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_fixedpointSetParams(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_fixedpoint_set_params((Z3_context)a0, (Z3_fixedpoint)a1, (Z3_params)a2);
}
JNIEXPORT jstring JNICALL Java_Z3Native_fixedpointGetHelp(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_string result = Z3_fixedpoint_get_help((Z3_context)a0, (Z3_fixedpoint)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jlong JNICALL Java_Z3Native_fixedpointGetParamDescrs(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_param_descrs result = Z3_fixedpoint_get_param_descrs((Z3_context)a0, (Z3_fixedpoint)a1);
  return (jlong) result;
}
JNIEXPORT jstring JNICALL Java_Z3Native_fixedpointToString(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jlongArray a3) {
  Z3_ast * _a3 = (Z3_ast *) jenv->GetLongArrayElements(a3, NULL);
  Z3_string result = Z3_fixedpoint_to_string((Z3_context)a0, (Z3_fixedpoint)a1, (unsigned)a2, _a3);
  jenv->ReleaseLongArrayElements(a3, (jlong *) _a3, JNI_ABORT);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jlong JNICALL Java_Z3Native_fixedpointFromString(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jstring a2) {
  Z3_string _a2 = (Z3_string) jenv->GetStringUTFChars(a2, NULL);
  Z3_ast_vector result = Z3_fixedpoint_from_string((Z3_context)a0, (Z3_fixedpoint)a1, _a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_fixedpointFromFile(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jstring a2) {
  Z3_string _a2 = (Z3_string) jenv->GetStringUTFChars(a2, NULL);
  Z3_ast_vector result = Z3_fixedpoint_from_file((Z3_context)a0, (Z3_fixedpoint)a1, _a2);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_fixedpointPush(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_fixedpoint_push((Z3_context)a0, (Z3_fixedpoint)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_fixedpointPop(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_fixedpoint_pop((Z3_context)a0, (Z3_fixedpoint)a1);
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkAstVector(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_ast_vector result = Z3_mk_ast_vector((Z3_context)a0);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_astVectorIncRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast_vector_inc_ref((Z3_context)a0, (Z3_ast_vector)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_astVectorDecRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast_vector_dec_ref((Z3_context)a0, (Z3_ast_vector)a1);
}
JNIEXPORT jint JNICALL Java_Z3Native_astVectorSize(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_ast_vector_size((Z3_context)a0, (Z3_ast_vector)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_astVectorGet(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_ast result = Z3_ast_vector_get((Z3_context)a0, (Z3_ast_vector)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_astVectorSet(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jlong a3) {
  Z3_ast_vector_set((Z3_context)a0, (Z3_ast_vector)a1, (unsigned)a2, (Z3_ast)a3);
}
JNIEXPORT void JNICALL Java_Z3Native_astVectorResize(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_ast_vector_resize((Z3_context)a0, (Z3_ast_vector)a1, (unsigned)a2);
}
JNIEXPORT void JNICALL Java_Z3Native_astVectorPush(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast_vector_push((Z3_context)a0, (Z3_ast_vector)a1, (Z3_ast)a2);
}
JNIEXPORT jlong JNICALL Java_Z3Native_astVectorTranslate(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast_vector result = Z3_ast_vector_translate((Z3_context)a0, (Z3_ast_vector)a1, (Z3_context)a2);
  return (jlong) result;
}
JNIEXPORT jstring JNICALL Java_Z3Native_astVectorToString(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_string result = Z3_ast_vector_to_string((Z3_context)a0, (Z3_ast_vector)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkAstMap(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_ast_map result = Z3_mk_ast_map((Z3_context)a0);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_astMapIncRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast_map_inc_ref((Z3_context)a0, (Z3_ast_map)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_astMapDecRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast_map_dec_ref((Z3_context)a0, (Z3_ast_map)a1);
}
JNIEXPORT jboolean JNICALL Java_Z3Native_astMapContains(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_bool result = Z3_ast_map_contains((Z3_context)a0, (Z3_ast_map)a1, (Z3_ast)a2);
  return (jboolean) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_astMapFind(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast result = Z3_ast_map_find((Z3_context)a0, (Z3_ast_map)a1, (Z3_ast)a2);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_astMapInsert(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jlong a3) {
  Z3_ast_map_insert((Z3_context)a0, (Z3_ast_map)a1, (Z3_ast)a2, (Z3_ast)a3);
}
JNIEXPORT void JNICALL Java_Z3Native_astMapErase(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_ast_map_erase((Z3_context)a0, (Z3_ast_map)a1, (Z3_ast)a2);
}
JNIEXPORT void JNICALL Java_Z3Native_astMapReset(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast_map_reset((Z3_context)a0, (Z3_ast_map)a1);
}
JNIEXPORT jint JNICALL Java_Z3Native_astMapSize(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_ast_map_size((Z3_context)a0, (Z3_ast_map)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_astMapKeys(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast_vector result = Z3_ast_map_keys((Z3_context)a0, (Z3_ast_map)a1);
  return (jlong) result;
}
JNIEXPORT jstring JNICALL Java_Z3Native_astMapToString(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_string result = Z3_ast_map_to_string((Z3_context)a0, (Z3_ast_map)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkGoal(JNIEnv * jenv, jclass cls, jlong a0, jboolean a1, jboolean a2, jboolean a3) {
  Z3_goal result = Z3_mk_goal((Z3_context)a0, (Z3_bool)a1, (Z3_bool)a2, (Z3_bool)a3);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_goalIncRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_goal_inc_ref((Z3_context)a0, (Z3_goal)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_goalDecRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_goal_dec_ref((Z3_context)a0, (Z3_goal)a1);
}
JNIEXPORT jint JNICALL Java_Z3Native_goalPrecision(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_goal_precision((Z3_context)a0, (Z3_goal)a1);
  return (jint) result;
}
JNIEXPORT void JNICALL Java_Z3Native_goalAssert(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_goal_assert((Z3_context)a0, (Z3_goal)a1, (Z3_ast)a2);
}
JNIEXPORT jboolean JNICALL Java_Z3Native_goalInconsistent(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_bool result = Z3_goal_inconsistent((Z3_context)a0, (Z3_goal)a1);
  return (jboolean) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_goalDepth(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_goal_depth((Z3_context)a0, (Z3_goal)a1);
  return (jint) result;
}
JNIEXPORT void JNICALL Java_Z3Native_goalReset(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_goal_reset((Z3_context)a0, (Z3_goal)a1);
}
JNIEXPORT jint JNICALL Java_Z3Native_goalSize(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_goal_size((Z3_context)a0, (Z3_goal)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_goalFormula(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_ast result = Z3_goal_formula((Z3_context)a0, (Z3_goal)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_goalNumExprs(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_goal_num_exprs((Z3_context)a0, (Z3_goal)a1);
  return (jint) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_goalIsDecidedSat(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_bool result = Z3_goal_is_decided_sat((Z3_context)a0, (Z3_goal)a1);
  return (jboolean) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_goalIsDecidedUnsat(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_bool result = Z3_goal_is_decided_unsat((Z3_context)a0, (Z3_goal)a1);
  return (jboolean) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_goalTranslate(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_goal result = Z3_goal_translate((Z3_context)a0, (Z3_goal)a1, (Z3_context)a2);
  return (jlong) result;
}
JNIEXPORT jstring JNICALL Java_Z3Native_goalToString(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_string result = Z3_goal_to_string((Z3_context)a0, (Z3_goal)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkTactic(JNIEnv * jenv, jclass cls, jlong a0, jstring a1) {
  Z3_string _a1 = (Z3_string) jenv->GetStringUTFChars(a1, NULL);
  Z3_tactic result = Z3_mk_tactic((Z3_context)a0, _a1);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_tacticIncRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_tactic_inc_ref((Z3_context)a0, (Z3_tactic)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_tacticDecRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_tactic_dec_ref((Z3_context)a0, (Z3_tactic)a1);
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkProbe(JNIEnv * jenv, jclass cls, jlong a0, jstring a1) {
  Z3_string _a1 = (Z3_string) jenv->GetStringUTFChars(a1, NULL);
  Z3_probe result = Z3_mk_probe((Z3_context)a0, _a1);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_probeIncRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_probe_inc_ref((Z3_context)a0, (Z3_probe)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_probeDecRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_probe_dec_ref((Z3_context)a0, (Z3_probe)a1);
}
JNIEXPORT jlong JNICALL Java_Z3Native_tacticAndThen(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_tactic result = Z3_tactic_and_then((Z3_context)a0, (Z3_tactic)a1, (Z3_tactic)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_tacticOrElse(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_tactic result = Z3_tactic_or_else((Z3_context)a0, (Z3_tactic)a1, (Z3_tactic)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_tacticParOr(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlongArray a2) {
  Z3_tactic * _a2 = (Z3_tactic *) jenv->GetLongArrayElements(a2, NULL);
  Z3_tactic result = Z3_tactic_par_or((Z3_context)a0, (unsigned)a1, _a2);
  jenv->ReleaseLongArrayElements(a2, (jlong *) _a2, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_tacticParAndThen(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_tactic result = Z3_tactic_par_and_then((Z3_context)a0, (Z3_tactic)a1, (Z3_tactic)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_tacticTryFor(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_tactic result = Z3_tactic_try_for((Z3_context)a0, (Z3_tactic)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_tacticWhen(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_tactic result = Z3_tactic_when((Z3_context)a0, (Z3_probe)a1, (Z3_tactic)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_tacticCond(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jlong a3) {
  Z3_tactic result = Z3_tactic_cond((Z3_context)a0, (Z3_probe)a1, (Z3_tactic)a2, (Z3_tactic)a3);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_tacticRepeat(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_tactic result = Z3_tactic_repeat((Z3_context)a0, (Z3_tactic)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_tacticSkip(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_tactic result = Z3_tactic_skip((Z3_context)a0);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_tacticFail(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_tactic result = Z3_tactic_fail((Z3_context)a0);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_tacticFailIf(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_tactic result = Z3_tactic_fail_if((Z3_context)a0, (Z3_probe)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_tacticFailIfNotDecided(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_tactic result = Z3_tactic_fail_if_not_decided((Z3_context)a0);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_tacticUsingParams(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_tactic result = Z3_tactic_using_params((Z3_context)a0, (Z3_tactic)a1, (Z3_params)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_probeConst(JNIEnv * jenv, jclass cls, jlong a0, jdouble a1) {
  Z3_probe result = Z3_probe_const((Z3_context)a0, (double)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_probeLt(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_probe result = Z3_probe_lt((Z3_context)a0, (Z3_probe)a1, (Z3_probe)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_probeGt(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_probe result = Z3_probe_gt((Z3_context)a0, (Z3_probe)a1, (Z3_probe)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_probeLe(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_probe result = Z3_probe_le((Z3_context)a0, (Z3_probe)a1, (Z3_probe)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_probeGe(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_probe result = Z3_probe_ge((Z3_context)a0, (Z3_probe)a1, (Z3_probe)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_probeEq(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_probe result = Z3_probe_eq((Z3_context)a0, (Z3_probe)a1, (Z3_probe)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_probeAnd(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_probe result = Z3_probe_and((Z3_context)a0, (Z3_probe)a1, (Z3_probe)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_probeOr(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_probe result = Z3_probe_or((Z3_context)a0, (Z3_probe)a1, (Z3_probe)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_probeNot(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_probe result = Z3_probe_not((Z3_context)a0, (Z3_probe)a1);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getNumTactics(JNIEnv * jenv, jclass cls, jlong a0) {
  unsigned result = Z3_get_num_tactics((Z3_context)a0);
  return (jint) result;
}
JNIEXPORT jstring JNICALL Java_Z3Native_getTacticName(JNIEnv * jenv, jclass cls, jlong a0, jint a1) {
  Z3_string result = Z3_get_tactic_name((Z3_context)a0, (unsigned)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jint JNICALL Java_Z3Native_getNumProbes(JNIEnv * jenv, jclass cls, jlong a0) {
  unsigned result = Z3_get_num_probes((Z3_context)a0);
  return (jint) result;
}
JNIEXPORT jstring JNICALL Java_Z3Native_getProbeName(JNIEnv * jenv, jclass cls, jlong a0, jint a1) {
  Z3_string result = Z3_get_probe_name((Z3_context)a0, (unsigned)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jstring JNICALL Java_Z3Native_tacticGetHelp(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_string result = Z3_tactic_get_help((Z3_context)a0, (Z3_tactic)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jlong JNICALL Java_Z3Native_tacticGetParamDescrs(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_param_descrs result = Z3_tactic_get_param_descrs((Z3_context)a0, (Z3_tactic)a1);
  return (jlong) result;
}
JNIEXPORT jstring JNICALL Java_Z3Native_tacticGetDescr(JNIEnv * jenv, jclass cls, jlong a0, jstring a1) {
  Z3_string _a1 = (Z3_string) jenv->GetStringUTFChars(a1, NULL);
  Z3_string result = Z3_tactic_get_descr((Z3_context)a0, _a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jstring JNICALL Java_Z3Native_probeGetDescr(JNIEnv * jenv, jclass cls, jlong a0, jstring a1) {
  Z3_string _a1 = (Z3_string) jenv->GetStringUTFChars(a1, NULL);
  Z3_string result = Z3_probe_get_descr((Z3_context)a0, _a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jdouble JNICALL Java_Z3Native_probeApply(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  double result = Z3_probe_apply((Z3_context)a0, (Z3_probe)a1, (Z3_goal)a2);
  return (jdouble) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_tacticApply(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_apply_result result = Z3_tactic_apply((Z3_context)a0, (Z3_tactic)a1, (Z3_goal)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_tacticApplyEx(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jlong a3) {
  Z3_apply_result result = Z3_tactic_apply_ex((Z3_context)a0, (Z3_tactic)a1, (Z3_goal)a2, (Z3_params)a3);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_applyResultIncRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_apply_result_inc_ref((Z3_context)a0, (Z3_apply_result)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_applyResultDecRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_apply_result_dec_ref((Z3_context)a0, (Z3_apply_result)a1);
}
JNIEXPORT jstring JNICALL Java_Z3Native_applyResultToString(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_string result = Z3_apply_result_to_string((Z3_context)a0, (Z3_apply_result)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jint JNICALL Java_Z3Native_applyResultGetNumSubgoals(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_apply_result_get_num_subgoals((Z3_context)a0, (Z3_apply_result)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_applyResultGetSubgoal(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_goal result = Z3_apply_result_get_subgoal((Z3_context)a0, (Z3_apply_result)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_applyResultConvertModel(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jlong a3) {
  Z3_model result = Z3_apply_result_convert_model((Z3_context)a0, (Z3_apply_result)a1, (unsigned)a2, (Z3_model)a3);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkSolver(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_solver result = Z3_mk_solver((Z3_context)a0);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkSimpleSolver(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_solver result = Z3_mk_simple_solver((Z3_context)a0);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkSolverForLogic(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_solver result = Z3_mk_solver_for_logic((Z3_context)a0, (Z3_symbol)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkSolverFromTactic(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_solver result = Z3_mk_solver_from_tactic((Z3_context)a0, (Z3_tactic)a1);
  return (jlong) result;
}
JNIEXPORT jstring JNICALL Java_Z3Native_solverGetHelp(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_string result = Z3_solver_get_help((Z3_context)a0, (Z3_solver)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jlong JNICALL Java_Z3Native_solverGetParamDescrs(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_param_descrs result = Z3_solver_get_param_descrs((Z3_context)a0, (Z3_solver)a1);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_solverSetParams(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_solver_set_params((Z3_context)a0, (Z3_solver)a1, (Z3_params)a2);
}
JNIEXPORT void JNICALL Java_Z3Native_solverIncRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_solver_inc_ref((Z3_context)a0, (Z3_solver)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_solverDecRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_solver_dec_ref((Z3_context)a0, (Z3_solver)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_solverPush(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_solver_push((Z3_context)a0, (Z3_solver)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_solverPop(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_solver_pop((Z3_context)a0, (Z3_solver)a1, (unsigned)a2);
}
JNIEXPORT void JNICALL Java_Z3Native_solverReset(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_solver_reset((Z3_context)a0, (Z3_solver)a1);
}
JNIEXPORT jint JNICALL Java_Z3Native_solverGetNumScopes(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_solver_get_num_scopes((Z3_context)a0, (Z3_solver)a1);
  return (jint) result;
}
JNIEXPORT void JNICALL Java_Z3Native_solverAssert(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2) {
  Z3_solver_assert((Z3_context)a0, (Z3_solver)a1, (Z3_ast)a2);
}
JNIEXPORT void JNICALL Java_Z3Native_solverAssertAndTrack(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jlong a3) {
  Z3_solver_assert_and_track((Z3_context)a0, (Z3_solver)a1, (Z3_ast)a2, (Z3_ast)a3);
}
JNIEXPORT jlong JNICALL Java_Z3Native_solverGetAssertions(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast_vector result = Z3_solver_get_assertions((Z3_context)a0, (Z3_solver)a1);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_solverCheck(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  int result = Z3_solver_check((Z3_context)a0, (Z3_solver)a1);
  return (jint) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_solverCheckAssumptions(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jlongArray a3) {
  Z3_ast * _a3 = (Z3_ast *) jenv->GetLongArrayElements(a3, NULL);
  int result = Z3_solver_check_assumptions((Z3_context)a0, (Z3_solver)a1, (unsigned)a2, _a3);
  jenv->ReleaseLongArrayElements(a3, (jlong *) _a3, JNI_ABORT);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_solverGetModel(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_model result = Z3_solver_get_model((Z3_context)a0, (Z3_solver)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_solverGetProof(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast result = Z3_solver_get_proof((Z3_context)a0, (Z3_solver)a1);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_solverGetUnsatCore(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_ast_vector result = Z3_solver_get_unsat_core((Z3_context)a0, (Z3_solver)a1);
  return (jlong) result;
}
JNIEXPORT jstring JNICALL Java_Z3Native_solverGetReasonUnknown(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_string result = Z3_solver_get_reason_unknown((Z3_context)a0, (Z3_solver)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jlong JNICALL Java_Z3Native_solverGetStatistics(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_stats result = Z3_solver_get_statistics((Z3_context)a0, (Z3_solver)a1);
  return (jlong) result;
}
JNIEXPORT jstring JNICALL Java_Z3Native_solverToString(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_string result = Z3_solver_to_string((Z3_context)a0, (Z3_solver)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jstring JNICALL Java_Z3Native_statsToString(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_string result = Z3_stats_to_string((Z3_context)a0, (Z3_stats)a1);
  return jenv->NewStringUTF(result);
}
JNIEXPORT void JNICALL Java_Z3Native_statsIncRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_stats_inc_ref((Z3_context)a0, (Z3_stats)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_statsDecRef(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_stats_dec_ref((Z3_context)a0, (Z3_stats)a1);
}
JNIEXPORT jint JNICALL Java_Z3Native_statsSize(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_stats_size((Z3_context)a0, (Z3_stats)a1);
  return (jint) result;
}
JNIEXPORT jstring JNICALL Java_Z3Native_statsGetKey(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_string result = Z3_stats_get_key((Z3_context)a0, (Z3_stats)a1, (unsigned)a2);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jboolean JNICALL Java_Z3Native_statsIsUint(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_bool result = Z3_stats_is_uint((Z3_context)a0, (Z3_stats)a1, (unsigned)a2);
  return (jboolean) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_statsIsDouble(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_bool result = Z3_stats_is_double((Z3_context)a0, (Z3_stats)a1, (unsigned)a2);
  return (jboolean) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_statsGetUintValue(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  unsigned result = Z3_stats_get_uint_value((Z3_context)a0, (Z3_stats)a1, (unsigned)a2);
  return (jint) result;
}
JNIEXPORT jdouble JNICALL Java_Z3Native_statsGetDoubleValue(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  double result = Z3_stats_get_double_value((Z3_context)a0, (Z3_stats)a1, (unsigned)a2);
  return (jdouble) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkInjectiveFunction(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jlongArray a3, jlong a4) {
  Z3_sort * _a3 = (Z3_sort *) jenv->GetLongArrayElements(a3, NULL);
  Z3_func_decl result = Z3_mk_injective_function((Z3_context)a0, (Z3_symbol)a1, (unsigned)a2, _a3, (Z3_sort)a4);
  jenv->ReleaseLongArrayElements(a3, (jlong *) _a3, JNI_ABORT);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_setLogic(JNIEnv * jenv, jclass cls, jlong a0, jstring a1) {
  Z3_string _a1 = (Z3_string) jenv->GetStringUTFChars(a1, NULL);
  Z3_set_logic((Z3_context)a0, _a1);
}
JNIEXPORT void JNICALL Java_Z3Native_push(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_push((Z3_context)a0);
}
JNIEXPORT void JNICALL Java_Z3Native_pop(JNIEnv * jenv, jclass cls, jlong a0, jint a1) {
  Z3_pop((Z3_context)a0, (unsigned)a1);
}
JNIEXPORT jint JNICALL Java_Z3Native_getNumScopes(JNIEnv * jenv, jclass cls, jlong a0) {
  unsigned result = Z3_get_num_scopes((Z3_context)a0);
  return (jint) result;
}
JNIEXPORT void JNICALL Java_Z3Native_persistAst(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_persist_ast((Z3_context)a0, (Z3_ast)a1, (unsigned)a2);
}
JNIEXPORT void JNICALL Java_Z3Native_assertCnstr(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_assert_cnstr((Z3_context)a0, (Z3_ast)a1);
}
JNIEXPORT jint JNICALL Java_Z3Native_checkAndGetModel(JNIEnv * jenv, jclass cls, jlong a0, jobject a1) {
  Z3_model _a1;
  int result = Z3_check_and_get_model((Z3_context)a0, &_a1);
  {
     jclass mc    = jenv->GetObjectClass(a1);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a1, fid, (jlong) _a1);
  }
  return (jint) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_check(JNIEnv * jenv, jclass cls, jlong a0) {
  int result = Z3_check((Z3_context)a0);
  return (jint) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_checkAssumptions(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlongArray a2, jobject a3, jobject a4, jobject a5, jlongArray a6) {
  Z3_ast * _a2 = (Z3_ast *) jenv->GetLongArrayElements(a2, NULL);
  Z3_model _a3;
  Z3_ast _a4;
  unsigned _a5;
  Z3_ast * _a6 = (Z3_ast *) malloc(((unsigned)a1) * sizeof(Z3_ast));
  int result = Z3_check_assumptions((Z3_context)a0, (unsigned)a1, _a2, &_a3, &_a4, &_a5, _a6);
  jenv->ReleaseLongArrayElements(a2, (jlong *) _a2, JNI_ABORT);
  {
     jclass mc    = jenv->GetObjectClass(a3);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a3, fid, (jlong) _a3);
  }
  {
     jclass mc    = jenv->GetObjectClass(a4);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a4, fid, (jlong) _a4);
  }
  {
     jclass mc    = jenv->GetObjectClass(a5);
     jfieldID fid = jenv->GetFieldID(mc, "value", "I");
     jenv->SetIntField(a5, fid, (jint) _a5);
  }
  jenv->SetLongArrayRegion(a6, 0, (jsize)a1, (jlong *) _a6);
  free(_a6);
  return (jint) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getImpliedEqualities(JNIEnv * jenv, jclass cls, jlong a0, jint a1, jlongArray a2, jintArray a3) {
  Z3_ast * _a2 = (Z3_ast *) jenv->GetLongArrayElements(a2, NULL);
  unsigned * _a3 = (unsigned *) malloc(((unsigned)a1) * sizeof(unsigned));
  unsigned result = Z3_get_implied_equalities((Z3_context)a0, (unsigned)a1, _a2, _a3);
  jenv->ReleaseLongArrayElements(a2, (jlong *) _a2, JNI_ABORT);
  jenv->SetIntArrayRegion(a3, 0, (jsize)a1, (jint *) _a3);
  free(_a3);
  return (jint) result;
}
JNIEXPORT void JNICALL Java_Z3Native_delModel(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_del_model((Z3_context)a0, (Z3_model)a1);
}
JNIEXPORT void JNICALL Java_Z3Native_softCheckCancel(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_soft_check_cancel((Z3_context)a0);
}
JNIEXPORT jint JNICALL Java_Z3Native_getSearchFailure(JNIEnv * jenv, jclass cls, jlong a0) {
  unsigned result = Z3_get_search_failure((Z3_context)a0);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_mkLabel(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jboolean a2, jlong a3) {
  Z3_ast result = Z3_mk_label((Z3_context)a0, (Z3_symbol)a1, (Z3_bool)a2, (Z3_ast)a3);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getRelevantLabels(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_literals result = Z3_get_relevant_labels((Z3_context)a0);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getRelevantLiterals(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_literals result = Z3_get_relevant_literals((Z3_context)a0);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getGuessedLiterals(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_literals result = Z3_get_guessed_literals((Z3_context)a0);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_delLiterals(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_del_literals((Z3_context)a0, (Z3_literals)a1);
}
JNIEXPORT jint JNICALL Java_Z3Native_getNumLiterals(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_num_literals((Z3_context)a0, (Z3_literals)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getLabelSymbol(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_symbol result = Z3_get_label_symbol((Z3_context)a0, (Z3_literals)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getLiteral(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_ast result = Z3_get_literal((Z3_context)a0, (Z3_literals)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT void JNICALL Java_Z3Native_disableLiteral(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_disable_literal((Z3_context)a0, (Z3_literals)a1, (unsigned)a2);
}
JNIEXPORT void JNICALL Java_Z3Native_blockLiterals(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  Z3_block_literals((Z3_context)a0, (Z3_literals)a1);
}
JNIEXPORT jint JNICALL Java_Z3Native_getModelNumConstants(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_model_num_constants((Z3_context)a0, (Z3_model)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getModelConstant(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_func_decl result = Z3_get_model_constant((Z3_context)a0, (Z3_model)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getModelNumFuncs(JNIEnv * jenv, jclass cls, jlong a0, jlong a1) {
  unsigned result = Z3_get_model_num_funcs((Z3_context)a0, (Z3_model)a1);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getModelFuncDecl(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_func_decl result = Z3_get_model_func_decl((Z3_context)a0, (Z3_model)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_evalFuncDecl(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jobject a3) {
  Z3_ast _a3;
  Z3_bool result = Z3_eval_func_decl((Z3_context)a0, (Z3_model)a1, (Z3_func_decl)a2, &_a3);
  {
     jclass mc    = jenv->GetObjectClass(a3);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a3, fid, (jlong) _a3);
  }
  return (jboolean) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_isArrayValue(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jobject a3) {
  unsigned _a3;
  Z3_bool result = Z3_is_array_value((Z3_context)a0, (Z3_model)a1, (Z3_ast)a2, &_a3);
  {
     jclass mc    = jenv->GetObjectClass(a3);
     jfieldID fid = jenv->GetFieldID(mc, "value", "I");
     jenv->SetIntField(a3, fid, (jint) _a3);
  }
  return (jboolean) result;
}
JNIEXPORT void JNICALL Java_Z3Native_getArrayValue(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jint a3, jlongArray a4, jlongArray a5, jobject a6) {
  Z3_ast * _a4 = (Z3_ast *) malloc(((unsigned)a3) * sizeof(Z3_ast));
  Z3_ast * _a5 = (Z3_ast *) malloc(((unsigned)a3) * sizeof(Z3_ast));
  Z3_ast _a6;
  Z3_get_array_value((Z3_context)a0, (Z3_model)a1, (Z3_ast)a2, (unsigned)a3, _a4, _a5, &_a6);
  jenv->SetLongArrayRegion(a4, 0, (jsize)a3, (jlong *) _a4);
  free(_a4);
  jenv->SetLongArrayRegion(a5, 0, (jsize)a3, (jlong *) _a5);
  free(_a5);
  {
     jclass mc    = jenv->GetObjectClass(a6);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a6, fid, (jlong) _a6);
  }
}
JNIEXPORT jlong JNICALL Java_Z3Native_getModelFuncElse(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  Z3_ast result = Z3_get_model_func_else((Z3_context)a0, (Z3_model)a1, (unsigned)a2);
  return (jlong) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getModelFuncNumEntries(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2) {
  unsigned result = Z3_get_model_func_num_entries((Z3_context)a0, (Z3_model)a1, (unsigned)a2);
  return (jint) result;
}
JNIEXPORT jint JNICALL Java_Z3Native_getModelFuncEntryNumArgs(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jint a3) {
  unsigned result = Z3_get_model_func_entry_num_args((Z3_context)a0, (Z3_model)a1, (unsigned)a2, (unsigned)a3);
  return (jint) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getModelFuncEntryArg(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jint a3, jint a4) {
  Z3_ast result = Z3_get_model_func_entry_arg((Z3_context)a0, (Z3_model)a1, (unsigned)a2, (unsigned)a3, (unsigned)a4);
  return (jlong) result;
}
JNIEXPORT jlong JNICALL Java_Z3Native_getModelFuncEntryValue(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jint a2, jint a3) {
  Z3_ast result = Z3_get_model_func_entry_value((Z3_context)a0, (Z3_model)a1, (unsigned)a2, (unsigned)a3);
  return (jlong) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_eval(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jobject a3) {
  Z3_ast _a3;
  Z3_bool result = Z3_eval((Z3_context)a0, (Z3_model)a1, (Z3_ast)a2, &_a3);
  {
     jclass mc    = jenv->GetObjectClass(a3);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a3, fid, (jlong) _a3);
  }
  return (jboolean) result;
}
JNIEXPORT jboolean JNICALL Java_Z3Native_evalDecl(JNIEnv * jenv, jclass cls, jlong a0, jlong a1, jlong a2, jint a3, jlongArray a4, jobject a5) {
  Z3_ast * _a4 = (Z3_ast *) jenv->GetLongArrayElements(a4, NULL);
  Z3_ast _a5;
  Z3_bool result = Z3_eval_decl((Z3_context)a0, (Z3_model)a1, (Z3_func_decl)a2, (unsigned)a3, _a4, &_a5);
  jenv->ReleaseLongArrayElements(a4, (jlong *) _a4, JNI_ABORT);
  {
     jclass mc    = jenv->GetObjectClass(a5);
     jfieldID fid = jenv->GetFieldID(mc, "value", "J");
     jenv->SetLongField(a5, fid, (jlong) _a5);
  }
  return (jboolean) result;
}
JNIEXPORT jstring JNICALL Java_Z3Native_contextToString(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_string result = Z3_context_to_string((Z3_context)a0);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jstring JNICALL Java_Z3Native_statisticsToString(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_string result = Z3_statistics_to_string((Z3_context)a0);
  return jenv->NewStringUTF(result);
}
JNIEXPORT jlong JNICALL Java_Z3Native_getContextAssignment(JNIEnv * jenv, jclass cls, jlong a0) {
  Z3_ast result = Z3_get_context_assignment((Z3_context)a0);
  return (jlong) result;
}
#ifdef __cplusplus
}
#endif
