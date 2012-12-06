# Customize error handling for contexts created in ML:
s/Z3_API Z3_mk_context(\(.*\))/Z3_API Z3_mk_context(\1) quote(dealloc,\"Z3_set_error_handler(_res, (void*)caml_z3_error_handler);\")/g
