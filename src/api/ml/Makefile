# to set ARGS, invoke as e.g.:  $ make ARGS='-DUNSAFE_ERRORS -DLEAK_CONTEXTS'
ARGS=


default: z3.ml z3.mli z3_stubs.c


%.ml %.mli %_stubs.c: ../%_api.h %.0.idl x3.ml x3V3.ml x3V3.mli \
	error_handling.idl mlx_get_app_args.idl mlx_get_array_sort.idl mlx_get_datatype_sort.idl mlx_get_domains.idl mlx_get_error_msg.idl mlx_get_pattern_terms.idl mlx_get_tuple_sort.idl mlx_mk_context_x.idl mlx_mk_datatypes.idl mlx_mk_numeral.idl mlx_mk_sort.idl mlx_mk_symbol.idl mlx_model.idl mlx_numeral_refine.idl mlx_parse_smtlib.idl mlx_sort_refine.idl mlx_statistics.idl mlx_symbol_refine.idl mlx_term_refine.idl \
	generate_mlapi.sh add_error_checking.V3.sed add_error_checking.sed preprocess.sed postprocess.sed reverse.sed
	./generate_mlapi.sh $(ARGS)

clean:
	rm -f z3.ml z3.mli z3_stubs.c
