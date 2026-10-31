#!/usr/bin/env bash
set -euo pipefail

build_dir="$1"
prefix="$2"
libdir="$prefix/lib"
package_dir="$libdir/ocaml/z3"
stub_dir="$libdir/ocaml/stublibs"

case "$(uname -s)" in
    Linux) library_suffix=.so ;;
    Darwin) library_suffix=.dylib ;;
    *) echo "Unsupported OCaml installation test platform" >&2; exit 1 ;;
esac

cmake --install "$build_dir" --prefix "$prefix"

test -e "$libdir/libz3$library_suffix"
for artifact in META z3.mli z3.cmi z3.cmx \
    z3enums.mli z3enums.cmi z3enums.cmx \
    z3native.mli z3native.cmi z3native.cmx \
    libz3ml.a z3ml.a z3ml.cma z3ml.cmxa z3ml.cmxs; do
    test -f "$package_dir/$artifact"
done
test -f "$stub_dir/dllz3ml.so"

if [[ "$library_suffix" == .dylib ]]; then
    otool -L "$stub_dir/dllz3ml.so" | tee "$prefix/dllz3ml-otool.txt"
    grep -E '@rpath/libz3(\.[0-9]+)+\.dylib' "$prefix/dllz3ml-otool.txt"
    otool -l "$stub_dir/dllz3ml.so" | tee "$prefix/dllz3ml-load-commands.txt"
    grep '@loader_path/../../' "$prefix/dllz3ml-load-commands.txt"
fi

ocamlfind ocamlc -o "$prefix/ml_example.byte" \
    -package zarith -linkpkg \
    -I "$package_dir" -I "$stub_dir" -dllpath "$stub_dir" \
    "$package_dir/z3ml.cma" examples/ml/ml_example.ml

ocamlfind ocamlopt -o "$prefix/ml_example" \
    -package zarith -linkpkg \
    -I "$package_dir" -I "$stub_dir" \
    "$package_dir/z3ml.cmxa" examples/ml/ml_example.ml

export DYLD_LIBRARY_PATH="$libdir"
export LD_LIBRARY_PATH="$libdir"
ocamlrun "$prefix/ml_example.byte"
"$prefix/ml_example"
