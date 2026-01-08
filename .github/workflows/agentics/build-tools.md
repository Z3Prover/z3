# Build Tools Configuration

This file contains build tool configurations and instructions for agentic workflows.

## OCaml Build Instructions

To build Z3 with OCaml bindings, follow these steps:

### System Dependencies

**Ubuntu/Linux:**
```bash
sudo apt-get update
sudo apt-get install -y bubblewrap m4 libgmp-dev pkg-config ninja-build ccache
```

**macOS:**
```bash
brew install gmp pkg-config ninja ccache
```

### OCaml Setup

1. Install OCaml using opam (OCaml Package Manager):
```bash
# Setup OCaml 5.x with opam
# Note: In GitHub Actions, use ocaml/setup-ocaml@v3 action
opam init -y --disable-sandboxing
eval $(opam env)
```

2. Install required OCaml packages:
```bash
opam install -y ocamlfind zarith
```

### Configure Z3 with OCaml Bindings

```bash
mkdir -p build
cd build

# Ensure opam environment is loaded
eval $(opam env)

# Verify OCaml tools are available
echo "OCAMLFIND: $(which ocamlfind)"
echo "OCAMLC: $(which ocamlc)"
echo "OCAMLOPT: $(which ocamlopt)"
echo "OCAML_VERSION: $(ocamlc -version)"

# Configure with CMake
cmake .. \
  -G Ninja \
  -DZ3_BUILD_LIBZ3_SHARED=ON \
  -DZ3_BUILD_OCAML_BINDINGS=ON \
  -DZ3_BUILD_JAVA_BINDINGS=OFF \
  -DZ3_BUILD_PYTHON_BINDINGS=OFF \
  -DZ3_BUILD_CLI=OFF \
  -DZ3_BUILD_TEST_EXECUTABLES=OFF \
  -DCMAKE_VERBOSE_MAKEFILE=TRUE
```

### Build Z3 and OCaml Bindings

```bash
cd build
eval $(opam env)

# Enable ccache if available
ccache -z || true

# Build the OCaml bindings
ninja build_z3_ocaml_bindings

# Show ccache statistics
ccache -s || true
```

### Test OCaml Bindings

**Compile and run bytecode example:**
```bash
eval $(opam env)

# Compile bytecode version
ocamlfind ocamlc -o ml_example.byte \
  -package zarith \
  -linkpkg \
  -I build/src/api/ml \
  -dllpath build/src/api/ml \
  build/src/api/ml/z3ml.cma \
  examples/ml/ml_example.ml

# Run bytecode example
export DYLD_LIBRARY_PATH=$(pwd)/build
ocamlrun ./ml_example.byte
```

**Compile and run native example:**
```bash
eval $(opam env)

# Compile native version
ocamlfind ocamlopt -o ml_example \
  -package zarith \
  -linkpkg \
  -I build/src/api/ml \
  build/src/api/ml/z3ml.cmxa \
  examples/ml/ml_example.ml

# Run native example
export DYLD_LIBRARY_PATH=$(pwd)/build
./ml_example
```

## Environment Variables

When building with OCaml, ensure these environment variables are set:

```bash
eval $(opam env)
export DYLD_LIBRARY_PATH=$(pwd)/build  # For macOS
export LD_LIBRARY_PATH=$(pwd)/build    # For Linux
```

## Caching Recommendations

For faster builds in CI/CD:

1. **Cache ccache directory:** `~/.ccache`
2. **Cache opam directory:** `~/.opam`

Example cache keys:
- ccache: `${{ runner.os }}-ccache-${{ github.sha }}`
- opam: `${{ runner.os }}-opam-5-${{ github.sha }}`

## Troubleshooting

### Common Issues

1. **OCaml not found:** Ensure `eval $(opam env)` is run before each build command
2. **Library not found at runtime:** Set `DYLD_LIBRARY_PATH` or `LD_LIBRARY_PATH`
3. **zarith missing:** Run `opam install -y zarith`
4. **Ninja not found:** Install ninja-build package

### Verify OCaml Installation

```bash
eval $(opam env)
ocamlc -version
ocamlfind query zarith
which ocamlfind
```
