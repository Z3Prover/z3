# Z3 Theorem Prover Development Guide

Always reference these instructions first and fallback to search or bash commands only when you encounter unexpected information that does not match the info here.

## Working Effectively

### Bootstrap and Build the Repository

Z3 supports multiple build systems. **ALWAYS** use one of these validated approaches:

#### Option 1: Python Build System (Recommended for most use cases)
- `python scripts/mk_make.py` -- takes 7 seconds to configure
- `cd build && make -j$(nproc)` -- takes 15 minutes to complete. **NEVER CANCEL**. Set timeout to 30+ minutes.

#### Option 2: CMake Build System (Recommended for integration)
- Clean source tree first if you previously used Python build: `git clean -fx src/`
- `mkdir build && cd build`
- `cmake ..` -- takes 1 second to configure
- `make -j$(nproc)` -- takes 17 minutes to complete. **NEVER CANCEL**. Set timeout to 30+ minutes.

#### Dependencies and Requirements
- Python 3.x (required for both build systems)
- C++20 capable compiler (g++ or clang++)
- GNU Make
- Git (for version information)

### Test the Repository

**Python Build System:**
- Build unit tests: `make test` -- takes 3.5 minutes to compile. **NEVER CANCEL**. Set timeout to 10+ minutes.
- Run unit tests: `./test-z3 /a` -- takes 16 seconds. **NEVER CANCEL**. Set timeout to 5+ minutes.

**CMake Build System:**
- Build unit tests: `make test-z3` -- takes 4 minutes to compile. **NEVER CANCEL**. Set timeout to 10+ minutes.
- Run unit tests: `./test-z3 /a` -- takes 16 seconds. **NEVER CANCEL**. Set timeout to 5+ minutes.

**Test basic Z3 functionality:**
```bash
./z3 --version
echo "(declare-const x Int)(assert (> x 0))(check-sat)(get-model)" | ./z3 -in
```

### Validation Scenarios

**ALWAYS** test these scenarios after making changes:

#### Basic SMT Solving
```bash
cd build
echo "(declare-const x Int)
(assert (> x 0))
(check-sat)
(get-model)" | ./z3 -in
```
Expected output: `sat` followed by a model showing `x = 1` or similar.

#### Python Bindings
```bash
cd build/python
python3 -c "import z3; x = z3.Int('x'); s = z3.Solver(); s.add(x > 0); print('Result:', s.check()); print('Model:', s.model())"
```
Expected output: `Result: sat` and `Model: [x = 1]` or similar.

#### Command Line Help
```bash
./z3 --help | head -10
```
Should display version and usage information.

## Build System Details

### Python Build System
- Configuration: `python scripts/mk_make.py` (7 seconds)
- Main build: `cd build && make -j$(nproc)` (15 minutes)
- Test build: `make test` (3.5 minutes)
- Generates build files in `build/` directory
- Creates Python bindings in `build/python/`
- **Warning**: Generates files in source tree that must be cleaned before using CMake

### CMake Build System  
- Clean first: `git clean -fx src/` (if switching from Python build)
- Configuration: `cmake ..` (1 second)
- Main build: `make -j$(nproc)` (17 minutes)
- **Advantages**: Clean build tree, no source pollution, better for integration
- **Recommended for**: IDE integration, package management, deployment

### Critical Timing and Timeout Requirements

**NEVER CANCEL these operations**:
- `make -j$(nproc)` builds: 15-17 minutes. **Set timeout to 30+ minutes minimum**.
- `make test` or `make test-z3` compilation: 3.5-4 minutes. **Set timeout to 10+ minutes**.
- Unit test execution: 16 seconds. **Set timeout to 5+ minutes**.

**Always wait for completion**. Z3 is a complex theorem prover with extensive code generation and builds may appear to hang but are actually progressing.

## Repository Structure

### Key Directories
- `src/` - Main source code organized by components (ast, smt, sat, etc.)
- `examples/` - Language binding examples (C, C++, Python, Java, .NET, etc.)
- `scripts/` - Build scripts and utilities
- `.github/workflows/` - CI/CD pipeline definitions
- `cmake/` - CMake configuration files

### Important Files
- `README.md` - Main documentation and build instructions
- `README-CMake.md` - Detailed CMake build documentation  
- `configure` - Wrapper script around `scripts/mk_make.py`
- `CMakeLists.txt` - Main CMake configuration
- `scripts/mk_make.py` - Python build system entry point

## Common Tasks and Validation

### Pre-commit Validation
Before committing changes:
1. **Build successfully**: Use one of the validated build commands above
2. **Run unit tests**: `./test-z3 /a` must pass
3. **Test basic functionality**: Run validation scenarios above
4. **Test affected language bindings**: If modifying API, test relevant examples

### Working with Language Bindings
- **Python**: Located in `build/python/`, test with validation scenario above
- **C/C++**: Examples in `examples/c/` and `examples/c++/`
  - Compile C++ example: `g++ -I src/api -I src/api/c++ examples/c++/example.cpp -L build -lz3 -o test_example`
  - Run with: `LD_LIBRARY_PATH=build ./test_example`
- **Java**: Build with `python scripts/mk_make.py --java`, examples in `examples/java/`
- **C#/.NET**: Build with `python scripts/mk_make.py --dotnet`, examples in `examples/dotnet/`

### Performance Testing
For performance-sensitive changes:
- Build optimized: `python scripts/mk_make.py` (Release mode by default)
- Test with realistic SMT problems from `examples/SMT-LIB2/`
- Use Z3's built-in statistics: `z3 -st problem.smt2`

## Common Issues and Solutions

### Build System Conflicts
- **Error**: CMake complains about polluted source tree
- **Solution**: Run `git clean -fx src/` to remove Python build artifacts

### Python Import Errors
- **Error**: `import z3` fails
- **Solution**: Ensure you're in `build/python/` directory or add it to `PYTHONPATH`

### Missing Dependencies
- **Error**: Compiler not found or version too old
- **Solution**: Z3 requires C++20. Install g++ 10+ or clang++ 10+

### Long Build Times
- **Normal**: 15-17 minute builds are expected for Z3
- **Never cancel**: Set timeouts appropriately and wait for completion
- **Optimization**: Use `make -j$(nproc)` for parallel compilation

## Key Projects in Codebase

Z3 is organized into several key components:

- **Core SMT**: `src/smt/` - Main SMT solver engine
- **SAT Solver**: `src/sat/` - Underlying boolean satisfiability solver  
- **Theories**: Various theory solvers (arithmetic, arrays, bit-vectors, etc.)
- **Abstract Syntax Trees**: `src/ast/` - Expression representation and manipulation
- **Tactics**: `src/tactic/` - Configurable solving strategies
- **API**: `src/api/` - Public C API and language bindings
- **Parsers**: SMT-LIB2, Dimacs, and other input format parsers
- **Model Generation**: Creating and manipulating satisfying assignments

The architecture is modular with clean separation between the core solver, theory plugins, and user interfaces.