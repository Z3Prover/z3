# Z3 Go Examples

This directory contains examples demonstrating how to use the Z3 Go bindings.

## Examples

### basic_example.go

Demonstrates fundamental Z3 operations:
- Creating contexts and solvers
- Defining integer and boolean variables
- Adding constraints
- Checking satisfiability
- Extracting models

## Building and Running

### Prerequisites

1. Build Z3 with Go bindings enabled
2. Ensure Z3 library is in your library path
3. Go 1.20 or later

### Linux/macOS

```bash
# Build Z3 first
cd ../..
mkdir build && cd build
cmake ..
make -j$(nproc)

# Set up environment
cd ../examples/go
export LD_LIBRARY_PATH=../../build:$LD_LIBRARY_PATH
export CGO_CFLAGS="-I../../src/api"
export CGO_LDFLAGS="-L../../build -lz3"

# Run examples
go run basic_example.go
```

### Windows

```cmd
REM Build Z3 first
cd ..\..
mkdir build
cd build
cmake ..
cmake --build . --config Release

REM Set up environment
cd ..\examples\go
set PATH=..\..\build\Release;%PATH%
set CGO_CFLAGS=-I..\..\src\api
set CGO_LDFLAGS=-L..\..\build\Release -lz3

REM Run examples
go run basic_example.go
```

## Expected Output

When you run `basic_example.go`, you should see output similar to:

```
Z3 Go Bindings - Basic Example
================================

Example 1: Solving x > 0
Satisfiable!
Model: ...
x = 1

Example 2: Solving x + y = 10 ∧ x - y = 2
Satisfiable!
x = 6
y = 4

Example 3: Boolean satisfiability
Satisfiable!
p = false
q = true

Example 4: Checking unsatisfiability
Status: unsat
The constraints are unsatisfiable (as expected)

All examples completed successfully!
```

## Creating Your Own Examples

1. Import the Z3 package:
   ```go
   import "github.com/Z3Prover/z3/src/api/go"
   ```

2. Create a context:
   ```go
   ctx := z3.NewContext()
   ```

3. Create variables and constraints:
   ```go
   x := ctx.MkIntConst("x")
   constraint := ctx.MkGt(x, ctx.MkInt(0, ctx.MkIntSort()))
   ```

4. Solve:
   ```go
   solver := ctx.NewSolver()
   solver.Assert(constraint)
   if solver.Check() == z3.Satisfiable {
       model := solver.Model()
       // Use model...
   }
   ```

## Troubleshooting

### "undefined reference to Z3_*" errors

Make sure:
- Z3 is built and the library is in your library path
- CGO_LDFLAGS includes the correct library path
- On Windows, the DLL is in your PATH

### "cannot find package" errors

Make sure:
- CGO_CFLAGS includes the Z3 API header directory
- The go.mod file exists in src/api/go

### CGO compilation errors

Ensure:
- CGO is enabled (set CGO_ENABLED=1 if needed)
- You have a C compiler installed (gcc, clang, or MSVC)
- The Z3 headers are accessible

## More Information

See the README.md in src/api/go for complete API documentation.
