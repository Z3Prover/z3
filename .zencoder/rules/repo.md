---
description: Repository Information Overview
alwaysApply: true
---

# Z3 Theorem Prover Information

## Summary
Z3 is a theorem prover from Microsoft Research, licensed under the MIT license. It's a high-performance SMT (Satisfiability Modulo Theories) solver that can check the satisfiability of logical formulas over one or more theories.

## Structure
- **src/**: Core source code organized by components (ast, smt, sat, etc.)
- **examples/**: Language binding examples (C, C++, Python, Java, .NET, etc.)
- **scripts/**: Build scripts and utilities
- **cmake/**: CMake configuration files
- **docker/**: Docker configuration files
- **test/**: Unit tests and testing infrastructure

## Language & Runtime
**Language**: C++
**Version**: C++20
**Build Systems**: 
- Python build system (scripts/mk_make.py)
- CMake build system
- Bazel build system

**Package Manager**: None (self-contained)

## Dependencies
**Main Dependencies**:
- Python 3.x (required for build)
- C++20 capable compiler (g++ or clang++)
- GNU Make
- Git (for version information)

**Optional Dependencies**:
- GMP (optional for multi-precision integers)
- Various language runtimes for bindings (Java, .NET, OCaml, etc.)

## Build & Installation
**Python Build System**:
```bash
python scripts/mk_make.py
cd build && make -j$(nproc)
```

**CMake Build System**:
```bash
mkdir build && cd build
cmake ..
make -j$(nproc)
```

**Bazel Build System**:
```bash
bazel build //...
```

## Docker
**Dockerfile**: docker/ubuntu-20-04.Dockerfile
**Base Image**: ubuntu:20.04
**Build Command**:
```bash
docker build -f docker/ubuntu-20-04.Dockerfile -t z3:latest .
```

## Testing
**Framework**: Custom test framework
**Test Location**: src/test/
**Run Command**:
```bash
cd build
make test
./test-z3 /a
```

## Language Bindings
Z3 provides bindings for multiple programming languages:

**C/C++**: Native API (always enabled)
```bash
# Build with C++ examples
g++ -I src/api -I src/api/c++ examples/c++/example.cpp -L build -lz3 -o example
```

**Python**:
```bash
# Enable Python bindings
python scripts/mk_make.py --python
cd build && make
```

**Java**:
```bash
# Enable Java bindings
python scripts/mk_make.py --java
cd build && make
```

**.NET**:
```bash
# Enable .NET bindings
python scripts/mk_make.py --dotnet
cd build && make
```

**OCaml**:
```bash
# Enable OCaml bindings
python scripts/mk_make.py --ml
cd build && make
```

## Version Information
**Current Version**: 4.15.4.0
**Version File**: scripts/VERSION.txt