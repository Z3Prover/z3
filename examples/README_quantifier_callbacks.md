# UserPropagator Quantifier Instantiation Callback Examples

This directory contains examples demonstrating the UserPropagator callback for quantifier instantiations feature added in Z3 version 4.15.3.

## Overview

The quantifier instantiation callback allows user propagators to intercept and control quantifier instantiations, providing fine-grained control over the solving process.

## Files

### Python Examples
- `examples/python/quantifier_instantiation_callback.py` - Comprehensive Python examples showing:
  - Basic instantiation control (limiting number of instantiations)
  - Advanced pattern-based filtering
  - Instantiation logging and analysis

### C++ Examples  
- `examples/c++/quantifier_instantiation_callback.cpp` - C++ API examples (requires compilation)

### C Examples
- `examples/c/quantifier_instantiation_callback.c` - C API examples (requires compilation)

### Unit Tests
- `src/test/test_quantifier_instantiation_callback.py` - Unit tests validating functionality

### Documentation
- `doc/quantifier_instantiation_callback.md` - Complete API documentation and usage guide

## Running the Examples

### Python Examples

```bash
cd build/python
PYTHONPATH=/path/to/z3/build/python python3 ../../examples/python/quantifier_instantiation_callback.py
```

Or from the Z3 build directory:
```bash
cd build/python
python3 ../../examples/python/quantifier_instantiation_callback.py
```

### C++ Examples

```bash
# Compile
g++ -I src/api -I src/api/c++ examples/c++/quantifier_instantiation_callback.cpp -L build -lz3 -o quantifier_callback_cpp

# Run
LD_LIBRARY_PATH=build ./quantifier_callback_cpp
```

### C Examples

```bash
# Compile  
gcc -I src/api examples/c/quantifier_instantiation_callback.c -L build -lz3 -o quantifier_callback_c

# Run
LD_LIBRARY_PATH=build ./quantifier_callback_c
```

### Unit Tests

```bash
cd z3-root-directory
PYTHONPATH=build/python python3 src/test/test_quantifier_instantiation_callback.py
```

## Expected Output

When running the Python examples, you should see output like:

```
============================================================
BASIC QUANTIFIER INSTANTIATION CONTROL EXAMPLE
============================================================
Checking satisfiability with instantiation control...
Instantiation #1:
  Quantifier: ForAll(x, f(x) >= 0)
  Instantiation: f(1) >= 0
  -> ALLOWED (#1)

Instantiation #2:
  Quantifier: ForAll(x, f(x) >= 0)
  Instantiation: f(2) >= 0
  -> ALLOWED (#2)

Instantiation #3:
  Quantifier: ForAll(x, f(x) >= 0)
  Instantiation: f(3) >= 0
  -> ALLOWED (#3)

Result: sat
Model: [c = 3, b = 2, a = 1, f = [else -> 0]]

Instantiation Statistics:
  Total attempts: 3
  Allowed: 3
  Blocked: 0
```

## Key Features Demonstrated

1. **Basic Control**: Limiting the number of quantifier instantiations
2. **Pattern Filtering**: Allowing only a certain number of instantiations per pattern
3. **Logging**: Recording all instantiation attempts for analysis
4. **Performance Impact**: Showing how filtering affects solving time
5. **Error Handling**: Graceful handling of callback exceptions

## Use Cases

- **Performance Optimization**: Reduce solving time by limiting expensive instantiations
- **Custom Strategies**: Implement domain-specific instantiation heuristics  
- **Debugging**: Understand solver behavior through instantiation analysis
- **Interactive Solving**: Dynamically control solving process

## Requirements

- Z3 version 4.15.3 or later
- Python 3.x for Python examples
- GCC/Clang for C/C++ examples
- Z3 shared library in LD_LIBRARY_PATH

## Troubleshooting

### "ModuleNotFoundError: No module named 'z3'"
Set PYTHONPATH to point to the Z3 Python bindings:
```bash
export PYTHONPATH=/path/to/z3/build/python:$PYTHONPATH
```

### "No instantiations were attempted"
- Check that your formula contains quantifiers
- Verify that the constraints actually trigger instantiation (e.g., through function applications)
- Try disabling other Z3 optimizations that might eliminate the need for instantiation

### C/C++ Compilation Errors
- Ensure Z3 headers are in the include path (`-I /path/to/z3/src/api`)
- Link against the Z3 library (`-L /path/to/z3/build -lz3`)
- Set LD_LIBRARY_PATH to find the shared library at runtime

### Performance Issues
- Keep callback logic simple and fast
- Avoid expensive string operations in callbacks
- Consider sampling (only process every Nth callback) for high-frequency instantiations

## Further Reading

- See `doc/quantifier_instantiation_callback.md` for complete API documentation
- Z3 Guide: https://microsoft.github.io/z3guide/
- Z3 API Reference: https://z3prover.github.io/api/html/

## Contributing

To add new examples or improve existing ones:
1. Follow the existing code style and structure
2. Add appropriate error handling and documentation
3. Include unit tests for new functionality
4. Update this README with any new examples