# Julia bindings

The Julia package [Z3.jl](https://github.com/ahumenberger/Z3.jl) provides and interface to Z3 by exposing its C++ API via [CxxWrap.jl](https://github.com/JuliaInterop/CxxWrap.jl). The bindings therefore consist of a [C++ part](z3jl.cpp) and a [Julia part](https://github.com/ahumenberger/Z3.jl). The C++ part defines the Z3 types/methods which are exposed. The resulting library is loaded in the Julia part via CxxWrap.jl which creates the corresponding Julia types/methods.

## Building the C++ part 

In order to build the Julia bindings the build option `Z3_BUILD_JULIA_BINDINGS` has to be enabled via CMake and [libcxxwrap-julia](https://github.com/JuliaInterop/libcxxwrap-julia) has to be present. Infos about obtaining the libcxxwrap prefix can be found [here](https://github.com/JuliaInterop/CxxWrap.jl#compiling-the-c-code).

```
mkdir build && cd build
cmake -DCMAKE_BUILD_TYPE=Release -DZ3_BUILD_JULIA_BINDINGS=True -DCMAKE_PREFIX_PATH=/path/to/libcxxwrap-julia-prefix ..
make
```

## Julia part

The Z3 binaries are provided to [Z3.jl](https://github.com/ahumenberger/Z3.jl) via [z3_jll.jl](https://github.com/JuliaBinaryWrappers/z3_jll.jl). That is, in order to release a new Z3 version one has to update the corresponding [build script](https://github.com/JuliaPackaging/Yggdrasil/tree/master/Z/z3) which triggers a new version of z3_jll.jl.

### Using the compiled version of Z3

The binaries are managed via the JLL package z3_jll. To use your own binaries, you need to set up an overrides file, by default at `~/.julia/artifacts/Overrides.toml` with the following content:

```toml
[1bc4e1ec-7839-5212-8f2f-0d16b7bd09bc]
z3 = "/path/to/z3/build"
```
