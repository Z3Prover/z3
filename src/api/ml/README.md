Summary
=======

The OCaml z3 bindings now work both in dynamic and static mode and the compiled
libraries can be used by all linkers in the OCaml system, without
any specific instructions other than specifying the dependency on
the z3 library.


Using the libraries
===================

Compiling binaries
------------------

The libraries can be linked statically with both ocamlc and ocamlopt
compilers, e.g.,

```
ocamlfind ocamlc -thread -package z3 -linkpkg run.ml -o run
```
or
```
ocamlfind ocamlopt -thread -package z3 -linkpkg run.ml -o run
```

When bindings compiled with the `--staticlib` the produced binary will
not have any dependencies on z3
```
$ ldd ./run
        linux-vdso.so.1 (0x00007fff9c9ed000)
        libstdc++.so.6 => /usr/lib/x86_64-linux-gnu/libstdc++.so.6 (0x00007fb56f09c000)
        libgmp.so.10 => /usr/lib/x86_64-linux-gnu/libgmp.so.10 (0x00007fb56ee1b000)
        libpthread.so.0 => /lib/x86_64-linux-gnu/libpthread.so.0 (0x00007fb56ebfc000)
        libm.so.6 => /lib/x86_64-linux-gnu/libm.so.6 (0x00007fb56e85e000)
        libdl.so.2 => /lib/x86_64-linux-gnu/libdl.so.2 (0x00007fb56e65a000)
        libgcc_s.so.1 => /lib/x86_64-linux-gnu/libgcc_s.so.1 (0x00007fb56e442000)
        libc.so.6 => /lib/x86_64-linux-gnu/libc.so.6 (0x00007fb56e051000)
        /lib64/ld-linux-x86-64.so.2 (0x00007fb570de9000)
```

The bytecode version will have a depedency on z3 and other external
libraries (packed as dlls and usually installed in opam switch):
```
$ ocamlobjinfo run | grep 'Used DLL' -A5
Used DLLs:
        dllz3ml
        dllzarith
        dllthreads
        dllunix
```

But it is possible to compile a portable self-contained version of the
bytecode executable using the `-custom` switch:

```
ocamlfind ocamlc -custom -thread -package z3 -linkpkg run.ml -o run
```

The build binary is now quite large but doesn't have any external
dependencies (modulo the system dependencies):
```
$ du -h run
27M     run
$ ocamlobjinfo run | grep 'Used DLL' | wc -l
0
$ ldd run
        linux-vdso.so.1 (0x00007ffee42c2000)
        libstdc++.so.6 => /usr/lib/x86_64-linux-gnu/libstdc++.so.6 (0x00007fdbdc415000)
        libgmp.so.10 => /usr/lib/x86_64-linux-gnu/libgmp.so.10 (0x00007fdbdc194000)
        libpthread.so.0 => /lib/x86_64-linux-gnu/libpthread.so.0 (0x00007fdbdbf75000)
        libm.so.6 => /lib/x86_64-linux-gnu/libm.so.6 (0x00007fdbdbbd7000)
        libdl.so.2 => /lib/x86_64-linux-gnu/libdl.so.2 (0x00007fdbdb9d3000)
        libgcc_s.so.1 => /lib/x86_64-linux-gnu/libgcc_s.so.1 (0x00007fdbdb7bb000)
        libc.so.6 => /lib/x86_64-linux-gnu/libc.so.6 (0x00007fdbdb3ca000)
        /lib64/ld-linux-x86-64.so.2 (0x00007fdbde026000)
```

Loading in toplevel
-------------------

It is also possible to use the built libraries in toplevel and use
them in ocaml scripts, e.g.,
```
$ ocaml
        OCaml version 4.09.0

 # #use "topfind";;
 - : unit = ()
 Findlib has been successfully loaded. Additional directives:
  #require "package";;      to load a package
  #list;;                   to list the available packages
  #camlp4o;;                to load camlp4 (standard syntax)
  #camlp4r;;                to load camlp4 (revised syntax)
  #predicates "p,q,...";;   to set these predicates
  Topfind.reset();;         to force that packages will be reloaded
  #thread;;                 to enable threads

- : unit = ()
 # #require "z3";;
 /home/ivg/.opam/4.09.0/lib/zarith: added to search path
 /home/ivg/.opam/4.09.0/lib/zarith/zarith.cma: loaded
 /home/ivg/.opam/4.09.0/lib/z3: added to search path
 /home/ivg/.opam/4.09.0/lib/z3/z3ml.cma: loaded
 #
```

To use z3 in a script mode add the following preamble to a file with
OCaml code:
```
  #!/usr/bin/env ocaml
  #use "topfind";;
  #require "z3";;

  (* your OCaml code *)
```

Then it is possible to run it as `./script` (provided that the code is
in a file named `script` and permissions are set with `chmod a+x
script`).

Of course, such scripts will depend on ocaml installation that shall
have z3 dependencies installed.

Using Dynlink
-------------

The built z3ml.cmxs file is a self-contained shared library that
doesn't have any depndencies on z3 (the z3 code is included in it) and
could be loaded with `Dynlink.loadfile` in runtime.

Installation
============

I did not touch the installation part in this PR, as I was using opam
and installed artifacts as simple as:
```
ocamlfind install z3 build/api/ml/* build/libz3-static.a
```

assuming that the following configuration and building process
```
python2.7 scripts/mk_make.py --ml --staticlib
make -C build
```

Though the default installation script in the make file shall work.

Dynamic Library mode
====================

The dynamic library mode is also supported provided that libz3.so is
installed in a search path of the dynamic loader (or the location is
added via the LD_LIBRARY_PATH) or stored in rpaths of the built
binary.

Build Artifacts
===============

In the static mode (--staticlib), the following files are built and
installed:

- `{z3,z3enums,z3native}.{cmi,cmo,cmx,o,mli}`: the three compilation
units (modules) that comprise Z3 bindings. The `*.mli` files are not
necessary but are installed for the user convenience and documentation
purposes. The *.cmi files enables access to the unit
definitions. Finally, `*.cmo` contain the bytecode and `*.cmx, *.o`
contain the native code. Files with the code are necessary for cross-module
optimization but are not strictly needed as the code is also
duplicated in the libraries.

- libz3-static.a (OR libz3.so if built not in the staticlib mode)
contains the machine code of the Z3 library;

- z3ml.{a,cma,cmxa,cmxs} - the OCaml code for the bindings. File
z3ml.a and z3ml.cmxa are static libraries with OCaml native code,
which will be included in the final binary when ocamlopt is used. The
z3 library code itself is not included in those three artifacts, but
the instructions where to find it are. The same is truce for `z3ml.a`
which includes the bytecode of the bindings as well as instructions
how to link the final product. Finally, `z3ml.cmxs` is a standalone
shared library that could be loaded in runtime use
`Dynlink.loadfile` (which used dlopen on posix machines underneath the
hood).

- libz3ml.a is the archived machine code for `z3native_stubs.c`, which
is made by ocamlmklib: `ar rcs api/ml/libz3ml.a
api/ml/z3native_stubs.o` it is needed to build statically linked
binaries and libraries that use z3 bindings.

- dllz3ml.so is the shared object that contains `z3native_stubs.o` as
well as correct ldd entries for C++ and Z3 libraries to enable proper
static and dynamic linking. The file is built with ocamlmklib on posix
systems as
```
gcc -shared -o api/ml/dllz3ml.so api/ml/z3native_stubs.o -L. -lz3-static -lstdc++
```

It is used by `ocaml`, `ocamlrun`, and `ocamlc` to link z3 and c++
code into the OCaml runtime and enables usage of z3 bindings in
non-custom runtimes (default runtimes).

The `dllz3ml.so` is usually installed in the stubs library in opam
installation (`$(opam config var lib)/stublibs`), it is done
automatically by `ocamlfind` so no special treatment is needed.

Technical Details
=================

The patch itself is rather small. First of all, we have to use
`-l<lib>` instead of `-cclib -l<lib>` in ocamlmklib since the latter
will pass the options only to the ocaml{c,opt} linker and will not
use the passed libraries when shared and non-shared versions of the
bindings are built (libz3ml.a and dllz3ml.so). They were both missing
either z3 code itself and ldd entries for stdc++ (and z3 if built not
in --staticlib mode).

Having stdc++ entry streamlines the compilation process and makes
dynamic loading more resistant to the inclusion order.

Finally, we had to add `-L.` to make sure that the built artifacts are
correctly found by gcc.

I specifically left the cygwin part of the code intact as I have no
idea what the original author meant by this, neither do I use or
tested this patch in the cygwin or mingw environemt. I think that this
code is rather outdated and shouldn't really work. E.g., in the
--staticlib mode adding z3linkdep (which is libz3-static.a) as an
argument to `ocamlmklib` will yield the following broken archive
```
ar rcs api/ml/libz3ml.a libz3-static.a api/ml/z3native_stubs.o
```
and it is not allowed (or supported) to have .a in archives (though it
doesn't really hurt as most of the systems will just ignore it).

But otherwise, cygwin, mingw shall behave as they did (the only change
that affects them is `-L.` which I believe should be benign).

[1]: https://stackoverflow.com/questions/56839246/installing-ocaml-api-for-z3-using-opam/58398704
[2]: https://stackoverflow.com/questions/57065191/linker-error-when-installing-z3-ocaml-bindings-in-local-opam-environment
[3]: https://discuss.ocaml.org/t/trouble-with-z3-on-ocaml-4-10-on-linux-and-ocaml-4-x-on-macos/5418/9
[4]: https://github.com/ocaml/opam-repository/blob/master/packages/z3/z3.4.8.8/opam
[5]: https://github.com/akabe/ocaml-jupyter

Other notes
==============
On Windows, there are no less than four different ports of OCaml. The Z3 build 
system assumes that either the win32 or the win64 port is installed. This means
that OCaml will use `cl' as the underlying C compiler and not the cygwin or
mingw compilers.

OCamlfind: When ocamlfind is found, the `install' target will install the Z3
OCaml bindings into the ocamlfind site-lib directory. The installed package is
linked against the (dynamic) libz3 and it adds $(PREFIX)/lib to the library
include paths. On Windows, there is no $(PREFIX), so the build directory is
used instead (see META.in).

