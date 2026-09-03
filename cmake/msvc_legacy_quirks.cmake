# This file ether sets or notes various compiler and linker flags for MSVC that
# were defined by the old python/Makefile based build system but
# don't obviously belong in the other sections in the CMake build system.

################################################################################
# Compiler definitions
################################################################################
# FIXME: All the commented out defines should be removed once
# we are confident it is correct to not set them.
set(Z3_MSVC_LEGACY_DEFINES
  # Don't set `_DEBUG`. The old build system sets this but this
  # is wrong. MSVC will set this depending on which runtime is being used.
  # See https://msdn.microsoft.com/en-us/library/b0084kay.aspx
  # _DEBUG

  # The old build system only set `UNICODE` and `_UNICODE` for x86_64 release.
  # That seems completely wrong so set it for all configurations.
  # According to https://blogs.msdn.microsoft.com/oldnewthing/20040212-00/?p=40643/
  # `UNICODE` affects Windows headers and `_UNICODE` affects C runtime header files.
  # There is some discussion of this define at https://msdn.microsoft.com/en-us/library/dybsewaf.aspx
  UNICODE
  _UNICODE
)

if (TARGET_ARCHITECTURE STREQUAL "x86_64")
  list(APPEND Z3_MSVC_LEGACY_DEFINES ""
    # Don't set `_LIB`. The old build system sets this for x86_64 release
    # build. This flag doesn't seem to be documented but a stackoverflow
    # post hints that this is usually set when building a static library.
    # See http://stackoverflow.com/questions/35034683/how-to-tell-if-current-project-is-dll-or-static-lib
    # This seems wrong give that the old build system set this regardless
    # whether or not libz3 was static or shared so its probably best
    # to not set for now.
    #$<$<CONFIG:Release>:_LIB>
    #$<$<CONFIG:RelWithDebInfo>:_LIB>

    # Don't set `_CONSOLE`. The old build system sets for all configurations
    # except x86_64 release. It seems ( https://codeyarns.com/2010/12/02/visual-c-windows-and-console-subsystems/ )
    # that `_CONSOLE` used to be defined by older Visual C++ environments.
    # Setting this undocumented option seems like a bad idea so let's not do it.
    #$<$<CONFIG:Debug:_CONSOLE>
    #$<$<CONFIG:MinSizeRel:_CONSOLE>

    # Don't set `ASYNC_COMMANDS`. The old build system sets this for x86_64
    # release but this macro does not appear to be used anywhere and is not
    # documented so don't set it for now.
    #$<$<CONFIG:Release>:ASYNC_COMMANDS>
    #$<$<CONFIG:RelWithDebInfo>:ASYNC_COMMANDS>
  )
else()
  list(APPEND Z3_MSVC_LEGACY_DEFINES ""
    # Don't set `_CONSOLE`. See reasoning above.
    #_CONSOLE
  )
endif()

# Note we don't set WIN32 or _WINDOWS because
# CMake provides that for us. As a sanity check make sure the option
# is present.
if (NOT CMAKE_CXX_FLAGS MATCHES "[-/]D[ ]*WIN32")
  message(FATAL_ERROR "\"/D WIN32\" is missing")
endif()
if (NOT CMAKE_CXX_FLAGS MATCHES "[-/]D[ ]*_WINDOWS")
  message(FATAL_ERROR "\"/D _WINDOWS\" is missing")
endif()

target_compile_definitions(z3_internal_options INTERFACE
  ${Z3_MSVC_LEGACY_DEFINES})

################################################################################
# Compiler flags
################################################################################
# FIXME: We might want to move this out somewhere else if we decide
# we want to set `-fno-omit-frame-pointer` for gcc/clang.
# No omit frame pointer
set(NO_OMIT_FRAME_POINTER_MSVC_FLAG "/Oy-")
CHECK_CXX_COMPILER_FLAG(${NO_OMIT_FRAME_POINTER_MSVC_FLAG} HAS_MSVC_NO_OMIT_FRAME_POINTER)
if (NOT HAS_MSVC_NO_OMIT_FRAME_POINTER)
  message(FATAL_ERROR "${NO_OMIT_FRAME_POINTER_MSVC_FLAG} flag not supported")
endif()

# FIXME: This doesn't make a huge amount of sense but the old
# build system kept the frame pointer for all configurations
# except x86_64 release (I don't know why the frame pointer
# is kept for i686 release).
if (TARGET_ARCHITECTURE STREQUAL "x86_64")
  target_compile_options(z3_internal_options INTERFACE
    $<$<CONFIG:Debug>:${NO_OMIT_FRAME_POINTER_MSVC_FLAG}>
    $<$<CONFIG:MinSizeRel>:${NO_OMIT_FRAME_POINTER_MSVC_FLAG}>
  )
else()
  target_compile_options(z3_internal_options INTERFACE
    ${NO_OMIT_FRAME_POINTER_MSVC_FLAG})
endif()

if ((TARGET_ARCHITECTURE STREQUAL "x86_64") OR (TARGET_ARCHITECTURE STREQUAL "i686"))
  # Use __cdecl calling convention. Apparently this is MSVC's default
  # but the old build system set it so for completeness set it too.
  # See https://msdn.microsoft.com/en-us/library/46t77ak2.aspx
  z3_add_cxx_flag("/Gd" REQUIRED)
endif()

z3_add_cxx_flag("/EHsc" REQUIRED)

################################################################################
# Linker flags
################################################################################

set(_z3_link_executable
  "$<STREQUAL:$<TARGET_PROPERTY:TYPE>,EXECUTABLE>")
set(_z3_link_shared
  "$<STREQUAL:$<TARGET_PROPERTY:TYPE>,SHARED_LIBRARY>")
set(_z3_link_binary "$<OR:${_z3_link_executable},${_z3_link_shared}>")

# The old build disables incremental linking for executables and DLLs.
target_link_options(z3_internal_options INTERFACE
  "$<${_z3_link_binary}:/INCREMENTAL:NO>")

# The original build system passes `/STACK:` to the linker.
# This size comes from the original build system.
# FIXME: What is the rationale behind this?
set(STACK_SIZE_MSVC_LINKER 8388608)
# MSVC documentation (https://msdn.microsoft.com/en-us/library/35yc2tc3.aspx)
# says this only matters for executables which is why this is not being
# set for CMAKE_SHARED_LINKER_FLAGS or CMAKE_STATIC_LINKER_FLAGS.
target_link_options(z3_internal_options INTERFACE
  "$<${_z3_link_executable}:/STACK:${STACK_SIZE_MSVC_LINKER}>")

# The original build system passes `/SUBSYSTEM:<X>` to the linker where `<X>`
# depends on what is being linked. Where `<X>` is `CONSOLE` for executables
# and `WINDOWS` for shard libraries.
# We don't need to pass `/SUBSYSTEM:CONSOLE` because CMake will do this for
# us when building executables because we don't pass the `WIN32` argument to
# `add_executable()`.
# FIXME: We probably don't need this. https://msdn.microsoft.com/en-us/library/fcc1zstk.aspx
# suggests that `/SUBSYSTEM:` only matters for executables.
target_link_options(z3_internal_options INTERFACE
  "$<${_z3_link_shared}:/SUBSYSTEM:WINDOWS>")

# FIXME: The following linker flags are weird. They are set in all configurations
# in the old build system except release x86_64. We try to emulate this here but
# this is likely the wrong thing to do.
string(TOUPPER "${available_build_types}" _build_types_as_upper)
foreach (_build_type IN LISTS _build_types_as_upper)
  if (TARGET_ARCHITECTURE STREQUAL "x86_64" AND
      (_build_type STREQUAL "RELEASE" OR
      _build_type  STREQUAL "RELWITHDEBINFO")
      )
    message(AUTHOR_WARNING "Skipping legacy linker MSVC options for x86_64 ${_build_type}")
  else()
    # Linker optimizations.
    # See https://msdn.microsoft.com/en-us/library/bxwfs976.aspx
    target_link_options(z3_internal_options INTERFACE
      "$<$<AND:${_z3_link_binary},$<CONFIG:${_build_type}>>:/OPT:REF>"
      "$<$<AND:${_z3_link_binary},$<CONFIG:${_build_type}>>:/OPT:ICF>")

    # FIXME: This is not necessary. This is MSVC's default.
    # See https://msdn.microsoft.com/en-us/library/b1kw34cb.aspx
    target_link_options(z3_internal_options INTERFACE
      "$<$<AND:${_z3_link_binary},$<CONFIG:${_build_type}>>:/TLBID:1>")

    # FIXME: This is not necessary. This is MSVC's default.
    # Indicate that the executable is compatible with DEP
    # See https://msdn.microsoft.com/en-us/library/ms235442.aspx
    target_link_options(z3_internal_options INTERFACE
      "$<$<AND:${_z3_link_executable},$<CONFIG:${_build_type}>>:/NXCOMPAT>")

  endif()
endforeach()
