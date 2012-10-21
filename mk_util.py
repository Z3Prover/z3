############################################
# Copyright (c) 2012 Microsoft Corporation
# 
# Auxiliary scripts for generate Makefiles and Visual 
# Studio project files.
#
# Author: Leonardo de Moura (leonardo)
############################################
import os
import glob

BUILD_DIR='build'
SRC_DIR='src'
MODES=[]
PLATFORMS=[]

def set_build_dir(d):
    global BUILD_DIR
    BUILD_DIR = d
    mk_dir(BUILD_DIR)

def set_src_dir(d):
    global SRC_DIR
    SRC_DIR = d

def set_modes(l):
    global MODES
    MODES=l

def set_platforms(l):
    global PLATFORMS
    PLATFORMS=l

VS_COMMON_OPTIONS='WIN32'
VS_DBG_OPTIONS='_DEBUG'
VS_RELEASE_OPTIONS='NDEBUG'

HEADERS = []
LIBS = []
LIB_DEPS = {}

class MKException(Exception):
    def __init__(self, value):
        self.value = value
    def __str__(self):
        return repr(self.value)

def set_vs_options(common, dbg, release):
    global VS_COMMON_OPTIONS, VS_DBG_OPTIONS, VS_RELEASE_OPTIONS
    VS_COMMON_OPTIONS = common
    VS_DBG_OPTIONS = dbg
    VS_RELEASE_OPTIONS = release

def is_debug(mode):
    return mode == 'Debug'

def is_x64(platform):
    return platform == 'x64'

def mk_dir(d):
    if not os.path.exists(d):
        os.makedirs(d)

def module_src_dir(name):
    return '%s%s%s' % (SRC_DIR, os.sep, name)

def module_build_dir(name):
    return '%s%s%s' % (BUILD_DIR, os.sep, name)

def vs_header(f):
    f.write(
'<?xml version="1.0" encoding="utf-8"?>\n'
'<Project DefaultTargets="Build" ToolsVersion="4.0" xmlns="http://schemas.microsoft.com/developer/msbuild/2003">\n')

GUI = 0
Name2GUI = {}

def vs_project_configurations(f, name):
    global GUI, Name2GUI
    f.write('  <ItemGroup Label="ProjectConfigurations">\n')
    for mode in MODES:
        for platform in PLATFORMS:
            f.write('    <ProjectConfiguration Include="%s|%s">\n' % (mode, platform))
            f.write('      <Configuration>%s</Configuration>\n' % mode)
            f.write('      <Platform>%s</Platform>\n' % platform)
            f.write('    </ProjectConfiguration>\n')
    f.write('  </ItemGroup>\n')

    f.write('   <PropertyGroup Label="Globals">\n')
    f.write('    <ProjectGuid>{00000000-0000-0000-000--%s}</ProjectGuid>\n' % GUI)
    f.write('    <ProjectName>%s</ProjectName>\n' % name)
    f.write('    <Keyword>Win32Proj</Keyword>\n')
    f.write('  </PropertyGroup>\n')
    f.write('  <Import Project="$(VCTargetsPath)\Microsoft.Cpp.Default.props" />\n')
    Name2GUI[name] = GUI
    GUI = GUI + 1

def vs_lib_configurations(f, name):
    for mode in MODES:
        for platform in PLATFORMS:
            f.write('  <PropertyGroup Condition="\'$(Configuration)|$(Platform)\'==\'%s|%s\'" Label="Configuration">\n' % (mode, platform))
            f.write('    <ConfigurationType>StaticLibrary</ConfigurationType>\n')
            f.write('    <CharacterSet>Unicode</CharacterSet>\n')
            f.write('    <UseOfMfc>false</UseOfMfc>\n')
            f.write('  </PropertyGroup>\n')

    f.write('  <Import Project="$(VCTargetsPath)\Microsoft.Cpp.props" />\n')
    f.write('  <ImportGroup Label="ExtensionSettings">\n')
    f.write('   </ImportGroup>\n')
    f.write('   <ImportGroup Label="PropertySheets">\n')
    f.write('    <Import Project="$(UserRootDir)\Microsoft.Cpp.$(Platform).user.props" Condition="exists(\'$(UserRootDir)\Microsoft.Cpp.$(Platform).user.props\')" Label="LocalAppDataPlatform" />  </ImportGroup>\n')
    f.write('  <PropertyGroup Label="UserMacros" />\n')

    f.write('  <PropertyGroup>\n')
    for mode in MODES:
        for platform in PLATFORMS:
            if is_x64(platform):
                f.write('    <OutDir Condition="\'$(Configuration)|$(Platform)\'==\'%s|%s\'">$(SolutionDir)$(Platform)\$(Configuration)\</OutDir>\n' % 
                        (mode, platform))
            else:
                f.write('    <OutDir Condition="\'$(Configuration)|$(Platform)\'==\'%s|%s\'">$(SolutionDir)$(Configuration)\</OutDir>\n' % (mode, platform))
    for mode in MODES:
        for platform in PLATFORMS:
            f.write('    <TargetName Condition="\'$(Configuration)|$(Platform)\'==\'%s|%s\'">%s</TargetName>\n' % (mode, platform, name))
            f.write('    <TargetExt Condition="\'$(Configuration)|$(Platform)\'==\'%s|%s\'">.lib</TargetExt>\n' % (mode, platform))
    f.write('  </PropertyGroup>\n')

def vs_compilation_options(f, name, deps):
    for mode in MODES:
        for platform in PLATFORMS:
            f.write('  <ItemDefinitionGroup Condition="\'$(Configuration)|$(Platform)\'==\'%s|%s\'">\n' % (mode, platform))
            if is_x64(platform):
                f.write('    <Midl>\n')
                f.write('      <TargetEnvironment>X64</TargetEnvironment>\n')
                f.write('    </Midl>\n')
            f.write('    <ClCompile>\n')
            if is_debug(mode):
                f.write('      <Optimization>Disabled</Optimization>\n')
            else:
                f.write('      <Optimization>Full</Optimization>\n')
            options = VS_COMMON_OPTIONS
            if is_debug(mode):
                options = "%s;%s" % (options, VS_DBG_OPTIONS)
            else:
                options = "%s;%s" % (options, VS_RELEASE_OPTIONS)
            if is_x64(platform):
                options = "%s;_AMD64_" % options
            f.write('      <PreprocessorDefinitions>%s;%%(PreprocessorDefinitions)</PreprocessorDefinitions>\n' % options)
            if is_debug(mode):
                f.write('      <MinimalRebuild>true</MinimalRebuild>\n')
                f.write('      <BasicRuntimeChecks>EnableFastChecks</BasicRuntimeChecks>\n')
                f.write('      <WarningLevel>Level3</WarningLevel>\n')
            f.write('      <RuntimeLibrary>MultiThreadedDebugDLL</RuntimeLibrary>\n')
            f.write('      <OpenMPSupport>true</OpenMPSupport>\n')
            f.write('      <DebugInformationFormat>ProgramDatabase</DebugInformationFormat>\n')
            f.write('      <AdditionalIncludeDirectories>')
            f.write('..\..\src\%s' % name)
            for dep in deps:
                f.write(';..\..\src\%s' % dep)
            f.write('</AdditionalIncludeDirectories>\n')
            f.write('    </ClCompile>\n')
            f.write('    <Link>\n')
            f.write('      <OutputFile>$(OutDir)%s.lib</OutputFile>\n' % name)
            f.write('      <AdditionalLibraryDirectories>%(AdditionalLibraryDirectories)</AdditionalLibraryDirectories>\n')
            if is_x64(platform):
                f.write('      <TargetMachine>MachineX64</TargetMachine>\n')
            else:
                f.write('      <TargetMachine>MachineX86</TargetMachine>\n')
            f.write('    </Link>\n')
            f.write('  </ItemDefinitionGroup>\n')

def add_vs_cpps(f, name):
    f.write('  <ItemGroup>\n')
    srcs = module_src_dir(name)
    for cppfile in glob.glob(os.path.join(srcs, '*.cpp')):
       f.write('    <ClCompile Include="..%s..%s%s" />\n' % (os.sep, os.sep, cppfile))
    f.write('  </ItemGroup>\n')

def vs_footer(f):
    f.write(
'  <Import Project="$(VCTargetsPath)\Microsoft.Cpp.targets" />\n'
'  <ImportGroup Label="ExtensionTargets">\n'
'  </ImportGroup>\n'
'</Project>\n')

def check_new_component(name):
    if (name in HEADERS) or (name in LIBS):
        raise MKException("Component '%s' was already defined" % name)

# Add a directory containing only .h files
def add_header(name):
    check_new_component(name)
    HEADERS.append(name)

def find_all_deps(name, deps):
    new_deps = []
    for dep in deps:
        if dep in LIBS:
            if not (dep in new_deps):
                new_deps.append(dep)
            for dep_dep in LIB_DEPS[dep]:
                if not (dep_dep in new_deps):
                    new_deps.append(dep_dep)
        elif dep in HEADERS:
            if not (dep in new_deps):
                new_deps.append(dep)
        else:
            raise MKException("Unknown component '%s' at '%s'." % (dep, name))
    return new_deps

def add_lib(name, deps):
    check_new_component(name)
    LIBS.append(name)
    deps = find_all_deps(name, deps)
    LIB_DEPS[name] = deps
    print "Dependencies for '%s': %s" % (name, deps)

    module_dir = module_build_dir(name)
    mk_dir(module_dir)

    vs_proj = open('%s%s%s.vcxproj' % (module_dir, os.sep, name), 'w')
    vs_header(vs_proj)
    vs_project_configurations(vs_proj, name)
    vs_lib_configurations(vs_proj, name)
    vs_compilation_options(vs_proj, name, deps)
    add_vs_cpps(vs_proj, name)
    vs_footer(vs_proj)

