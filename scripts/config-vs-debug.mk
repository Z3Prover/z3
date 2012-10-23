CXX=cl
CXXFLAGS=/c /ZI /nologo /W3 /WX- /Od /Oy- /D "WIN32" /D "_DEBUG" /D "Z3DEBUG" /D "_CONSOLE" /D "_TRACE" /D "_WINDOWS" /Gm /EHsc /RTC1 /MDd /GS /fp:precise /Zc:wchar_t /Zc:forScope /openmp /Gd /analyze- 
CXX_OUT_FLAG=/Fo
OBJ_EXT=.obj
LIB_EXT=.lib
AR=lib
AR_FLAGS=/nologo
AR_OUTFLAG=/OUT:
EXE_EXT=.exe
LINK=cl
LINK_FLAGS=/nologo "$(VSINSTALLDIR)VC\Lib\libcpmt.lib" "$(WindowsSdkDir)Lib\uuid.lib" "$(VSINSTALLDIR)VC\Lib\libcmt.lib" "$(VSINSTALLDIR)VC\Lib\oldnames.lib" "$(VSINSTALLDIR)VC\Lib\VCOMP.lib" "$(WindowsSdkDir)Lib\kernel32.lib"
LINK_EXTRA_FLAGS=/link /DEBUG /MACHINE:X86 /SUBSYSTEM:CONSOLE /INCREMENTAL:NO /STACK:"8388608" /OPT:REF /OPT:ICF /TLBID:1 /DYNAMICBASE /NXCOMPAT
LINK_OUT_FLAG=/Fe


