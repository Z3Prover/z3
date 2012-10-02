using namespace System;
using namespace System::Reflection;
using namespace System::Runtime::CompilerServices;
using namespace System::Runtime::InteropServices;
using namespace System::Security::Permissions;

//
// General Information about an assembly is controlled through the following
// set of attributes. Change these attribute values to modify the information
// associated with an assembly.
//
[assembly:AssemblyTitleAttribute("Z3 .NET Interface")];
[assembly:AssemblyDescriptionAttribute(".NET Interface to the Z3 Theorem Prover")];
[assembly:AssemblyConfigurationAttribute("")];
[assembly:AssemblyCompanyAttribute("Microsoft Corporation")];
[assembly:AssemblyProductAttribute("Z3")];
[assembly:AssemblyCopyrightAttribute("Copyright (c) Microsoft Corporation 2006")];
[assembly:AssemblyTrademarkAttribute("")];
[assembly:AssemblyCultureAttribute("")];

[assembly:ComVisible(false)];
[assembly:CLSCompliantAttribute(true)];
[assembly:SecurityPermission(SecurityAction::RequestMinimum, UnmanagedCode = true)];

[assembly:AssemblyVersionAttribute("4.2.0.0")];
[assembly:AssemblyFileVersionAttribute("4.2.0.0")];

#ifdef DELAYSIGN
[assembly:AssemblyKeyFile("35MSSharedLib1024.snk")];
[assembly:AssemblyDelaySign(true)];
#else
[assembly:AssemblyKeyFile("z3.snk")];
[assembly:AssemblyDelaySign(true)];
#endif
