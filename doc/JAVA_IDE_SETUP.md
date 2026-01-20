# Z3 Java Bindings: IDE Setup Guide

This guide explains how to set up and use Z3 Java bindings in popular Java IDEs (Eclipse, IntelliJ IDEA, and Visual Studio Code).

## Prerequisites

Before setting up Z3 in your IDE, you need to obtain the Z3 binaries:

### Option 1: Download Pre-built Binaries (Recommended)

1. Download the appropriate Z3 release for your platform from the [Z3 Releases page](https://github.com/Z3Prover/z3/releases)
   - For Windows: `z3-x.x.x-x64-win.zip`
   - For Linux: `z3-x.x.x-x64-glibc-x.x.zip`
   - For macOS: `z3-x.x.x-x64-osx-x.x.zip`

2. Extract the archive to a location on your system (e.g., `C:\z3` on Windows or `/opt/z3` on Linux/macOS)

3. The extracted folder contains:
   - `bin/com.microsoft.z3.jar` - The Java API library
   - `bin/libz3.dll` (Windows) / `bin/libz3.so` (Linux) / `bin/libz3.dylib` (macOS) - The native Z3 library
   - `bin/libz3java.dll` (Windows) / `bin/libz3java.so` (Linux) / `bin/libz3java.dylib` (macOS) - The Java JNI bridge

### Option 2: Build from Source

If you need to build Z3 from source with Java bindings enabled:

```bash
python scripts/mk_make.py --java
cd build
make
```

The resulting files will be in the `build` directory.

## Eclipse Setup

### Step 1: Add Z3 JAR to Build Path

1. Right-click on your Java project in the **Package Explorer**
2. Select **Build Path** → **Configure Build Path...**
3. In the **Libraries** tab, click **Add External JARs...**
4. Navigate to the Z3 `bin` folder and select `com.microsoft.z3.jar`
5. Click **Apply and Close**

### Step 2: Configure Native Library Path

Eclipse needs to know where to find the native Z3 libraries (`.dll`, `.so`, or `.dylib` files).

**Method 1: Using Eclipse Native Library Location (Recommended)**

1. In the **Package Explorer**, expand the **Referenced Libraries** section
2. Find and expand `com.microsoft.z3.jar`
3. Right-click on **Native Library Location** and select **Edit...**
4. Click **External Folder...** and select the Z3 `bin` folder (where the native libraries are located)
5. Click **OK**

**Method 2: Using VM Arguments**

1. Right-click on your project → **Run As** → **Run Configurations...**
2. Select your Java application configuration (or create a new one)
3. Go to the **Arguments** tab
4. In the **VM arguments** field, add:
   ```
   -Djava.library.path=C:\path\to\z3\bin
   ```
   (Replace with your actual Z3 bin directory path)
5. Click **Apply** and **Run**

**Method 3: Using System PATH (Windows)**

1. Add the Z3 `bin` directory to your system PATH environment variable:
   - Open **System Properties** → **Advanced** → **Environment Variables**
   - Under **System Variables**, find and edit the `Path` variable
   - Add the full path to your Z3 `bin` directory (e.g., `C:\z3\bin`)
   - Click **OK** and restart Eclipse

### Step 3: Verify Setup

Create a test Java file with the following code:

```java
import com.microsoft.z3.*;

public class Z3Test {
    public static void main(String[] args) {
        System.out.println("Creating Z3 context...");
        Context ctx = new Context();
        System.out.println("Z3 version: " + Version.getFullVersion());
        
        // Simple example: x > 0
        IntExpr x = ctx.mkIntConst("x");
        Solver solver = ctx.mkSolver();
        solver.add(ctx.mkGt(x, ctx.mkInt(0)));
        
        if (solver.check() == Status.SATISFIABLE) {
            System.out.println("SAT");
            System.out.println("Model: " + solver.getModel());
        }
        
        ctx.close();
        System.out.println("Success!");
    }
}
```

Run the program. If you see the Z3 version and "Success!" printed, your setup is working correctly.

## IntelliJ IDEA Setup

### Step 1: Add Z3 JAR to Project

1. Open your project in IntelliJ IDEA
2. Go to **File** → **Project Structure** (or press `Ctrl+Alt+Shift+S`)
3. Select **Modules** → **Dependencies**
4. Click the **+** button and select **JARs or directories...**
5. Navigate to the Z3 `bin` folder and select `com.microsoft.z3.jar`
6. Click **OK** and **Apply**

### Step 2: Configure Native Library Path

**Method 1: Using Run Configuration (Recommended)**

1. Go to **Run** → **Edit Configurations...**
2. Select your application configuration (or create a new one)
3. In the **VM options** field, add:
   ```
   -Djava.library.path=/path/to/z3/bin
   ```
   (Replace with your actual Z3 bin directory path)
4. Click **OK**

**Method 2: Using Environment Variable (Windows)**

Add the Z3 `bin` directory to your system PATH as described in the Eclipse section above, then restart IntelliJ IDEA.

### Step 3: Verify Setup

Use the same test code from the Eclipse section to verify your setup.

## Visual Studio Code Setup

### Step 1: Install Java Extension Pack

1. Open Visual Studio Code
2. Install the **Extension Pack for Java** from the Extensions marketplace

### Step 2: Add Z3 JAR to Classpath

Create or edit `.vscode/settings.json` in your project root:

```json
{
    "java.project.referencedLibraries": [
        "path/to/z3/bin/com.microsoft.z3.jar"
    ]
}
```

### Step 3: Configure Native Library Path

Create or edit `.vscode/launch.json` in your project root:

```json
{
    "version": "0.2.0",
    "configurations": [
        {
            "type": "java",
            "name": "Launch with Z3",
            "request": "launch",
            "mainClass": "YourMainClass",
            "vmArgs": "-Djava.library.path=/path/to/z3/bin"
        }
    ]
}
```

Replace `YourMainClass` with your actual main class name and adjust the path to your Z3 bin directory.

### Step 4: Verify Setup

Use the same test code to verify your setup.

## Command-Line Build and Run

If you prefer to build and run from the command line:

### Compiling

```bash
# Windows
javac -cp "C:\path\to\z3\bin\com.microsoft.z3.jar;." YourProgram.java

# Linux/macOS
javac -cp "/path/to/z3/bin/com.microsoft.z3.jar:." YourProgram.java
```

### Running

```bash
# Windows
java -cp "C:\path\to\z3\bin\com.microsoft.z3.jar;." -Djava.library.path=C:\path\to\z3\bin YourProgram

# Linux
LD_LIBRARY_PATH=/path/to/z3/bin java -cp "/path/to/z3/bin/com.microsoft.z3.jar:." YourProgram

# macOS
DYLD_LIBRARY_PATH=/path/to/z3/bin java -cp "/path/to/z3/bin/com.microsoft.z3.jar:." YourProgram
```

## Troubleshooting

### ClassNotFoundException: com.microsoft.z3.Context

**Problem:** Java cannot find the Z3 classes.

**Solution:**
- Verify that `com.microsoft.z3.jar` is in your project's classpath
- In Eclipse: Check **Project Properties** → **Java Build Path** → **Libraries**
- In IntelliJ: Check **File** → **Project Structure** → **Modules** → **Dependencies**
- Ensure you're not just copying the JAR to your project's bin folder - it must be explicitly added to the classpath

### UnsatisfiedLinkError: no z3java in java.library.path

**Problem:** Java can find the Z3 classes but cannot load the native libraries.

**Solution:**
- Verify that `libz3.dll`/`libz3.so`/`libz3.dylib` and `libz3java.dll`/`libz3java.so`/`libz3java.dylib` are in a directory accessible to Java
- Add the Z3 `bin` directory to:
  - The `java.library.path` VM argument, or
  - The system PATH environment variable (Windows), or
  - The LD_LIBRARY_PATH (Linux) / DYLD_LIBRARY_PATH (macOS) environment variable

### ExceptionInInitializerError or Z3Exception

**Problem:** Z3 fails to initialize properly.

**Solution:**
- Ensure all Z3 files (JAR and native libraries) are from the same version
- Check that you're using a compatible Java version (Java 8 or later)
- Verify that the native libraries match your system architecture (32-bit vs 64-bit)

### Running on Different Platforms

**Windows:**
- Use semicolons (`;`) as classpath separators
- Native libraries: `libz3.dll` and `libz3java.dll`
- Set PATH or use `-Djava.library.path`

**Linux:**
- Use colons (`:`) as classpath separators  
- Native libraries: `libz3.so` and `libz3java.so`
- Set LD_LIBRARY_PATH or use `-Djava.library.path`

**macOS:**
- Use colons (`:`) as classpath separators
- Native libraries: `libz3.dylib` and `libz3java.dylib`
- Set DYLD_LIBRARY_PATH or use `-Djava.library.path`

## Maven/Gradle Setup

For Maven or Gradle projects, you can use system-scoped dependencies:

### Maven

```xml
<dependency>
    <groupId>com.microsoft</groupId>
    <artifactId>z3</artifactId>
    <version>x.x.x</version> <!-- Replace with your Z3 version -->
    <scope>system</scope>
    <systemPath>${project.basedir}/lib/com.microsoft.z3.jar</systemPath>
</dependency>
```

Place the Z3 JAR in your project's `lib` directory and configure the native library path as described above.

### Gradle

```gradle
dependencies {
    implementation files('lib/com.microsoft.z3.jar')
}
```

## Additional Resources

- [Z3 GitHub Repository](https://github.com/Z3Prover/z3)
- [Z3 Java API Documentation](https://z3prover.github.io/api/html/namespacecom_1_1microsoft_1_1z3.html)
- [Z3 Examples](https://github.com/Z3Prover/z3/tree/master/examples/java)
- [Z3 Guide](https://microsoft.github.io/z3guide/)

## Building Z3 with Java Support

If you need to build Z3 from source with Java bindings:

```bash
# Clone the repository
git clone https://github.com/Z3Prover/z3.git
cd z3

# Configure with Java support
python scripts/mk_make.py --java

# Build
cd build
make

# The Java bindings will be in the build directory
# - com.microsoft.z3.jar
# - libz3java.so / libz3java.dll / libz3java.dylib
# - libz3.so / libz3.dll / libz3.dylib
```

For more details on building Z3, see the main [README.md](../README.md).
