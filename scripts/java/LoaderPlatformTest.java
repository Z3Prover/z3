// Copyright (c) 2026 Microsoft Corporation
package com.microsoft.z3;

public final class LoaderPlatformTest {
    public static void main(String[] args) {
        String[][] cases = {
            {"Windows 11", "amd64", "win-x64"},
            {"Windows 10", "x86", "win-x86"},
            {"Windows 11", "aarch64", "win-arm64"},
            {"Darwin", "arm64", "osx-arm64"},
            {"Mac OS X", "x86_64", "osx-x64"},
            {"Linux", "aarch64", "linux-arm64"},
            {"Linux", "AMD64", "linux-x64"},
            {"Linux", "mips", "linux-unsupported-arch"},
            {"FreeBSD", "amd64", "unsupported-os-x64"}
        };
        for (String[] test : cases) {
            System.setProperty("os.name", test[0]);
            System.setProperty("os.arch", test[1]);
            if (!NativeLibraryLoader.platform().equals(test[2])) {
                throw new AssertionError("Platform mapping: " + test[0] + "/" + test[1]);
            }
        }
        System.out.println("PASS platform aliases: " + cases.length);
    }
}
