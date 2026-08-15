############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Assemble Java release packages from platform-specific Z3 release zips.
############################################
import argparse
import fnmatch
import os
import tempfile
import zipfile
from xml.sax.saxutils import escape


PLATFORMS = [
    {
        "classifier": "linux-x64",
        "pattern": "z3-*-x64-glibc*.zip",
        "libraries": ("libz3.so", "libz3java.so"),
    },
    {
        "classifier": "linux-arm64",
        "pattern": "z3-*-arm64-glibc*.zip",
        "libraries": ("libz3.so", "libz3java.so"),
    },
    {
        "classifier": "osx-x64",
        "pattern": "z3-*-x64-osx*.zip",
        "libraries": ("libz3.dylib", "libz3java.dylib"),
    },
    {
        "classifier": "osx-arm64",
        "pattern": "z3-*-arm64-osx*.zip",
        "libraries": ("libz3.dylib", "libz3java.dylib"),
    },
    {
        "classifier": "win-x86",
        "pattern": "z3-*-x86-win*.zip",
        "libraries": ("libz3.dll", "libz3java.dll", "z3.dll", "z3java.dll"),
    },
    {
        "classifier": "win-x64",
        "pattern": "z3-*-x64-win*.zip",
        "libraries": ("libz3.dll", "libz3java.dll", "z3.dll", "z3java.dll"),
    },
    {
        "classifier": "win-arm64",
        "pattern": "z3-*-arm64-win*.zip",
        "libraries": ("libz3.dll", "libz3java.dll", "z3.dll", "z3java.dll"),
    },
]


RESOURCE_PREFIX = "com/microsoft/z3/native"


def find_files(root, pattern):
    matches = []
    for dirpath, _, filenames in os.walk(root):
        for filename in filenames:
            if fnmatch.fnmatch(filename, pattern):
                matches.append(os.path.join(dirpath, filename))
    return sorted(matches)


def find_zip_entry(zip_file, basename):
    matches = [name for name in zip_file.namelist()
               if name.replace("\\", "/").endswith("/bin/" + basename)]
    if not matches:
        matches = [name for name in zip_file.namelist()
                   if os.path.basename(name) == basename]
    if not matches:
        return None
    return sorted(matches)[0]


def find_base_jar(zip_paths):
    for zip_path in zip_paths:
        with zipfile.ZipFile(zip_path) as zip_file:
            entry = find_zip_entry(zip_file, "com.microsoft.z3.jar")
            if entry is not None:
                return zip_path, entry
    raise RuntimeError("Could not find com.microsoft.z3.jar in release zips")


def copy_base_jar(zip_path, entry, output_path):
    with zipfile.ZipFile(zip_path) as zip_file, open(output_path, "wb") as out:
        out.write(zip_file.read(entry))


def create_native_jar(base_jar, zip_path, platform, output_path):
    found = []
    with zipfile.ZipFile(zip_path) as release_zip:
        for library in platform["libraries"]:
            entry = find_zip_entry(release_zip, library)
            if entry is not None:
                found.append((library, release_zip.read(entry)))

    if len(found) < 2:
        names = ", ".join(platform["libraries"])
        raise RuntimeError("Could not find required native libraries for {} in {}. Looked for {}".format(
            platform["classifier"], zip_path, names))

    with zipfile.ZipFile(base_jar) as source, zipfile.ZipFile(output_path, "w", zipfile.ZIP_DEFLATED) as target:
        for item in source.infolist():
            if not item.filename.startswith(RESOURCE_PREFIX + "/"):
                target.writestr(item, source.read(item.filename))
        for library, data in found:
            target.writestr("{}/{}/{}".format(RESOURCE_PREFIX, platform["classifier"], library), data)


def write_pom(path, group_id, artifact_id, version):
    pom = """<project xmlns=\"http://maven.apache.org/POM/4.0.0\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" xsi:schemaLocation=\"http://maven.apache.org/POM/4.0.0 https://maven.apache.org/xsd/maven-4.0.0.xsd\">
  <modelVersion>4.0.0</modelVersion>
  <groupId>{}</groupId>
  <artifactId>{}</artifactId>
  <version>{}</version>
  <name>Z3 Java bindings</name>
  <description>Java bindings for the Z3 theorem prover.</description>
  <url>https://github.com/Z3Prover/z3</url>
  <licenses>
    <license>
      <name>MIT License</name>
      <url>https://github.com/Z3Prover/z3/blob/master/LICENSE.txt</url>
    </license>
  </licenses>
</project>
""".format(escape(group_id), escape(artifact_id), escape(version))
    with open(path, "w", encoding="utf-8") as out:
        out.write(pom)


def main():
    parser = argparse.ArgumentParser(description="Build Maven-ready Z3 Java release artifacts from release zips")
    parser.add_argument("--artifacts-dir", required=True)
    parser.add_argument("--out-dir", required=True)
    parser.add_argument("--version", required=True)
    parser.add_argument("--group-id", default="com.microsoft")
    parser.add_argument("--artifact-id", default="z3")
    args = parser.parse_args()

    os.makedirs(args.out_dir, exist_ok=True)
    all_zips = find_files(args.artifacts_dir, "*.zip")
    if not all_zips:
        raise RuntimeError("No release zips found under " + args.artifacts_dir)

    base_zip, base_entry = find_base_jar(all_zips)
    base_jar = os.path.join(args.out_dir, "{}-{}.jar".format(args.artifact_id, args.version))
    copy_base_jar(base_zip, base_entry, base_jar)

    for platform in PLATFORMS:
        matches = find_files(args.artifacts_dir, platform["pattern"])
        if not matches:
            raise RuntimeError("No release zip matching {} for {}".format(platform["pattern"], platform["classifier"]))
        output = os.path.join(args.out_dir, "{}-{}-{}.jar".format(
            args.artifact_id, args.version, platform["classifier"]))
        create_native_jar(base_jar, matches[0], platform, output)

    write_pom(os.path.join(args.out_dir, "{}-{}.pom".format(args.artifact_id, args.version)),
              args.group_id, args.artifact_id, args.version)


if __name__ == "__main__":
    main()
