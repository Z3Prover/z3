############################################
# Copyright (c) 2026 Microsoft Corporation
# Collect handwritten and generated Java sources; never compile native code.
############################################
import argparse
from pathlib import Path
import difflib
import re
import shutil
import sys

from prepare import ROOT, SCRIPTS, run, signatures
from mk_java_package import checked_zip, sha256


def canonical_signatures(text):
    # javac versions may emit the same synthetic members in different orders.
    # Preserve each class header and every member/descriptor, ignoring order only.
    classes = re.findall(r'(?m)^([^\n]+ \{)\n(.*?)^}', text, re.S)
    if not classes:
        raise ValueError('Cannot parse javap member signatures')
    return sorted((header, tuple(sorted(part.strip() for part in
                                       re.split(r'(?m)(?=^  \S)', body) if part.strip())))
                  for header, body in classes)


def verify_loader_sources(sources, provenance):
    expected = {'NativeLibraryLoader.java': provenance['loader_sha256']}
    if 'generated_native_sha256' in provenance:
        expected['Native.java'] = provenance['generated_native_sha256']
    for name, digest in expected.items():
        if sha256((sources / 'com/microsoft/z3' / name).read_bytes()) != digest:
            raise ValueError('Source attachment differs from prepared loader/generator input: ' + name)


def collect(source_root, headers, generated, loader, out, api_jar):
    out.mkdir(parents=True, exist_ok=False)
    package = out / 'com/microsoft/z3'
    package.mkdir(parents=True)
    entries = checked_zip(api_jar.read_bytes())
    files = [path for path in (source_root / 'src/api/java').glob('*.java')
             if 'com/microsoft/z3/' + path.stem + '.class' in entries]
    if not files or any(path.name == 'Native.java' for path in files):
        raise ValueError('Expected handwritten API sources without generated Native.java')
    for path in files:
        shutil.copyfile(path, package / path.name)
    shutil.copyfile(generated / 'Native.java', package / 'Native.java')
    shutil.copyfile(loader, package / loader.name)
    run([sys.executable, SCRIPTS / 'mk_consts_files.py', *headers,
         '--java-output-dir', generated, '--java-package-name', 'com.microsoft.z3'])
    shutil.copytree(generated / 'enumerations', package / 'enumerations')
    return out


def verify(sources, api_jar, work):
    """Recompile the source attachment and compare every JVM member descriptor."""
    work.mkdir(parents=True, exist_ok=False)
    classes = work / 'classes'
    classes.mkdir()
    paths = sorted(sources.rglob('*.java'))
    # An argument file avoids Windows command-line length limits.
    arguments = work / 'sources.args'
    arguments.write_text('\n'.join('"' + p.resolve().as_posix() + '"' for p in paths), encoding='utf-8')
    run(['javac', '--release', '8', '-encoding', 'UTF-8', '-d', classes, '@' + str(arguments)])
    rebuilt = {p.relative_to(classes).as_posix(): p.read_bytes() for p in classes.rglob('*.class')}
    expected = {name: data for name, data in checked_zip(api_jar.read_bytes()).items() if name.endswith('.class')}
    if set(rebuilt) != set(expected):
        raise ValueError('Source/API class set differs: ' + str(sorted(set(rebuilt) ^ set(expected))))
    family = sorted(expected)
    before, after = signatures(api_jar, family), signatures(classes, family)
    if canonical_signatures(before) != canonical_signatures(after):
        difference = '\n'.join(difflib.unified_diff(before.splitlines(), after.splitlines(),
                                                  fromfile='API JAR', tofile='rebuilt sources'))
        raise ValueError('Source/API JVM member signatures differ:\n' + difference[:6000])
    return {'class_count': len(family), 'java_release': 8,
            'api_sha256': sha256(api_jar.read_bytes()),
            'files': {p.relative_to(sources).as_posix(): sha256(p.read_bytes()) for p in paths}}


def current(out, work, api_jar):
    # Reuse the header list used by the official CMake Java generator.
    text = (ROOT / 'CMakeLists.txt').read_text(encoding='utf-8')
    match = re.search(r'set\(Z3_API_HEADER_FILES_TO_SCAN\s+([^)]*)\)', text)
    if not match:
        raise ValueError('Cannot locate official Java API header list')
    headers = [ROOT / 'src/api' / name for name in match[1].split()]
    work.mkdir(parents=True, exist_ok=False)
    run([sys.executable, SCRIPTS / 'update_api.py', *headers,
         '--java-input-dir', ROOT / 'src/api/java', '--java-output-dir', work,
         '--java-package-name', 'com.microsoft.z3'])
    collect(ROOT, headers, work, ROOT / 'src/api/java/NativeLibraryLoader.java', out, api_jar)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir', type=Path, required=True)
    parser.add_argument('--work-dir', type=Path, required=True)
    parser.add_argument('--api-jar', type=Path, required=True)
    args = parser.parse_args()
    try:
        current(args.out_dir, args.work_dir, args.api_jar)
    except (OSError, ValueError) as error:
        parser.exit(1, 'Java source preparation failed: ' + str(error) + '\n')


if __name__ == '__main__':
    main()
