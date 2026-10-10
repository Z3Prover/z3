#!/usr/bin/env python3
"""Build the pinned external proof checkers (Python 3.12+, CMake, Cargo, GMP)."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tarfile
import urllib.request

HERE = Path(__file__).resolve().parent


def checked(path, expected):
    if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise ValueError(f'checksum mismatch: {path}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True, help='new build directory')
    parser.add_argument('--archives', type=Path, help='use local carcara.tar.gz and ffpacheck.tar.gz')
    parser.add_argument('--jobs', type=int, default=2)
    parser.add_argument('--cmake-arg', action='append', default=[])
    args = parser.parse_args()
    if args.jobs <= 0:
        parser.error('--jobs must be positive')
    pins = json.loads((HERE / 'versions.json').read_text())
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    for name in ['carcara', 'ffpacheck']:
        pin = pins[name]
        archive = out / (name + '.tar.gz')
        if args.archives:
            shutil.copyfile(args.archives / archive.name, archive)
        else:
            with urllib.request.urlopen(pin['archive'], timeout=120) as response, archive.open('wb') as dest:
                shutil.copyfileobj(response, dest)
        checked(archive, pin['sha256'])
        unpacked = out / (name + '-source')
        unpacked.mkdir()
        with tarfile.open(archive) as tar:
            tar.extractall(unpacked, filter='data')
        roots = list(unpacked.iterdir())
        if len(roots) != 1 or not roots[0].is_dir():
            raise ValueError(f'expected one source directory: {archive}')
        src = roots[0]
        if name == 'carcara':
            # The archive's rust-toolchain file and Cargo.lock pin the build.
            subprocess.run(['cargo', 'build', '--release', '--locked', '-j', str(args.jobs)], cwd=src, check=True)
            binary = src / 'target/release/carcara'
        else:
            patch = HERE / pin['patch']
            checked(patch, pin['patch_sha256'])
            subprocess.run(['patch', '-p1', '-i', str(patch)], cwd=src, check=True)
            build = out / 'ffpacheck-build'
            subprocess.run(['cmake', '-S', str(src), '-B', str(build),
                            '-DCMAKE_BUILD_TYPE=Release', *args.cmake_arg], check=True)
            subprocess.run(['cmake', '--build', str(build), '--parallel', str(args.jobs)], check=True)
            binary = build / 'ffpacheck'
        shutil.copy2(binary, out / name)
    shutil.copy2(HERE / 'versions.json', out / 'versions.json')
    hashes = {name: hashlib.sha256((out / name).read_bytes()).hexdigest()
              for name in ['carcara', 'ffpacheck']}
    (out / 'binaries.json').write_text(json.dumps(hashes, indent=2) + '\n')
    print(f'Checkers built and source checksums verified: {out}')


if __name__ == '__main__':
    main()
