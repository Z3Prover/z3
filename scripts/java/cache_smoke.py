############################################
# Copyright (c) 2026 Microsoft Corporation
# Real JNI cache checks, used by both fast and current-source native CI.
############################################
import hashlib
import os
from pathlib import Path
import subprocess

CACHE_MODES = {'cache-default', 'cache-reuse', 'cache-concurrent', 'cache-corrupt',
               'cache-unavailable', 'cache-classloaders', 'cache-overlap',
               'cache-retention', 'cache-links', 'cache-failure', 'cache-classloaders-concurrent'}


def cache_smoke(jar, classes, work, version, libraries, environment, run):
    work.mkdir()
    home = work / 'home'
    home.mkdir()
    empty = work / 'empty'
    empty.mkdir()
    cache = work / 'cache'
    results = []

    def command(temporary, root=cache, extra=(), helper=None):
        temporary.mkdir()
        args = ['java', '-Djava.library.path=' + str(empty.resolve()),
                '-Djava.io.tmpdir=' + str(temporary.resolve()), '-Duser.home=' + str(home.resolve())]
        if root is not None:
            args.append('-Dz3.nativeCacheDir=' + str(root.absolute()))
        args.extend(extra)
        args.extend(['-cp', str(jar) + os.pathsep + str(classes.resolve())])
        args.extend(helper or ['Smoke', 'lifecycle', version])
        return args

    def assert_pair(root, private=False):
        entries = list(root.iterdir())
        directories = [p for p in entries if p.is_dir()]
        if len(directories) != 1 or {p.name for p in entries if p.is_file()} != (set() if private else {'.lock'}):
            raise ValueError('Expected exactly one native pair: ' + str(root))
        pair = directories[0]
        if {p.name for p in pair.iterdir()} != set(libraries):
            raise ValueError('Unexpected native pair contents: ' + str(pair))
        return pair

    def snapshot(pair):
        return {p.name: (hashlib.sha256(p.read_bytes()).hexdigest(), p.stat().st_mtime_ns)
                for p in pair.iterdir()}

    def passed(mode):
        results.append(mode)
        print(jar.name + ': PASS ' + mode, flush=True)

    # No cache property: exercise the actual default, isolated from the runner profile.
    default_temp = work / 'default-tmp'
    run(command(default_temp, root=None), environment)
    assert_pair(home / '.z3/native')
    if any(default_temp.iterdir()):
        raise ValueError('Default cache unexpectedly used java.io.tmpdir')
    passed('cache-default')

    run(command(work / 'first-tmp'), environment)
    pair = assert_pair(cache)
    original = snapshot(pair)
    for index in range(3):
        temporary = work / ('reuse-%d-tmp' % index)
        run(command(temporary), environment)
        if any(temporary.iterdir()) or snapshot(assert_pair(cache)) != original:
            raise ValueError('A JVM restart rewrote native files or left private extraction files')
    passed('cache-reuse')

    # Start four JVMs against an empty cache; none may need a private extraction.
    concurrent_cache = work / 'concurrent'
    pending = []
    try:
        for index in range(4):
            temporary = work / ('concurrent-%d-tmp' % index)
            process = subprocess.Popen(command(temporary, concurrent_cache), env=environment,
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                       text=True, encoding='utf-8', errors='replace')
            pending.append((process, temporary))
        for process, temporary in pending:
            output, error = process.communicate(timeout=120)
            if process.returncode or 'PASS lifecycle' not in output or any(temporary.iterdir()):
                raise ValueError('Concurrent JVM cache failed:\n' + output + error)
    finally:
        for process, _ in pending:
            if process.poll() is None:
                process.kill()
                process.communicate()
    if {k: v[0] for k, v in snapshot(assert_pair(concurrent_cache)).items()} != {k: v[0] for k, v in original.items()}:
        raise ValueError('Concurrent cache binary mismatch')
    passed('cache-concurrent')

    (pair / libraries[-1]).write_bytes(b'intentionally damaged cache')
    temporary = work / 'repair-tmp'
    run(command(temporary), environment)
    if any(temporary.iterdir()) or {k: v[0] for k, v in snapshot(assert_pair(cache)).items()} != {k: v[0] for k, v in original.items()}:
        raise ValueError('Damaged cache was not repaired from bundled bytes')
    passed('cache-corrupt')

    blocked = work / 'not-a-directory'
    blocked.write_text('blocked', encoding='ascii')
    temporary = work / 'fallback-tmp'
    run(command(temporary, blocked, helper=['Smoke', 'lifecycle-private', version, ','.join(libraries)]), environment)
    passed('cache-unavailable')

    run(command(work / 'failure-tmp', blocked,
                extra=['-Djava.io.tmpdir=' + str(blocked.resolve())],
                helper=['Smoke', 'cache-failure', version]), environment)
    passed('cache-failure')

    for mode, argument in [('cache-classloaders', 'isolated'), ('cache-overlap', 'overlap'),
                           ('cache-classloaders-concurrent', 'concurrent')]:
        temporary = work / (argument + '-tmp')
        output = run(command(temporary, helper=['CacheClassLoaderTest', argument,
                     str(jar), str(classes.resolve()), version]), environment)
        if 'PASS ' + argument not in output:
            raise ValueError('Missing ClassLoader proof: ' + output)
        passed(mode)

    # Older owned entries are eligible for pruning; unrelated data is never touched.
    prefix = pair.name.rsplit('-', 1)[0]
    for index in range(5):
        old = cache / (prefix + '-' + ('%064x' % index))
        old.mkdir()
        for name in libraries:
            (old / name).write_bytes(b'old cache fixture')
        os.utime(old, (1, 1))
    protected = cache / (prefix + '-' + 'f' * 64)
    protected.mkdir()
    (protected / 'user-data').write_bytes(b'preserve')
    os.utime(protected, (1, 1))
    abandoned = cache / '.extract-abandoned-test'
    abandoned.mkdir()
    (abandoned / libraries[0]).write_bytes(b'incomplete')
    os.utime(abandoned, (1, 1))
    run(command(work / 'retention-tmp'), environment)
    pairs = [p for p in cache.iterdir() if p.is_dir() and p != protected]
    if len(pairs) != 3 or abandoned.exists() or (protected / 'user-data').read_bytes() != b'preserve':
        raise ValueError('Cache retention or unknown-file protection failed')
    passed('cache-retention')

    # Every native runner must test symlinks. Windows CI needs Developer Mode or admin.
    link = work / 'linked-cache'
    target = work / 'link-target'
    target.mkdir()
    link.symlink_to(target.resolve(), target_is_directory=True)
    temporary = work / 'link-tmp'
    run(command(temporary, link, helper=['Smoke', 'lifecycle-private', version, ','.join(libraries)]), environment)
    if any(target.iterdir()):
        raise ValueError('Loader followed a native-cache symlink')
    passed('cache-links')
    if set(results) != CACHE_MODES:
        raise ValueError('Incomplete native cache smoke coverage')
    return results
