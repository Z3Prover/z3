# Z3 Build Cache Workflow

This workflow builds Z3 and caches the built binaries for use by other workflows, eliminating the need for repeated builds and saving significant CI time.

## Purpose

The `build-z3-cache.yml` workflow:
1. Builds Z3 from source using the Python build system
2. Caches the built binaries and libraries
3. Can be triggered manually, on schedule, or on pushes to main
4. Can be called as a reusable workflow from other workflows

## Cache Contents

The workflow caches:
- `build/z3` - Main Z3 executable
- `build/libz3.so` and `build/libz3.a` - Z3 libraries
- `build/*.so` and `build/*.a` - Additional library files
- `build/python` - Python bindings

## Cache Key Format

The cache key is: `z3-build-{OS}-{git-sha}`

**How it works:**
- Each commit gets its own cache entry based on its git SHA
- When restoring, the `restore-keys` pattern allows falling back to caches from previous commits
- The most recent cache matching the `restore-keys` pattern will be used if an exact key match isn't found
- This means workflows typically restore from a recent build and save a new cache for the current commit

**Example:**
- A workflow on commit `abc123` will look for `z3-build-Linux-abc123`
- If not found, it falls back to the most recent `z3-build-Linux-*` cache
- After building, it saves a new cache with key `z3-build-Linux-abc123`

This ensures:
- Caches are OS-specific
- Each new commit can reuse builds from recent commits
- The cache stays relatively up-to-date with the repository

## Using the Cached Build

### Option 1: Direct Cache Restore (Recommended)

Add these steps to your workflow before you need to use Z3:

```yaml
- name: Checkout code
  uses: actions/checkout@v6

- name: Setup Python
  uses: actions/setup-python@v6
  with:
    python-version: '3.x'

- name: Restore Z3 cache
  id: cache-z3
  uses: actions/cache/restore@v4
  with:
    path: |
      build/z3
      build/libz3.so
      build/libz3.a
      build/*.so
      build/*.a
      build/python
    key: z3-build-${{ runner.os }}-${{ github.sha }}
    restore-keys: |
      z3-build-${{ runner.os }}-

- name: Build Z3 (if not cached)
  if: steps.cache-z3.outputs.cache-hit != 'true'
  run: |
    python scripts/mk_make.py
    cd build
    make -j$(nproc)

- name: Verify Z3 is available
  run: |
    build/z3 --version
```

### Option 2: Call as Reusable Workflow

You can also call this workflow before your job:

```yaml
jobs:
  build-cache:
    uses: ./.github/workflows/build-z3-cache.yml

  your-job:
    needs: build-cache
    runs-on: ubuntu-latest
    steps:
      - name: Checkout code
        uses: actions/checkout@v6
      
      - name: Restore Z3 cache
        uses: actions/cache/restore@v4
        with:
          path: |
            build/z3
            build/libz3.so
            build/libz3.a
            build/*.so
            build/*.a
            build/python
          key: ${{ needs.build-cache.outputs.cache-key }}
      
      - name: Use Z3
        run: build/z3 --version
```

## Benefits

- **Time Savings**: Eliminates 15-17 minute build time when cache hit
- **Resource Efficiency**: Reduces CI compute usage
- **Reliability**: Ensures consistent Z3 binary across workflow runs
- **Flexibility**: Works with manual triggers, schedules, and pushes

## Example: Soundness Bug Detector

The soundness bug detector workflow can now use cached Z3:

```yaml
name: Soundness Bug Detector

on:
  schedule:
    - cron: '0 4 * * *'

jobs:
  detect-bugs:
    runs-on: ubuntu-latest
    steps:
      - name: Checkout code
        uses: actions/checkout@v6

      - name: Setup Python
        uses: actions/setup-python@v6
        with:
          python-version: '3.x'

      - name: Restore Z3 cache
        uses: actions/cache/restore@v4
        with:
          path: |
            build/z3
            build/libz3.so
            build/libz3.a
            build/*.so
            build/*.a
            build/python
          key: z3-build-${{ runner.os }}-${{ github.sha }}
          restore-keys: |
            z3-build-${{ runner.os }}-

      - name: Build Z3 (if not cached)
        run: |
          if [ ! -f build/z3 ]; then
            python scripts/mk_make.py
            cd build
            make -j$(nproc)
          fi

      - name: Test soundness issues
        run: |
          # Now Z3 is available at build/z3
          build/z3 --version
          # ... rest of soundness testing logic
```

## Cache Maintenance

**GitHub Actions Cache Policies:**
- **Retention**: Caches are removed after 7 days without being accessed
- **Repository Limit**: Total cache size per repository is limited to 10GB
- **Eviction**: Least Recently Used (LRU) caches are evicted when the limit is reached
- **Size per Entry**: Each Z3 build cache is approximately 68MB (z3: 34MB, libz3.so: 33MB, python: 2MB)

**This Workflow's Strategy:**
- **Daily Schedule**: Runs daily at 2 AM UTC to refresh the cache
- **Push Trigger**: Updates cache on pushes to master/main branches  
- **Manual Trigger**: Can be triggered manually via workflow_dispatch

**Best Practices:**
- The daily schedule ensures at least one cache is always available (within 7-day retention)
- Multiple commits may share the same cache via the `restore-keys` fallback pattern
- If you need guaranteed cache availability for a specific commit, manually trigger the workflow

## Troubleshooting

### Cache miss on every run

If you're getting cache misses, check:
1. The cache key format matches between save and restore
2. The git SHA is consistent (use the same checkout before restore)
3. The runner OS matches

### Build not working after restore

After restoring from cache:
1. Verify all library files are present: `ls -la build/`
2. Check library dependencies: `ldd build/z3`
3. Ensure Python bindings are in the correct location

### Need different build configuration

If you need a different Z3 build (e.g., with debug symbols), you can:
1. Create a separate cache workflow with a different cache key
2. Or build Z3 directly in your workflow with custom flags

## Related Workflows

- `ci.yml` - Main CI workflow (could benefit from caching)
- `soundness-bug-detector.lock.yml` - Automated soundness testing
- `nightly.yml` - Nightly builds (uses its own build process)

## Implementation Note

This addresses the recommendation from [GitHub Discussion #8458](https://github.com/Z3Prover/z3/discussions/8458), which identified that the soundness bug detector and other workflows were unable to test properly due to missing Z3 binaries and build tool limitations.
