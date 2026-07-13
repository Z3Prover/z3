import assert from 'assert';
import { SpawnOptions, spawnSync as originalSpawnSync } from 'child_process';
import fs, { existsSync } from 'fs';
import os from 'os';
import path from 'path';
import process from 'process';
import { asyncFuncs } from './async-fns';
import { makeCCSinglethreadWrapper } from './make-cc-wrapper';
import { functions } from './parse-api';

console.log('--- Building single-threaded WASM (no SharedArrayBuffer required)');

// Single-threaded build: no -pthread / USE_PTHREADS.
// POLLING_TIMER gives timeout support via wall-clock polling rather than threads.
const SWAP_OPTS: SpawnOptions = {
  shell: true,
  stdio: 'inherit',
  env: {
    ...process.env,
    CXXFLAGS: '-DSINGLE_THREAD -DPOLLING_TIMER -fexceptions -s DISABLE_EXCEPTION_CATCHING=0',
    LDFLAGS: '-s WASM_BIGINT',
    FPMATH_ENABLED: 'False', // Until Safari supports WASM SSE, we have to disable fast FP support
  },
};

function spawnSync(command: string, opts: SpawnOptions = {}) {
  console.log(`- ${command}`);
  // TODO(ritave): Create a splitter that keeps track of quoted strings
  const [cmd, ...args] = command.split(' ');
  const { error, ...rest } = originalSpawnSync(cmd, args, { ...SWAP_OPTS, ...opts });
  if (error !== undefined || rest.status !== 0) {
    if (error !== undefined) {
      console.error(error.message);
    } else {
      console.error(`Process exited with status ${rest.status}`);
    }
    process.exit(1);
  }
  return rest;
}

function exportedFuncs(): string[] {
  const extras = [
    '_malloc',
    '_free',
    '_set_throwy_error_handler',
    '_set_noop_error_handler',
    ...asyncFuncs.map(f => '_async_' + f),
  ];

  return [...extras, ...(functions as any[]).map(f => '_' + f.name)];
}

assert(fs.existsSync('./package.json'), 'Not in the root directory of js api');
const z3RootDir = path.join(process.cwd(), '../../../');

// Single-threaded libz3.a is built in a separate directory to avoid
// conflicting with the threaded build in 'build/'.
const singlethreadBuildDir = 'build-singlethread';
const singlethreadBuildPath = path.join(z3RootDir, singlethreadBuildDir);

if (!existsSync(path.join(singlethreadBuildPath, 'Makefile'))) {
  spawnSync(
    `emconfigure python scripts/mk_make.py --staticlib --single-threaded --arm64=false --build=${singlethreadBuildDir}`,
    { cwd: z3RootDir },
  );
}

spawnSync(`emmake make -j${os.cpus().length} libz3.a`, { cwd: singlethreadBuildPath });

const ccWrapperPath = 'build/async-fns-singlethread.cc';
console.log(`- Building ${ccWrapperPath}`);
fs.mkdirSync(path.dirname(ccWrapperPath), { recursive: true });
fs.writeFileSync(ccWrapperPath, makeCCSinglethreadWrapper());

const fns = JSON.stringify(exportedFuncs());
// No PThread in exported methods for the single-threaded build.
const methods = '["ccall","FS","UTF8ToString","intArrayFromString","addFunction","removeFunction"]';
const libz3a = path.normalize(`../../../${singlethreadBuildDir}/libz3.a`);
spawnSync(
  `emcc build/async-fns-singlethread.cc ${libz3a} --std=c++20 --pre-js src/low-level/async-wrapper.js -fexceptions -s WASM_BIGINT -s MODULARIZE=1 -s 'EXPORT_NAME="initZ3SingleThread"' -s EXPORTED_RUNTIME_METHODS=${methods} -s EXPORTED_FUNCTIONS=${fns} -s DISABLE_EXCEPTION_CATCHING=0 -s SAFE_HEAP=0 -s ALLOW_MEMORY_GROWTH=1 -s INITIAL_MEMORY=64MB -s TOTAL_STACK=20MB -s ALLOW_TABLE_GROWTH=1 -I z3/src/api/ -o build/z3-built-singlethread.js`,
);

fs.rmSync(ccWrapperPath);

console.log('--- Single-threaded WASM build finished');
