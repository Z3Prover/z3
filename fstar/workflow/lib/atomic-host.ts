/**
 * Loads this workflow outside Atomic's loader. Atomic supplies `@bastani/atomic/workflows` and
 * `typebox` to workflow files; here the same modules come from the installed Atomic package.
 * `registerAtomicHostModules` (Bun only, for the tests' in-process runs) registers them as
 * virtual modules so the workflow definition imports exactly the host's SDK instance; the
 * launcher's Node runs (lib/node-run.ts) resolve `HOST_SPECIFIERS` from `atomicPackageDir()`.
 */
import { spawnSync } from "node:child_process";
import { existsSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join } from "node:path";
import { pathToFileURL } from "node:url";

export const HOST_SPECIFIERS = [
  "@bastani/atomic/workflows",
  "@bastani/atomic/workflows/builtin/steering-context",
  "typebox",
] as const;

interface BunPluginBuilder {
  module(specifier: string, callback: () => { exports: Record<string, unknown>; loader: "object" }): void;
}
interface BunRuntime {
  plugin(plugin: { name: string; setup(builder: BunPluginBuilder): void }): void;
}

/** Locate the installed `@bastani/atomic` package: `ATOMIC_PACKAGE_DIR`, `npm root -g`, or next to `atomic` on PATH. */
export function atomicPackageDir(): string {
  const candidates: string[] = [];
  if (process.env.ATOMIC_PACKAGE_DIR) candidates.push(process.env.ATOMIC_PACKAGE_DIR);
  const npmRoot = spawnSync("npm", ["root", "-g"], { encoding: "utf8", shell: true, timeout: 30_000 });
  if (npmRoot.status === 0 && npmRoot.stdout.trim()) candidates.push(join(npmRoot.stdout.trim(), "@bastani", "atomic"));
  const which = spawnSync(process.platform === "win32" ? "where" : "which", ["atomic"], { encoding: "utf8", timeout: 30_000 });
  for (const line of which.status === 0 ? which.stdout.split(/\r?\n/) : []) {
    if (line.trim()) candidates.push(join(dirname(line.trim()), "node_modules", "@bastani", "atomic"));
  }
  const found = candidates.find((candidate) => existsSync(join(candidate, "package.json")));
  if (!found) throw new Error("Cannot find the @bastani/atomic package; set ATOMIC_PACKAGE_DIR to its directory.");
  return found;
}

let registered: string | undefined;

/** Register the host modules once per process and return the package directory used. */
export async function registerAtomicHostModules(packageDir = atomicPackageDir()): Promise<string> {
  if (registered) return registered;
  const bun = (globalThis as { Bun?: BunRuntime }).Bun;
  if (!bun) throw new Error("registerAtomicHostModules requires Bun; inside Atomic the loader provides these modules.");
  const resolver = createRequire(join(packageDir, "package.json"));
  const modules = new Map<string, Record<string, unknown>>();
  for (const specifier of HOST_SPECIFIERS) {
    modules.set(specifier, (await import(pathToFileURL(resolver.resolve(specifier)).href)) as Record<string, unknown>);
  }
  bun.plugin({
    name: "atomic-host-modules",
    setup(builder) {
      for (const [specifier, exports] of modules) builder.module(specifier, () => ({ exports, loader: "object" }));
    },
  });
  registered = packageDir;
  return packageDir;
}
