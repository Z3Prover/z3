/**
 * Module resolution for the Node entry points (lib/node-run.ts, lib/node-evidence.ts). Node
 * strips the TypeScript types; this hook loads the host modules from the installed Atomic package,
 * as Atomic's loader does, and maps the workflow's `.js` import specifiers to its `.ts` sources.
 * Register it before importing any workflow module.
 */
import { existsSync } from "node:fs";
import { registerHooks } from "node:module";
import { join } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
// Explicit `.ts`: this module is loaded before the hook below maps `.js` specifiers to sources.
import { HOST_SPECIFIERS } from "./atomic-host.ts";

/** Also shared by Atomic's loader: the SDK root (stage-session reads in lib/stage-sessions.ts). */
const NODE_HOST_SPECIFIERS = [...HOST_SPECIFIERS, "@bastani/atomic"];

export function registerWorkflowHooks(packageDir: string): void {
  const host = new Set<string>(NODE_HOST_SPECIFIERS);
  const hostParent = pathToFileURL(join(packageDir, "package.json")).href;
  registerHooks({
    resolve(specifier, context, nextResolve) {
      // Resolved as if imported from inside the installed package: the instances Atomic itself uses.
      if (host.has(specifier)) return nextResolve(specifier, { ...context, parentURL: hostParent });
      if (/^\.\.?\//.test(specifier) && specifier.endsWith(".js") && context.parentURL?.endsWith(".ts")) {
        const source = new URL(`${specifier.slice(0, -".js".length)}.ts`, context.parentURL);
        if (existsSync(fileURLToPath(source))) return { url: source.href, shortCircuit: true };
      }
      return nextResolve(specifier, context);
    },
  });
}
