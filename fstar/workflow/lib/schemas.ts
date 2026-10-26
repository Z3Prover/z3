/** TypeBox schemas for schema-backed workflow stages. */
import { Type } from "typebox";

export const VerifierVerdictSchema = Type.Object({
  verdict: Type.Union([Type.Literal("verified"), Type.Literal("unverified"), Type.Literal("rejected")], {
    description: "verified only if every final command ran with the real toolchain and passed.",
  }),
  toolchainAvailable: Type.Boolean({ description: "Whether F*, OCaml/opam and (when relevant) Cherry actually ran." }),
  commands: Type.Array(Type.Object({
    command: Type.String(),
    exitCode: Type.Integer(),
    phase: Type.Union([Type.Literal("baseline"), Type.Literal("exploratory"), Type.Literal("final")]),
  }, { additionalProperties: false }), { description: "Commands actually executed, with observed exit codes." }),
  resolvedFingerprints: Type.Array(Type.String(), { description: "Finding fingerprints whose targeted inputs were observed to improve." }),
  soundnessConcerns: Type.Array(Type.String()),
  summary: Type.String(),
}, { additionalProperties: false });
