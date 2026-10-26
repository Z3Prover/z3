/**
 * Deterministic workflow for the launch tests: one durable tool step, no agent stages, no
 * commands. It imports the real definition, so the whole fstar-proof-checking module graph
 * must load in the launch runtime too.
 */
import { workflow } from "@bastani/atomic/workflows";
import { Type } from "typebox";
import fstarProofChecking from "../../fstar-proof-checking.js";

export default workflow({
  name: "fstar-launch-probe",
  description: "Doubles a number in one durable step and names the workflow definition it loaded.",
  inputs: { value: Type.Integer({ default: 1 }) },
  outputs: { doubled: Type.Integer(), loaded: Type.String() },
  run: async (ctx) => {
    const value = ctx.inputs.value as number;
    const doubled = await ctx.tool("double", { value }, async () => value * 2);
    return { doubled, loaded: fstarProofChecking.name };
  },
});
