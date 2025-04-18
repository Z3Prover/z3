import { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";

async function importZ3() {
    try {
        const z3 = await import("z3-solver");
        return await z3.init();
    } catch (e) {
        console.error("Failed to import z3-solver:", e?.message);
        return undefined;
    }
}

async function Z3Run(input) {
    const z3p = await importZ3();
    if (!z3p) {
        return "Z3 not available. Make sure to install the https://www.npmjs.com/package/z3-solver package.";
    }
    const { Z3 } = z3p;
    const cfg = Z3.mk_config();
    const ctx = Z3.mk_context(cfg);
    Z3.del_config(cfg);
    const timeout = 10000;
    Z3.global_param_set("timeout", String(timeout));
    let output = "";
    let error = "";
    const timeStart = Date.now();
    try {
        output = (await Z3.eval_smtlib2_string(ctx, input)) ?? "";
    } catch (e) {
        error = e.message ?? "Error message is empty";
    } finally {
        Z3.del_context(ctx);
    }
    if (/unknown/.test(output)) {
        const timeEnd = Date.now();
        if (timeEnd - timeStart >= timeout) {
            output = output + "\nZ3 timeout\n";
        }
    }
    if (!error) return output;
    else return `error: ${error}\n\n${output || ""}`;
}



const server = new McpServer({
    name: "z3",
    version: "1.0.0"
});

server.tool(
    "eval",
    { command: { type: "string", description: "smtlib2 command" } },
    async ({ command }) => {
        const result = await Z3Run(command);
        return { content: [{ type: "text", text: result }] };
    }
);

const transport = new StdioServerTransport();
await server.connect(transport);
