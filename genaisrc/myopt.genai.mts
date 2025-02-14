script({
    title: "Invoke LLM code optimization",
    files: "code_slices/muz/spacer/orig_spacer_antiunify.cpp_anti_unifier.cpp"
})

import { invokeLLMOpt } from "./myai.genai.mts";

let file = env.files[0];
let answer = await invokeLLMOpt(file);
const outputFile = file.filename + ".opt";
await workspace.writeText(outputFile, answer);
