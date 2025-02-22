
script({
    title: "optimize functions in a file",
    files: "src/muz/spacer/spacer_qe_project.cpp"
})

import { invokeLLMClassInvariant} from "./myai.genai.mts";

const headerFile = env.files[0];
const cppFile = env.files[1];
let answer = await invokeLLMClassInvariant(headerFile.content, cppFile.content);

await workspace.writeText(headerFile.filename + ".spec.md", answer);