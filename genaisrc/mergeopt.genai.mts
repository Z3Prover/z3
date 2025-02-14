script({
    title: "Merge optimizations function changes for a C++ file"
})

import { mergeFunctions } from "./myai.genai.mts";
const inputFile = env.files[0];
let new_code = await mergeFunctions(inputFile);
await workspace.writeText(inputFile.filename + ".opt.cpp", new_code);