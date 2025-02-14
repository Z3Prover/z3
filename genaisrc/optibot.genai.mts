
script({
    title: "optimize functions in a file",
    files: "src/muz/spacer/spacer_qe_project.cpp"
})

import { splitFunctions, invokeLLMOpt, mergeFunctionsFromList, mergeCompileFunction} from "./myai.genai.mts";

const inputFile = env.files[0];
let funs = await splitFunctions(inputFile);
let new_code = inputFile.content;
for (const fun of funs) {
    if (fun.code.length < 200) // don't sweat the small stuff
        continue;
    let answer = await invokeLLMOpt(fun.code);
    if (answer)
        new_code = await mergeCompileFunction(inputFile, new_code, funs, answer);
}

await workspace.writeText(inputFile.filename + ".opt.cpp", new_code);
