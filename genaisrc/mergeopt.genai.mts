script({
    title: "Merge optimizations function changes for a C++ file"
})

// given a source file <src>
// list files in code_slice directory based on that name with extension opt
// replace functions in src by the corresponding ones in the opt files.
// Save into <dst>


import * as fs from 'fs';


function get_functions(captures : QueryCapture[], code : string) {
    return captures.map(({ name, node }) => ({
        code : node.text,
        start : node.startIndex,
        end : node.endIndex,
        name : node.text.split('(')[0].trim()
    }))
}


const inputFile = env.files[0];

const { captures: functions } = await parsers.code(
    inputFile,
    `(function_definition) @function`
);


let funs = get_functions(functions, inputFile.content);

const modifiedFunctions = "slice_" + path.basename(inputFile.filename) + "*.opt";

let inputCode = inputFile.content;
console.log(modifiedFunctions);
const directory_path = path.join("code_slices", modifiedFunctions);
const files = await workspace.findFiles(directory_path);
for (const file of files) {
    console.log(file.filename);
    const code = file.content.match(/```cpp([\s\S]*?)```/);
    if (!code) {
        continue;
    }
    const modifiedFunction = code[1];
    const name = modifiedFunction.split('(')[0].trim();
    console.log(name);
    const fun = funs.find(f => f.name === name);
    if (fun) {
        console.log("Updated function: " + name);
        inputCode = inputCode.replace(fun.code, modifiedFunction);
    }
}

console.log(inputCode);
await workspace.writeText(inputFile.filename + ".opt.cpp", inputCode);