function function_name_from_code(code: string) {
    let name = code.split('(')[0].trim();
    name = name
        .replace(/::/g, '_')
        .replace(/ /g, '_')
        .replace(/\*/g, '');
    return name;
}

function tree_sitter_get_functions(captures: QueryCapture[], code: string) {
    return captures.map(({ name, node }) => ({
        code: node.text,
        start: node.startIndex,
        end: node.endIndex,
        name: function_name_from_code(node.text)
    }));
}

function output_name_from_file(inputFile: WorkspaceFile, name: string) {
    let outputFile = "slice_" + path.basename(inputFile.filename) + name + ".cpp";
    return path.join("code_slices", outputFile);
}

export async function splitFunctions(inputFile: WorkspaceFile) {
    const { captures: functions } = await parsers.code(
        inputFile,
        `(function_definition) @function`
    );
    return tree_sitter_get_functions(functions, inputFile.content);
}


export async function saveFunctions(inputFile: WorkspaceFile, funs: { code: string, name: string }[]) {
    for (const fun of funs) {
        let name = function_name_from_code(fun.code);
        console.log(name);
        let outputFile = output_name_from_file(inputFile, name);
        await workspace.writeText(outputFile, `//Extracted ${name} in ${inputFile.filename}\n${fun.code}\n\n`);
    }
}

// given a source file <src>
// list files in code_slice directory based on that name with extension opt
// replace functions in src by the corresponding ones in the opt files.
// Save into <dst>

async function parseOptFunctions(inputFile: WorkspaceFile) {
    const modifiedFunctions = "slice_" + path.basename(inputFile.filename) + "*.opt";
    console.log(modifiedFunctions);
    const directory_path = path.join("code_slices", modifiedFunctions);
    const files = await workspace.findFiles(directory_path);
    let modifiedFunctionsList = [];
    for (const file of files) {
        console.log(file.filename);
        const code = file.content.match(/```cpp([\s\S]*?)```/);
        if (!code) {
            continue;
        }
        const modifiedFunction = code[1];
        modifiedFunctionsList.push(modifiedFunction);
    }
    return modifiedFunctionsList;
}

import * as fs from 'fs';

export async function mergeModifiedFunction(code :string, funs : { code: string, name: string }[], new_code : string) {
    let name = function_name_from_code(new_code);
    let fun = funs.find(f => f.name === name);
    if (fun) {
        console.log("Updated function: " + name);
        code = code.replace(fun.code, new_code);
    }
    return code;
}

async function canCompileCode(inputFile : WorkspaceFile, code : string) {

    // move input file to a temp file
    // move code to the inputFile.filename
    // invoke ninja in the build directory: ninja -b build
    // move the temp file back to the original file
    // return true iff it succeeded

    let tempFile = inputFile.filename + ".tmp";
    let original_content = inputFile.content;
    await workspace.writeText(tempFile, inputFile.content);
    await workspace.writeText(inputFile.filename, code);
    let result = await host.exec(`cmd /k "C:\Program\ Files/Microsoft\ Visual\ Studio/2022/Enterprise/Common7/Tools/VsDevCmd.bat" -arch=x64 & ninja`, { cwd: "build" });

    // await fs.delete(tempFile);
    if (result.exitCode !== 0) {
        await workspace.writeText(inputFile.filename, original_content);
        console.log(result.stderr);
        return false;
    }
    return true;
}

export async function mergeCompileFunction(inputFile : WorkspaceFile, code : string, funs : { code: string, name: string }[], new_code_input : string) {
    let match_new_code = new_code_input.match(/```cpp([\s\S]*?)```/);
    if (!match_new_code) {
        console.log("Invalid new code");
        return code;
    }
    let new_code = match_new_code[1];

    let name = function_name_from_code(new_code);
    let fun = funs.find(f => f.name == name);

    if (!fun) {
        console.log(`Function name '${name}' not found`);
        for (const fun of funs) 
            console.log("'" + fun.name + "'");
        return code;
    }
    console.log("Updated function: " + name);
    let modified_code = code.replace(fun.code, new_code);
    if (code == modified_code) {
        console.log("No change in function: " + name);
        return code;
    }
    let canCompile = await canCompileCode(inputFile, modified_code);
    console.log("Can compile: " + canCompile);
    if (canCompile) 
        return modified_code;
    return code;
}

export async function mergeFunctionsFromList(inputCode: string, funs: { code: string, name: string }[], modifiedFunctionList: string[]) {
    let code = inputCode;
    for (const new_code of modifiedFunctionList) 
        code = await mergeModifiedFunction(code, funs, new_code);    
    return code;
}

export async function mergeFunctions(inputFile: WorkspaceFile) {
    let funs = await splitFunctions(inputFile);
    let modifiedFunctionList = await parseOptFunctions(inputFile);
    return mergeFunctionsFromList(inputFile.content, funs, modifiedFunctionList);
}

export async function invokeLLMOpt(code : string) {
    const answer = await runPrompt(
        (_) => {
            _.def("CODE", code);
            _.$`You are a highly experienced compiler engineer with over 20 years of expertise, 
        specializing in C and C++ programming. Your deep knowledge of best coding practices 
        and software engineering principles enables you to produce robust, efficient, and 
        maintainable code in any scenario.

        Please modify the original code in <CODE> to ensure that it uses best practices for optimal code execution.'    `
        }, {
        system: [],
        systemSafety: false
    }
    );
    return answer.text;
}