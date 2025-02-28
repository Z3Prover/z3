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

export async function mergeModifiedFunction(code: string, funs: { code: string, name: string }[], new_code: string) {
    let name = function_name_from_code(new_code);
    let fun = funs.find(f => f.name === name);
    if (fun) {
        console.log("Updated function: " + name);
        code = code.replace(fun.code, new_code);
    }
    return code;
}

class ShellOutputRef {
    shellOutput: ShellOutput;
}

async function canCompileCode(inputFile: WorkspaceFile, new_code: string, result: ShellOutputRef) {

    //
    // move input file to a temp file
    // move code to the inputFile.filename
    // invoke ninja in the build directory: ninja -b build
    // move the temp file back to the original file
    // return true iff it succeeded
    //

    let tempFile = inputFile.filename + ".tmp";
    let old_code = inputFile.content;
    await workspace.writeText(tempFile, old_code);
    await workspace.writeText(inputFile.filename, new_code);
    result.shellOutput = await host.exec(`cmd /k "C:/Program\ Files/Microsoft\ Visual\ Studio/2022/Enterprise/Common7/Tools/VsDevCmd.bat" -arch=x64 & ninja`, { cwd: "build" });
    await workspace.writeText(inputFile.filename, old_code);
    console.log(result.shellOutput.stdout);
    console.log(result.shellOutput.stderr);
    let has_failed = result.shellOutput.stdout.search("failed");
    if (has_failed != -1) {
        console.log("Failed to compile");
        return false;
    }
    if (result.shellOutput.exitCode == 0) {
        await workspace.writeText(tempFile, new_code);
        return true;
    }
    return false;
}

async function llmFixCompilerErrors(inputFile: WorkspaceFile, new_code: string, result: ShellOutput) {
    let answer = await runPrompt(
        (_) => {
            _.def("CODE", new_code);
            _.def("OUTPUT", result.stderr + result.stdout);
            _.$`You are a highly experienced compiler engineer with over 20 years of expertise, 
        specializing in C and C++ programming. Your deep knowledge of best coding practices 
        and software engineering principles enables you to produce robust, efficient, and 
        maintainable code in any scenario.

        Please modify the original code in <CODE> to ensure that it compiles without any errors.
        The compiler produced the output <OUTPUT> when building <CODE>.
        `
        }, {
        system: [],
        systemSafety: false
    }
    );
    let new_code_input = answer.text;
    let match_new_code = new_code_input.match(/```cpp([\s\S]*?)```/);
    if (!match_new_code) {
        console.log("Invalid new code");
        return new_code;
    }
    return match_new_code[1];
}

export async function mergeCompileFunction(inputFile: WorkspaceFile, code: string, funs: { code: string, name: string }[], new_code_input: string) {
    let match_new_code = new_code_input.match(/```cpp([\s\S]*?)```/);
    if (!match_new_code) {
        console.log("Invalid new code");
        return code;
    }
    let new_code = match_new_code[1];
    let retry_count = 0;

    while (retry_count < 2) {
        let name = function_name_from_code(new_code);
        let fun = funs.find(f => f.name == name);

        if (!fun) {
            console.log(`Function name '${name}' not found`);
            console.log("Available functions: ");
            for (const fun of funs)
                console.log("'" + fun.name + "'");
            console.log(new_code);
            return code;
        }
        console.log("Updated function: " + name);
        let modified_code = code.replace(fun.code, new_code);
        if (code == modified_code) {
            console.log("No change in function: " + name);
            return code;
        }
        let result = new ShellOutputRef();
        let canCompile = await canCompileCode(inputFile, modified_code, result);
        console.log("Can compile: " + canCompile);
        if (canCompile)
            return modified_code;
        if (retry_count > 0)
            break;
        retry_count++;
        new_code = await llmFixCompilerErrors(inputFile, new_code, result.shellOutput);
    }
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

export async function invokeLLMOpt(code: string) {
    const answer = await runPrompt(
        (_) => {
            _.def("CODE", code);
            _.$`You are a highly experienced compiler engineer with over 20 years of expertise, 
        specializing in C and C++ programming. Your deep knowledge of best coding practices 
        and software engineering principles enables you to produce robust, efficient, and 
        maintainable code in any scenario.

        Please modify the original code in <CODE> to ensure that it uses best practices for optimal code execution.
        
        - do use for loops of the form for (auto const& x : container) { ... } instead of for (it = container.begin(); it != container.end(); ++it) { ... }.
        - do not use assert. Instead use SASSERT.
        - do not change function signatures.
        - do not use std::vector.
        - do not add new comments.        
        - do not split functions into multiple functions.`
        }, {
        system: [],
        systemSafety: false
    }
    );
    return answer.text;
}

export async function invokeLLMClassInvariant(header : string, code : string) {
    const answer = await runPrompt(
        (_) => {
            _.def("HEADER", header);
            _.def("CODE", code);
            _.$`You are a highly experienced compiler engineer with over 20 years of expertise, 
        specializing in C and C++ programming. Your deep knowledge of best coding practices 
        and software engineering principles enables you to produce robust, efficient, and 
        maintainable code in any scenario.

        Please create class invariant methods for the classes used in <CODE>.
        The signature of the class invariant methods should be 'bool well_formed()'.
        If the code already has class invariant methods, please do not add new ones.
        Create only code for the class invariant methods and optionally auxiliary helper functions.

        In addition, for each method, provide pre and post conditions.
        A precondition is an assertion that must be true before the method is called.
        Similarly, a postcondition is an assertion that must be true after the method is called.
        Include the well_formed() method in the pre and post conditions if it should be included.      
        `        
        }, {
        system: [],
        systemSafety: false
    }
    );
    return answer.text;
}