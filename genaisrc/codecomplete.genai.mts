
script({
    title: "Invoke LLM completion for code snippets",
})


import * as fs from 'fs';
import * as path from 'path';


async function runCodePrompt(role, message, code) {
    const answer = await runPrompt(
        (_) => {
            _.def("ROLE", role);
            _.def("REQUEST", message);
            _.def("CODE", code);   
            _.$`Your role is <ROLE>.
            The request is given by <REQUEST> 
            original code snippet:
            <CODE>.`
        }
    )
    console.log(answer.text);
    return answer.text;
}

async function invokeLLMCompletion(code, prefix) {

    let role = `You are a highly experienced compiler engineer with over 20 years of expertise, 
        specializing in C and C++ programming. Your deep knowledge of best coding practices 
        and software engineering principles enables you to produce robust, efficient, and 
        maintainable code in any scenario.`;

    let userMessage = `Please complete the provided C/C++ code to ensure it is compilable and executable. 
        Return only the fully modified code while preserving the original logic. 
        Add any necessary stubs, infer data types, and make essential changes to enable 
        successful compilation and execution. Avoid unnecessary code additions. 
        Ensure the final code is robust, secure, and adheres to best practices.`;

    return runCodePrompt(role, userMessage, code);
}

async function invokeLLMAnalyzer(code, inputFilename, funcName) {
    // Define the llm role
    let role = 
    `You are a highly experienced compiler engineer with over 20 years of expertise, 
    specializing in C and C++ programming. Your deep knowledge of best coding practices 
    and software engineering principles enables you to produce robust, efficient, and 
    maintainable code in any scenario.`;
  
    // Define the message to send
    let userMessage = 
    `Please analyze the provided C/C++ code and identify any potential issues, bugs, or opportunities for performance improvement. For each observation:
    
    - Clearly describe the issue or inefficiency.
    - Explain the reasoning behind the problem or performance bottleneck.
    - Suggest specific code changes or optimizations, including code examples where applicable.
    - Ensure recommendations follow best practices for efficiency, maintainability, and correctness.
    
    At the end of the analysis, provide a detailed report in **Markdown format** summarizing:
    
    1. **Identified Issues and Their Impact:**
       - Description of each issue and its potential consequences.
    
    2. **Suggested Fixes (with Code Examples):**
       - Detailed code snippets showing the recommended improvements.
    
    3. **Performance Improvement Recommendations:**
       - Explanation of optimizations and their expected benefits.

    4. **Additional Insights or Best Practices:**
       - Suggestions to further enhance the code's quality and maintainability.`;

    return runCodePrompt(role, userMessage, code);
  }

async function createGitUpdateRequest(src_directory : string, filename : string, modifiedCode : string) {
    // extract relative path from filename after slice_directory, extract function and source file name.
    // Relative path: code_slices\ast\sls\orig_sls_smt_solver.cpp_updt_params.cpp  file name: orig_sls_smt.cpp
    const regex = /code_slices\\(.*)\\([^_]*)_(.*)\.cpp_(.*)\.cpp/;
    const match = filename.match(regex);
    if (!match) {
        console.log(`Filename does not match expected pattern: ${filename}`);
        return "";
    }
    const [_, relative_path, prefix, fileName, funcName] = match;

    console.log(`Relative path: ${relative_path}  file name: ${fileName}.cpp`);

    const srcFilePath = path.join(src_directory, relative_path, fileName + ".cpp");
    const srcFileContent = await workspace.readText(srcFilePath);

    let role = 
    `You are a highly experienced compiler engineer with over 20 years of expertise, 
    specializing in C and C++ programming. Your deep knowledge of best coding practices 
    and software engineering principles enables you to produce robust, efficient, and 
    maintainable code in any scenario.`;

    const answer = await runPrompt(
        (_) => {
            _.def("ROLE", role);
            _.def("SOURCE", srcFileContent);   
            _.def("REVIEW", modifiedCode);
            _.def("FUNCTION", funcName);
            _.$`Your role is <ROLE>.
                Please create a well-formed git patch based on the source code given in
                <SOURCE> 
                A code analysis is for the method or function <FUNCTION>.
                The analysis is he following:
                <REVIEW>`
        }
    )
    console.log(answer.text);
    return answer.text;
}
  
const input_directory = "code_slices";
const output_directory = "code_slices_analyzed";
const src_directory = "src";
const code_slice_files = await workspace.findFiles("code_slices/**/*.cpp");

let count = 0;
for (const file of code_slice_files) {
    if (path.extname(file.filename) === '.cpp') {
        console.log(`Processing file: ${file.filename}`);

        const regex = /(.*)_(.*)\.cpp_(.*)\.cpp/;
        const match = file.filename.match(regex);

        if (!match) {
            console.log(`Filename does not match expected pattern: ${file.filename}`);
            continue;
        }
        const [_, prefix, fileName, funcName] = match;

        const content = file.content;
        const answer1 = await invokeLLMCompletion(content, fileName);
        const answer2 = await invokeLLMAnalyzer(answer1, fileName, funcName);
        const outputFilePath = path.join(output_directory, fileName + "_" + funcName + ".md");
        await workspace.writeText(outputFilePath, answer2);
        const answer3 = await createGitUpdateRequest(src_directory, file.filename, answer2);
        const outputFilePath2 = path.join(output_directory, fileName + "_" + funcName + ".patch");
        await workspace.writeText(outputFilePath2, answer3);
        ++count;
        if (count > 3)
            break;
    }
}

