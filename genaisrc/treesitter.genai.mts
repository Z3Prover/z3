script({
    title: "Invoke LLM code update",
    files: "src/muz/spacer/spacer_qe_project.cpp"
})

// return function names and source code of the functions 

function get_functions(captures : QueryCapture[], code : string) {
    return captures.map(({ name, node }) => ({
        code : node.text
    }))
}

const inputFile = env.files[0];


const { captures: functions } = await parsers.code(
    inputFile,
    `(function_definition) @function`
);


let funs = get_functions(functions, inputFile.content);

for (const fun of funs) {
    // todo put files in a different directory
    let name = fun.code.split('(')[0].trim();
    name = name
        .replace(/::/g, '_')
        .replace(/ /g, '_');        
    let outputFile = path.basename(inputFile.filename)
            .replace(/\.cpp$/, `.${name}.cpp`)
            .replace(/\.h$/, `.${name}.h`);
    outputFile = "slice_" + outputFile;
    outputFile = path.join("code_slices", outputFile);
        
    await workspace.writeText(outputFile, `//Extracted ${name} in ${inputFile.filename}\n${fun.code}\n\n`);
}

