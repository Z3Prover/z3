script({
    title: "Extract functions from files using treesitter",
    files: "src/muz/spacer/spacer_qe_project.cpp"
})

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
        .replace(/ /g, '_')
        .replace(/\*/g, '');
    console.log(name);        
    let outputFile = "slice_" + path.basename(inputFile.filename) + name + ".cpp";
    outputFile = path.join("code_slices", outputFile);
        
    await workspace.writeText(outputFile, `//Extracted ${name} in ${inputFile.filename}\n${fun.code}\n\n`);
}

