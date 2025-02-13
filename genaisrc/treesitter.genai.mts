script({
    title: "Invoke LLM code update",
    files: "src/muz/spacer/spacer_qe_project.cpp"
})



const inputFile = env.files[0];
const { captures } = await parsers.code(inputFile);

// pretty-print tree sitter parse tree of captures:


console.log(JSON.stringify(captures, null,2))
