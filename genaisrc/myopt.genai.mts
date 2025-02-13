script({
    title: "Invoke LLM code optimization",
    files: "code_slices/muz/spacer/orig_spacer_antiunify.cpp_anti_unifier.cpp"
})


async function invokeLLMUpdate(code) {
    const answer = await runPrompt(
        (_) => {
            _.def("CODE", code);
            _.$`
            You are a highly experienced compiler engineer with over 20 years of expertise, 
        specializing in C and C++ programming. Your deep knowledge of best coding practices 
        and software engineering principles enables you to produce robust, efficient, and 
        maintainable code in any scenario.

        Please modify the original code in <CODE> to ensure that it uses best practices for optimal code execution.'    `
        }, {
            system: [],
            systemSafety: false
        }
    )
    console.log(answer.text);
    return answer.text;
}


const inputFile = env.files[0];
const file = await workspace.readText(inputFile);
const answer = await invokeLLMUpdate(file.content);
// Extract the code from the answer by removing ```cpp and ```:
let code = answer.replace(/```cpp/g, "").replace(/```/g, "");
const outputFile = inputFile.filename + ".patch";
await workspace.writeText(outputFile, code);
