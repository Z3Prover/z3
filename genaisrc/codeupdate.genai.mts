
script({
    title: "Invoke LLM code update",
})


async function runCodePrompt(role, message, code) {
    const answer = await runPrompt(
        (_) => {
            _.def("ROLE", role);
            _.def("REQUEST", message);
            _.def("CODE", code);   
            _.$`Your role is <ROLE>.
            The request is given by <REQUEST> 
            original code:
            <CODE>.`
        }
    )
    console.log(answer.text);
    return answer.text;
}

async function invokeLLMUpdate(code, inputFile) {
    
    let role = `You are a highly experienced compiler engineer with over 20 years of expertise, 
        specializing in C and C++ programming. Your deep knowledge of best coding practices 
        and software engineering principles enables you to produce robust, efficient, and 
        maintainable code in any scenario.`;

    let userMessage = `Please modify the original code to ensure that it enforces the following:
      - do not use pointer arithmetic for the updates.
      - do not introduce uses of std::vector.
      - only make replacements that are compatible with the ones listed below.
      - add white space between operators:
        For example:
             i=0 
        by 
             i = 0
        For example
             a+b
        by
            a + b
      - remove brackets around single statements:
        For example:
              { break; }
        by 
              break;              
      - replaces uses of for loops using begin(), end() iterator patterns by C++21 style for loops
        For example replace 
            for (auto it = x.begin(), end = x.end(); it != end; ++it) 
        by
            for (auto & e : x) 

        For example, replace
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                expr* arg = a->get_arg(i);
                ...
            }
         by
            for (auto arg : *a) {
                ...
            }
    `;

    return runCodePrompt(role, userMessage, code);
}


const inputFile = env.files[0];
const file = await workspace.readText(inputFile);
const answer = await invokeLLMUpdate(file.content, inputFile);
// Extract the code from the answer by removing ```cpp and ```:
let code = answer.replace(/```cpp/g, "").replace(/```/g, "");
const outputFile = inputFile.filename + ".patch";
await workspace.writeText(outputFile, code);

