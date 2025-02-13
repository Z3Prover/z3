
script({
    title: "Invoke LLM code update",
    files: "src/muz/spacer/spacer_qe_project.cpp"
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

        Please modify the original code in <CODE> to ensure that it enforces the following:
      - do not use pointer arithmetic.
      - do not introduce uses of std::vector.
      - do not remove comments from the code.
      - do not replace for loops over unsigned by for loops over 'auto'.
      - keep comments in the same place. Please.
      - only make replacements that are compatible with the ones listed next:
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
        for example replace:
            else { 
               result = 0; 
            }
        by
            else 
                result = 0; 
        for example replace:
            if (a) { 
                result = 0; 
            }
        by 
            if (a) 
                result = 0;  
      - start else statements on a new line.       
      - replaces uses of for loops using begin(), end() iterator patterns by C++21 style for loops
        For example replace 
            for (auto it = x.begin(), end = x.end(); it != end; ++it) 
        by
            for (auto e : x) 
        or 
            for (auto const& e : x)

        For example, replace
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                expr* arg = a->get_arg(i);
                ...
            }
         by
            for (auto arg : *a) {
                ...
            }
    `
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
