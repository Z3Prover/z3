type OptionsOrString<TOptions extends string> = (string & {}) | TOptions

type ElementOrArray<T> = T | T[]

interface PromptGenerationConsole {
    log(...data: any[]): void
    warn(...data: any[]): void
    debug(...data: any[]): void
    error(...data: any[]): void
}

type DiagnosticSeverity = "error" | "warning" | "info"

interface Diagnostic {
    filename: string
    range: CharRange
    severity: DiagnosticSeverity
    message: string
    /**
     * error or warning code
     */
    code?: string
}

type Awaitable<T> = T | PromiseLike<T>

interface SerializedError {
    name?: string
    message?: string
    stack?: string
    cause?: unknown
    code?: string
    line?: number
    column?: number
}

interface PromptDefinition {
    /**
     * Based on file name.
     */
    id: string

    /**
     * Something like "Summarize children", show in UI.
     */
    title?: string

    /**
     * Longer description of the prompt. Shows in UI grayed-out.
     */
    description?: string

    /**
     * Groups template in UI
     */
    group?: string

    /**
     * List of tools defined in the script
     */
    defTools?: { id: string; description: string; kind: "tool" | "agent" }[]
}

interface PromptLike extends PromptDefinition, PromptToolsDefinition {
    /**
     * File where the prompt comes from (if any).
     */
    filename?: string

    /**
     * The actual text of the prompt template.
     * Only used for system prompts.
     */
    text?: string

    /**
     * The text of the prompt JS source code.
     */
    jsSource?: string

    /**
     * Resolved system ids
     */
    resolvedSystem?: string[]

    /**
     * Infered input schema for parameters
     */
    inputSchema?: JSONSchemaObject
}

type SystemPromptId = OptionsOrString<
    | "system"
    | "system.agent_data"
    | "system.agent_docs"
    | "system.agent_fs"
    | "system.agent_git"
    | "system.agent_github"
    | "system.agent_interpreter"
    | "system.agent_planner"
    | "system.agent_user_input"
    | "system.agent_video"
    | "system.agent_web"
    | "system.annotations"
    | "system.assistant"
    | "system.changelog"
    | "system.diagrams"
    | "system.diff"
    | "system.english"
    | "system.explanations"
    | "system.files"
    | "system.files_schema"
    | "system.fs_ask_file"
    | "system.fs_data_query"
    | "system.fs_diff_files"
    | "system.fs_find_files"
    | "system.fs_read_file"
    | "system.git"
    | "system.git_diff"
    | "system.git_info"
    | "system.github_actions"
    | "system.github_files"
    | "system.github_info"
    | "system.github_issues"
    | "system.github_pulls"
    | "system.math"
    | "system.md_find_files"
    | "system.md_frontmatter"
    | "system.meta_prompt"
    | "system.meta_schema"
    | "system.node_info"
    | "system.node_test"
    | "system.output_ini"
    | "system.output_json"
    | "system.output_markdown"
    | "system.output_plaintext"
    | "system.output_yaml"
    | "system.planner"
    | "system.python"
    | "system.python_code_interpreter"
    | "system.python_types"
    | "system.retrieval_fuzz_search"
    | "system.retrieval_vector_search"
    | "system.retrieval_web_search"
    | "system.safety_canary_word"
    | "system.safety_harmful_content"
    | "system.safety_jailbreak"
    | "system.safety_protected_material"
    | "system.safety_ungrounded_content_summarization"
    | "system.safety_validate_harmful_content"
    | "system.schema"
    | "system.tasks"
    | "system.technical"
    | "system.tool_calls"
    | "system.tools"
    | "system.transcribe"
    | "system.typescript"
    | "system.user_input"
    | "system.video"
    | "system.vision_ask_images"
    | "system.zero_shot_cot"
>

type SystemToolId = OptionsOrString<
    | "agent_data"
    | "agent_docs"
    | "agent_fs"
    | "agent_git"
    | "agent_github"
    | "agent_interpreter"
    | "agent_planner"
    | "agent_user_input"
    | "agent_video"
    | "agent_web"
    | "fs_ask_file"
    | "fs_data_query"
    | "fs_diff_files"
    | "fs_find_files"
    | "fs_read_file"
    | "git_branch_current"
    | "git_branch_default"
    | "git_branch_list"
    | "git_diff"
    | "git_last_tag"
    | "git_list_commits"
    | "git_status"
    | "github_actions_job_logs_diff"
    | "github_actions_job_logs_get"
    | "github_actions_jobs_list"
    | "github_actions_workflows_list"
    | "github_files_get"
    | "github_files_list"
    | "github_issues_comments_list"
    | "github_issues_get"
    | "github_issues_list"
    | "github_pulls_get"
    | "github_pulls_list"
    | "github_pulls_review_comments_list"
    | "math_eval"
    | "md_find_files"
    | "md_read_frontmatter"
    | "meta_prompt"
    | "meta_schema"
    | "node_test"
    | "python_code_interpreter_copy_files_to_container"
    | "python_code_interpreter_read_file"
    | "python_code_interpreter_run"
    | "retrieval_fuzz_search"
    | "retrieval_vector_search"
    | "retrieval_web_search"
    | "transcribe"
    | "user_input_confirm"
    | "user_input_select"
    | "user_input_text"
    | "video_extract_audio"
    | "video_extract_clip"
    | "video_extract_frames"
    | "video_probe"
    | "vision_ask_images"
>

type FileMergeHandler = (
    filename: string,
    label: string,
    before: string,
    generated: string
) => Awaitable<string>

interface PromptOutputProcessorResult {
    /**
     * Updated text
     */
    text?: string
    /**
     * Generated files from the output
     */
    files?: Record<string, string>

    /**
     * User defined errors
     */
    annotations?: Diagnostic[]
}

type PromptOutputProcessorHandler = (
    output: GenerationOutput
) =>
    | PromptOutputProcessorResult
    | Promise<PromptOutputProcessorResult>
    | undefined
    | Promise<undefined>
    | void
    | Promise<void>

type PromptTemplateResponseType =
    | "text"
    | "json"
    | "yaml"
    | "markdown"
    | "json_object"
    | "json_schema"
    | undefined

type ModelType = OptionsOrString<
    | "large"
    | "small"
    | "long"
    | "vision"
    | "vision_small"
    | "reasoning"
    | "reasoning_small"
    | "openai:gpt-4o"
    | "openai:gpt-4o-mini"
    | "openai:gpt-3.5-turbo"
    | "openai:o1"
    | "openai:o1-mini"
    | "openai:o1-preview"
    | "github:o3-mini"
    | "github:gpt-4o"
    | "github:gpt-4o-mini"
    | "github:o1"
    | "github:o1-mini"
    | "github:o1-preview"
    | "github:o3-mini"
    | "github:AI21-Jamba-1.5-Large"
    | "github:AI21-Jamba-1-5-Mini"
    | "github:DeepSeek-R1"
    | "github:Phi-4"
    | "azure:gpt-4o"
    | "azure:gpt-4o-mini"
    | "azure:o1"
    | "azure:o1-mini"
    | "azure:o1-preview"
    | "azure:o3-mini"
    | "ollama:marco-o1"
    | "ollama:tulu3"
    | "ollama:athene-v2"
    | "ollama:opencoder"
    | "ollama:qwen2.5-coder"
    | "ollama:llama3.2-vision"
    | "ollama:llama3.2"
    | "ollama:phi4"
    | "ollama:phi3.5"
    | "ollama:deepseek-r1:1.5b"
    | "ollama:deepseek-r1:7b"
    | "ollama:olmo2:7b"
    | "ollama:command-r7b:7b"
    | "anthropic:claude-3-5-sonnet-20240620"
    | "anthropic:claude-3-opus-20240229"
    | "anthropic:claude-3-sonnet-20240229"
    | "anthropic:claude-3-haiku-20240307"
    | "anthropic:claude-2.1"
    | "anthropic:claude-instant-1.2"
    | "anthropic_bedrock:anthropic.claude-3-opus-20240229-v1:0"
    | "anthropic_bedrock:anthropic.claude-3-sonnet-20240229-v1:0"
    | "anthropic_bedrock:anthropic.claude-3-haiku-20240307-v1:0"
    | "huggingface:microsoft/Phi-3-mini-4k-instruct"
    | "jan:llama3.2-3b-instruct"
    | "google:gemini-2.0-flash-exp"
    | "google:gemini-2.0-flash-thinking-exp-1219"
    | "google:gemini-1.5-flash"
    | "google:gemini-1.5-flash-latest"
    | "google:gemini-1.5-flash-8b"
    | "google:gemini-1.5-flash-8b-latest"
    | "google:gemini-1.5-pro"
    | "google:gemini-1.5-pro-latest"
    | "mistral:mistral-large-latest"
    | "mistral:mistral-small-latest"
    | "mistral:pixtral-large-latest"
    | "mistral:codestral-latest"
    | "mistral:nemo"
    | "alibaba:qwen-turbo"
    | "alibaba:qwen-max"
    | "alibaba:qwen-plus"
    | "alibaba:qwen2-72b-instruct"
    | "alibaba:qwen2-57b-a14b-instruct"
    | "deepseek:deepseek-chat"
    | "transformers:onnx-community/Qwen2.5-0.5B-Instruct:q4"
    | "transformers:HuggingFaceTB/SmolLM2-1.7B-Instruct:q4f16"
>

type ModelSmallType = OptionsOrString<
    | "openai:gpt-4o-mini"
    | "github:gpt-4o-mini"
    | "azure:gpt-4o-mini"
    | "openai:gpt-3.5-turbo"
    | "github:Phi-3-5-mini-instruct"
    | "github:AI21-Jamba-1-5-Mini"
>

type ModelVisionType = OptionsOrString<
    "openai:gpt-4o" | "github:gpt-4o" | "azure:gpt-4o" | "azure:gpt-4o-mini"
>

type ModelTranscriptionType = OptionsOrString<
    "openai:whisper-1" | "whisperasr:default"
>

type ModelProviderType = OptionsOrString<
    | "openai"
    | "azure"
    | "azure_serverless"
    | "azure_serverless_models"
    | "anthropic"
    | "anthropic_bedrock"
    | "google"
    | "huggingface"
    | "mistral"
    | "alibaba"
    | "github"
    | "transformers"
    | "ollama"
    | "lmstudio"
    | "jan"
    | "llamafile"
    | "litellm"
    | "github_copilot_chat"
    | "deepseek"
>

interface ModelConnectionOptions {
    /**
     * Which LLM model by default or for the `large` alias.
     */
    model?: ModelType
}

interface ModelAliasesOptions {
    /**
     * Configure the `small` model alias.
     */
    smallModel?: ModelSmallType

    /**
     * Configure the `vision` model alias.
     */
    visionModel?: ModelVisionType
}

interface ModelOptions extends ModelConnectionOptions, ModelTemplateOptions {
    /**
     * Temperature to use. Higher temperature means more hallucination/creativity.
     * Range 0.0-2.0.
     *
     * @default 0.2
     */
    temperature?: number

    /**
     * Some reasoning model support a reasoning effort parameter.
     */
    reasoningEffort?: "high" | "medium" | "low"

    /**
     * A list of keywords that should be found in the output.
     */
    choices?: ElementOrArray<
        string | { token: string | number; weight?: number }
    >

    /**
     * Returns the log probabilities of the each tokens. Not supported in all models.
     */
    logprobs?: boolean

    /**
     * Number of alternate token logprobs to generate, up to 5. Enables logprobs.
     */
    topLogprobs?: number

    /**
     * Specifies the type of output. Default is plain text.
     * - `text` enables plain text mode (through system prompts)
     * - `json` enables JSON mode (through system prompts)
     * - `yaml` enables YAML mode (through system prompts)
     * - `json_object` enables JSON mode (native)
     * - `json_schema` enables structured outputs (native)
     * Use `responseSchema` to specify an output schema.
     */
    responseType?: PromptTemplateResponseType

    /**
     * JSON object schema for the output. Enables the `json_object` output mode by default.
     */
    responseSchema?: PromptParametersSchema | JSONSchema

    /**
     * “Top_p” or nucleus sampling is a setting that decides how many possible words to consider.
     * A high “top_p” value means the model looks at more possible words, even the less likely ones,
     * which makes the generated text more diverse.
     */
    topP?: number

    /**
     * Maximum number of completion tokens
     *
     */
    maxTokens?: number

    /**
     * Maximum number of tool calls to make.
     */
    maxToolCalls?: number

    /**
     * Maximum number of data repairs to attempt.
     */
    maxDataRepairs?: number

    /**
     * A deterministic integer seed to use for the model.
     */
    seed?: number

    /**
     * By default, LLM queries are not cached. If true, the LLM request will be cached. Use a string to override the default cache name
     */
    cache?: boolean | string

    /**
     * A list of model ids and their maximum number of concurrent requests.
     */
    modelConcurrency?: Record<string, number>
}

interface EmbeddingsModelConnectionOptions {
    /**
     * LLM model to use for embeddings.
     */
    embeddingsModel?: OptionsOrString<
        "openai:text-embedding-3-small",
        "openai:text-embedding-3-large",
        "openai:text-embedding-ada-002",
        "github:text-embedding-3-small",
        "github:text-embedding-3-large",
        "ollama:nomic-embed-text"
    >
}

interface EmbeddingsModelOptions extends EmbeddingsModelConnectionOptions {}

interface PromptSystemOptions {
    /**
     * List of system script ids used by the prompt.
     */
    system?: ElementOrArray<SystemPromptId>

    /**
     * List of tools used by the prompt.
     */
    tools?: ElementOrArray<SystemToolId>

    /**
     * List of system to exclude from the prompt.
     */
    excludedSystem?: ElementOrArray<SystemPromptId>
}

interface ScriptRuntimeOptions extends LineNumberingOptions {
    /**
     * Secrets required by the prompt
     */
    secrets?: string[]
}

type PromptJSONParameterType<T> = T & { required?: boolean }

type PromptParameterType =
    | string
    | number
    | boolean
    | object
    | PromptJSONParameterType<JSONSchemaNumber>
    | PromptJSONParameterType<JSONSchemaString>
    | PromptJSONParameterType<JSONSchemaBoolean>
type PromptParametersSchema = Record<
    string,
    PromptParameterType | [PromptParameterType]
>
type PromptParameters = Record<string, string | number | boolean | object>

type PromptAssertion = {
    // How heavily to weigh the assertion. Defaults to 1.0
    weight?: number
    /**
     * The transformation to apply to the output before checking the assertion.
     */
    transform?: string
} & (
    | {
          // type of assertion
          type:
              | "icontains"
              | "not-icontains"
              | "equals"
              | "not-equals"
              | "starts-with"
              | "not-starts-with"
          // The expected value
          value: string
      }
    | {
          // type of assertion
          type:
              | "contains-all"
              | "not-contains-all"
              | "contains-any"
              | "not-contains-any"
              | "icontains-all"
              | "not-icontains-all"
          // The expected values
          value: string[]
      }
    | {
          // type of assertion
          type: "levenshtein" | "not-levenshtein"
          // The expected value
          value: string
          // The threshold value
          threshold?: number
      }
    | {
          type: "javascript"
          /**
           * JavaScript expression to evaluate.
           */
          value: string
          /**
           * Optional threshold if the javascript expression returns a number
           */
          threshold?: number
      }
)

interface PromptTest {
    /**
     * Short name of the test
     */
    name?: string
    /**
     * Description of the test.
     */
    description?: string
    /**
     * List of files to apply the test to.
     */
    files?: string | string[]
    /**
     * List of in-memory files to apply the test to.
     */
    workspaceFiles?: WorkspaceFile | WorkspaceFile[]
    /**
     * Extra set of variables for this scenario
     */
    vars?: Record<string, string | boolean | number>
    /**
     * LLM output matches a given rubric, using a Language Model to grade output.
     */
    rubrics?: string | string[]
    /**
     * LLM output adheres to the given facts, using Factuality method from OpenAI evaluation.
     */
    facts?: string | string[]
    /**
     * List of keywords that should be contained in the LLM output.
     */
    keywords?: string | string[]
    /**
     * List of keywords that should not be contained in the LLM output.
     */
    forbidden?: string | string[]
    /**
     * Additional deterministic assertions.
     */
    asserts?: PromptAssertion | PromptAssertion[]

    /**
     * Determines what kind of output is sent back to the test engine. Default is "text".
     */
    format?: "text" | "json"
}

/**
 * Configure promptfoo redteam plugins
 */
interface PromptRedteam {
    /**
     * The `purpose` property is used to guide the attack generation process. It should be as clear and specific as possible.
     * Include the following information:
     * - Who the user is and their relationship to the company
     * - What data the user has access to
     * - What data the user does not have access to
     * - What actions the user can perform
     * - What actions the user cannot perform
     * - What systems the agent has access to
     * @link https://www.promptfoo.dev/docs/red-team/troubleshooting/attack-generation/
     */
    purpose: string

    /**
     * Redteam identifer used for reporting purposes
     */
    label?: string

    /**
     * Default number of inputs to generate for each plugin.
     * The total number of tests will be `(numTests * plugins.length * (1 + strategies.length) * languages.length)`
     * Languages.length is 1 by default, but is added when the multilingual strategy is used.
     */
    numTests?: number

    /**
     * List of languages to target. Default is English.
     */
    language?: string

    /**
     * Red team plugin list
     * @link https://www.promptfoo.dev/docs/red-team/owasp-llm-top-10/
     */
    plugins?: ElementOrArray<
        OptionsOrString<
            | "default"
            | "nist:ai:measure"
            | "owasp:llm"
            | "owasp:api"
            | "mitre:atlas"
            | "owasp:llm:01"
            | "owasp:llm:02"
            | "owasp:llm:04"
            | "owasp:llm:06"
            | "owasp:llm:09"
            | "contracts"
            | "divergent-repetition"
            | "excessive-agency"
            | "hallucination"
            | "harmful:chemical-biological-weapons"
            | "harmful:child-exploitation"
            | "harmful:copyright-violations"
            | "harmful:cybercrime"
            | "harmful:cybercrime:malicious-code"
            | "harmful:graphic-content"
            | "harmful:harassment-bullying"
            | "harmful:hate"
            | "harmful:illegal-activities"
            | "harmful:illegal-drugs"
            | "harmful:illegal-drugs:meth"
            | "harmful:indiscriminate-weapons"
            | "harmful:insults"
            | "harmful:intellectual-property"
            | "harmful:misinformation-disinformation"
            | "harmful:non-violent-crime"
            | "harmful:privacy"
            | "harmful:profanity"
            | "harmful:radicalization"
            | "harmful:self-harm"
            | "harmful:sex-crime"
            | "harmful:sexual-content"
            | "harmful:specialized-advice"
            | "harmful:unsafe-practices"
            | "harmful:violent-crime"
            | "harmful:weapons:ied"
            | "hijacking"
            | "pii:api-db"
            | "pii:direct"
            | "pii:session"
            | "pii:social"
            | "politics"
        >
    >

    /**
     * Adversary prompt generation strategies
     */
    strategies?: ElementOrArray<
        OptionsOrString<
            | "default"
            | "basic"
            | "jailbreak"
            | "jailbreak:composite"
            | "base64"
            | "jailbreak"
            | "prompt-injection"
        >
    >
}

interface ContentSafetyOptions {
    contentSafety?: ContentSafetyProvider
}

/**
 * Different ways to render a fence block.
 */
type FenceFormat = "markdown" | "xml" | "none"

interface FenceFormatOptions {
    /**
     * Formatting of code sections
     */
    fenceFormat?: FenceFormat
}

interface ModelTemplateOptions extends FenceFormatOptions {
    /**
     * Budget of tokens to apply the prompt flex renderer.
     */
    flexTokens?: number
}

interface PromptScript
    extends PromptLike,
        ModelOptions,
        ModelAliasesOptions,
        PromptSystemOptions,
        EmbeddingsModelOptions,
        ContentSafetyOptions,
        ScriptRuntimeOptions {
    /**
     * Which provider to prefer when picking a model.
     */
    provider?: ModelProviderType

    /**
     * Additional template parameters that will populate `env.vars`
     */
    parameters?: PromptParametersSchema

    /**
     * A file path or list of file paths or globs.
     * The content of these files will be by the files selected in the UI by the user or the cli arguments.
     */
    files?: ElementOrArray<string>

    /**
     * A comma separated list of file extensions to accept.
     */
    accept?: string

    /**
     * Extra variable values that can be used to configure system prompts.
     */
    vars?: Record<string, string>

    /**
     * Tests to validate this script.
     */
    tests?: ElementOrArray<string | PromptTest>

    /**
     * LLM vulnerability checks
     */
    redteam?: PromptRedteam

    /**
     * Don't show it to the user in lists. Template `system.*` are automatically unlisted.
     */
    unlisted?: boolean

    /**
     * Set if this is a system prompt.
     */
    isSystem?: boolean
}
/**
 * Represent a workspace file and optional content.
 */
interface WorkspaceFile {
    /**
     * Name of the file, relative to project root.
     */
    filename: string

    /**
     * Content mime-type if known
     */
    type?: string

    /**
     * Encoding of the content
     */
    encoding?: "base64"

    /**
     * Content of the file.
     */
    content?: string

    /**
     * Size in bytes if known
     */
    size?: number
}

interface WorkspaceFileWithScore extends WorkspaceFile {
    /**
     * Score allocated by search algorithm
     */
    score?: number
}

interface ToolDefinition {
    /**
     * The name of the function to be called. Must be a-z, A-Z, 0-9, or contain
     * underscores and dashes, with a maximum length of 64.
     */
    name: string

    /**
     * A description of what the function does, used by the model to choose when and
     * how to call the function.
     */
    description?: string

    /**
     * The parameters the functions accepts, described as a JSON Schema object. See the
     * [guide](https://platform.openai.com/docs/guides/text-generation/function-calling)
     * for examples, and the
     * [JSON Schema reference](https://json-schema.org/understanding-json-schema/) for
     * documentation about the format.
     *
     * Omitting `parameters` defines a function with an empty parameter list.
     */
    parameters?: JSONSchema
}

/**
 * Interface representing an output trace with various logging and tracing methods.
 * Extends the `ToolCallTrace` interface.
 */
interface OutputTrace extends ToolCallTrace {
    /**
     * Logs a heading message at the specified level.
     * @param level - The level of the heading.
     * @param message - The heading message.
     */
    heading(level: number, message: string): void

    /**
     * Logs an image with an optional caption.
     * @param url - The URL of the image.
     * @param caption - The optional caption for the image.
     */
    image(url: string, caption?: string): void

    /**
     * Logs a markdown table
     * @param rows
     */
    table(rows: object[]): void

    /**
     * Logs a result item with a boolean value and a message.
     * @param value - The boolean value of the result item.
     * @param message - The message for the result item.
     */
    resultItem(value: boolean, message: string): void

    /**
     * Starts a trace with details in markdown format.
     * @param title - The title of the trace.
     * @param options - Optional settings for the trace.
     * @returns A `MarkdownTrace` instance.
     */
    startTraceDetails(
        title: string,
        options?: { expanded?: boolean }
    ): MarkdownTrace

    /**
     * Appends content to the trace.
     * @param value - The content to append.
     */
    appendContent(value: string): void

    /**
     * Starts a details section in the trace.
     * @param title - The title of the details section.
     * @param options - Optional settings for the details section.
     */
    startDetails(
        title: string,
        options?: { success?: boolean; expanded?: boolean }
    ): void

    /**
     * Ends the current details section in the trace.
     */
    endDetails(): void

    /**
     * Logs a video with a name, file path, and optional alt text.
     * @param name - The name of the video.
     * @param filepath - The file path of the video.
     * @param alt - The optional alt text for the video.
     */
    video(name: string, filepath: string, alt?: string): void

    /**
     * Logs an audio file
     * @param name
     * @param filepath
     * @param alt
     */
    audio(name: string, filepath: string, alt?: string): void

    /**
     * Logs a details section with a title and body.
     * @param title - The title of the details section.
     * @param body - The body content of the details section, can be a string or an object.
     * @param options - Optional settings for the details section.
     */
    details(
        title: string,
        body: string | object,
        options?: { success?: boolean; expanded?: boolean }
    ): void

    /**
     * Logs a fenced details section with a title, body, and optional content type.
     * @param title - The title of the details section.
     * @param body - The body content of the details section, can be a string or an object.
     * @param contentType - The optional content type of the body.
     * @param options - Optional settings for the details section.
     */
    detailsFenced(
        title: string,
        body: string | object,
        contentType?: string,
        options?: { expanded?: boolean }
    ): void

    /**
     * Logs an item with a name, value, and optional unit.
     * @param name - The name of the item.
     * @param value - The value of the item.
     * @param unit - The optional unit of the value.
     */
    itemValue(name: string, value: any, unit?: string): void

    /**
     * Logs a warning message.
     * @param msg - The warning message to log.
     */
    warn(msg: string): void

    /**
     * Logs a caution message.
     * @param msg - The caution message to log.
     */
    caution(msg: string): void

    /**
     * Logs a note message.
     * @param msg - The note message to log.
     */
    note(msg: string): void
}

/**
 * Interface representing a tool call trace for logging various types of messages.
 */
interface ToolCallTrace {
    /**
     * Logs a general message.
     * @param message - The message to log.
     */
    log(message: string): void

    /**
     * Logs an item message.
     * @param message - The item message to log.
     */
    item(message: string): void

    /**
     * Logs a tip message.
     * @param message - The tip message to log.
     */
    tip(message: string): void

    /**
     * Logs a fenced message, optionally specifying the content type.
     * @param message - The fenced message to log.
     * @param contentType - The optional content type of the message.
     */
    fence(message: string | unknown, contentType?: string): void
}

/**
 * Position (line, character) in a file. Both are 0-based.
 */
type CharPosition = [number, number]

/**
 * Describes a run of text.
 */
type CharRange = [CharPosition, CharPosition]

/**
 * 0-based line numbers.
 */
type LineRange = [number, number]

interface FileEdit {
    type: string
    filename: string
    label?: string
    validated?: boolean
}

interface ReplaceEdit extends FileEdit {
    type: "replace"
    range: CharRange | LineRange
    text: string
}

interface InsertEdit extends FileEdit {
    type: "insert"
    pos: CharPosition | number
    text: string
}

interface DeleteEdit extends FileEdit {
    type: "delete"
    range: CharRange | LineRange
}

interface CreateFileEdit extends FileEdit {
    type: "createfile"
    overwrite?: boolean
    ignoreIfExists?: boolean
    text: string
}

type Edits = InsertEdit | ReplaceEdit | DeleteEdit | CreateFileEdit

interface ToolCallContent {
    type?: "content"
    content: string
    edits?: Edits[]
}

type ToolCallOutput =
    | string
    | number
    | boolean
    | ToolCallContent
    | ShellOutput
    | WorkspaceFile
    | RunPromptResult
    | SerializedError
    | undefined

interface WorkspaceFileCache<K, V> {
    /**
     * Gets the value associated with the key, or undefined if there is none.
     * @param key
     */
    get(key: K): Promise<V | undefined>
    /**
     * Sets the value associated with the key.
     * @param key
     * @param value
     */
    set(key: K, value: V): Promise<void>

    /**
     * List of keys
     */
    keys(): Promise<K[]>

    /**
     * List the values in the cache.
     */
    values(): Promise<V[]>
}

interface WorkspaceGrepOptions {
    /**
     * List of paths to
     */
    path?: ElementOrArray<string>
    /**
     * list of filename globs to search. !-prefixed globs are excluded. ** are not supported.
     */
    glob?: ElementOrArray<string>
    /**
     * Set to false to skip read text content. True by default
     */
    readText?: boolean
}

interface WorkspaceGrepResult {
    files: WorkspaceFile[]
    matches: WorkspaceFile[]
}

interface INIParseOptions {
    defaultValue?: any
}

interface FindFilesOptions {
    /** Glob patterns to ignore */
    ignore?: ElementOrArray<string>
    /**
     * Set to false to skip read text content. True by default
     */
    readText?: boolean
}

interface FileStats {
    /**
     * Size of the file in bytes
     */
    size: number
    mode: number
}

interface WorkspaceFileSystem {
    /**
     * Searches for files using the glob pattern and returns a list of files.
     * Ignore `.env` files and apply `.gitignore` if present.
     * @param glob
     */
    findFiles(
        glob: string,
        options?: FindFilesOptions
    ): Promise<WorkspaceFile[]>

    /**
     * Performs a grep search over the files in the workspace
     * @param query
     * @param globs
     */
    grep(
        query: string | RegExp,
        options?: WorkspaceGrepOptions
    ): Promise<WorkspaceGrepResult>
    grep(
        query: string | RegExp,
        glob: string,
        options?: Omit<WorkspaceGrepOptions, "path" | "glob">
    ): Promise<WorkspaceGrepResult>

    /**
     * Reads metadata information about the file. Returns undefined if the file does not exist.
     * @param filename
     */
    stat(filename: string): Promise<FileStats>

    /**
     * Reads the content of a file as text
     * @param path
     */
    readText(path: string | Awaitable<WorkspaceFile>): Promise<WorkspaceFile>

    /**
     * Reads the content of a file and parses to JSON, using the JSON5 parser.
     * @param path
     */
    readJSON(path: string | Awaitable<WorkspaceFile>): Promise<any>

    /**
     * Reads the content of a file and parses to YAML.
     * @param path
     */
    readYAML(path: string | Awaitable<WorkspaceFile>): Promise<any>

    /**
     * Reads the content of a file and parses to XML, using the XML parser.
     */
    readXML(
        path: string | Awaitable<WorkspaceFile>,
        options?: XMLParseOptions
    ): Promise<any>

    /**
     * Reads the content of a CSV file.
     * @param path
     */
    readCSV<T extends object>(
        path: string | Awaitable<WorkspaceFile>,
        options?: CSVParseOptions
    ): Promise<T[]>

    /**
     * Reads the content of a file and parses to INI
     */
    readINI(
        path: string | Awaitable<WorkspaceFile>,
        options?: INIParseOptions
    ): Promise<any>

    /**
     * Reads the content of a file and attempts to parse it as data.
     * @param path
     * @param options
     */
    readData(
        path: string | Awaitable<WorkspaceFile>,
        options?: CSVParseOptions & INIParseOptions & XMLParseOptions
    ): Promise<any>

    /**
     * Writes a file as text to the file system
     * @param path
     * @param content
     */
    writeText(path: string, content: string): Promise<void>

    /**
     * Caches a buffer to file and returns the unique file name
     * @param bytes
     */
    writeCached(
        bytes: BufferLike,
        options?: { scope?: "workspace" | "run" }
    ): Promise<string>

    /**
     * Copies a file between two paths
     * @param source
     * @param destination
     */
    copyFile(source: string, destination: string): Promise<void>

    /**
     * Opens a file-backed key-value cache for the given cache name.
     * The cache is persisted across runs of the script. Entries are dropped when the cache grows too large.
     * @param cacheName
     */
    cache<K = any, V = any>(
        cacheName: string
    ): Promise<WorkspaceFileCache<K, V>>
}

interface ToolCallContext {
    log(message: string): void
    debug(message: string): void
    trace: ToolCallTrace
}

interface ToolCallback {
    spec: ToolDefinition
    options?: DefToolOptions
    impl: (
        args: { context: ToolCallContext } & Record<string, any>
    ) => Awaitable<ToolCallOutput>
}

type AgenticToolCallback = Omit<ToolCallback, "spec"> & {
    spec: Omit<ToolDefinition, "parameters"> & {
        parameters: Record<string, any>
    }
}

interface AgenticToolProviderCallback {
    functions: Iterable<AgenticToolCallback>
}

type ChatParticipantHandler = (
    context: ChatTurnGenerationContext,
    messages: ChatCompletionMessageParam[]
) => Awaitable<{ messages?: ChatCompletionMessageParam[] } | undefined | void>

interface ChatParticipantOptions {
    label?: string
}

interface ChatParticipant {
    generator: ChatParticipantHandler
    options: ChatParticipantOptions
}

/**
 * A set of text extracted from the context of the prompt execution
 */
interface ExpansionVariables {
    /**
     * Directory where the prompt is executed
     */
    dir: string

    /**
     * Directory where output files (trace, output) are created
     */
    runDir: string

    /**
     * List of linked files parsed in context
     */
    files: WorkspaceFile[]

    /**
     * User defined variables
     */
    vars: Record<string, string | boolean | number | object | any> & {
        /**
         * When running in GitHub Copilot Chat, the current user prompt
         */
        question?: string
        /**
         * When running in GitHub Copilot Chat, the current chat history
         */
        "copilot.history"?: (HistoryMessageUser | HistoryMessageAssistant)[]
        /**
         * When running in GitHub Copilot Chat, the current editor content
         */
        "copilot.editor"?: string
        /**
         * When running in GitHub Copilot Chat, the current selection
         */
        "copilot.selection"?: string
        /**
         * When running in GitHub Copilot Chat, the current terminal content
         */
        "copilot.terminalSelection"?: string
    }

    /**
     * List of secrets used by the prompt, must be registered in `genaiscript`.
     */
    secrets: Record<string, string>

    /**
     * Root prompt generation context
     */
    generator: ChatGenerationContext

    /**
     * Output trace builder
     */
    output: OutputTrace

    /**
     * Resolved metadata
     */
    meta: PromptDefinition & ModelConnectionOptions
}

type MakeOptional<T, P extends keyof T> = Partial<Pick<T, P>> & Omit<T, P>

type PromptArgs = Omit<
    PromptScript,
    "text" | "id" | "jsSource" | "defTools" | "resolvedSystem"
>

type PromptSystemArgs = Omit<
    PromptArgs,
    | "model"
    | "embeddingsModel"
    | "temperature"
    | "topP"
    | "maxTokens"
    | "seed"
    | "tests"
    | "responseLanguage"
    | "responseType"
    | "responseSchema"
    | "files"
    | "modelConcurrency"
    | "redteam"
>

type StringLike = string | WorkspaceFile | WorkspaceFile[]

interface LineNumberingOptions {
    /**
     * Prepend each line with a line numbers. Helps with generating diffs.
     */
    lineNumbers?: boolean
}

interface FenceOptions extends LineNumberingOptions, FenceFormatOptions {
    /**
     * Language of the fenced code block. Defaults to "markdown".
     */
    language?:
        | "markdown"
        | "json"
        | "yaml"
        | "javascript"
        | "typescript"
        | "python"
        | "shell"
        | "toml"
        | string

    /**
     * JSON schema identifier
     */
    schema?: string
}

type PromptCacheControlType = "ephemeral"

interface ContextExpansionOptions {
    /**
     * Specifies an maximum of estimated tokens for this entry; after which it will be truncated.
     */
    maxTokens?: number

    /*
     * Value that is conceptually similar to a zIndex (higher number == higher priority).
     * If a rendered prompt has more message tokens than can fit into the available context window, the prompt renderer prunes messages with the lowest priority from the ChatMessages result, preserving the order in which they were declared. This means your extension code can safely declare TSX components for potentially large pieces of context like conversation history and codebase context.
     */
    priority?: number

    /**
     * Controls the proportion of tokens allocated from the container's budget to this element.
     * It defaults to 1 on all elements.
     */
    flex?: number

    /**
     * Caching policy for this text. `ephemeral` means the prefix can be cached for a short amount of time.
     */
    cacheControl?: PromptCacheControlType
}

interface RangeOptions {
    /**
     * The inclusive start of the line range, with a 1-based index
     */
    lineStart?: number
    /**
     * The inclusive end of the line range, with a 1-based index
     */
    lineEnd?: number
}

interface FileFilterOptions {
    /**
     * Filename filter based on file suffix. Case insensitive.
     */
    endsWith?: ElementOrArray<string>

    /**
     * Filename filter using glob syntax.
     */
    glob?: ElementOrArray<string>
}

interface ContentSafetyOptions {
    /**
     * Runs the default content safety validator
     * to prevent prompt injection.
     */
    detectPromptInjection?: "always" | "available" | boolean

    /**
     * Policy to inject builtin system prompts. See to `false` prevent automatically injecting.
     */
    systemSafety?: "default" | boolean

    /**
     * Policy to disable secret scanning when communicating with the LLM.
     * Set to `false` to disable.
     */
    secretScanning?: boolean
}

interface DefOptions
    extends FenceOptions,
        ContextExpansionOptions,
        DataFilter,
        RangeOptions,
        FileFilterOptions,
        ContentSafetyOptions {
    /**
     * By default, throws an error if the value in def is empty.
     */
    ignoreEmpty?: boolean

    /**
     * The content of the def is a predicted output.
     * This setting disables line numbers.
     */
    prediction?: boolean
}

/**
 * Options for the `defDiff` command.
 */
interface DefDiffOptions
    extends ContextExpansionOptions,
        FenceFormatOptions,
        LineNumberingOptions {}

interface DefImagesOptions {
    /**
     * A "low" detail image is always downsampled to 512x512 pixels.
     */
    detail?: "high" | "low"
    /**
     * Crops the image to the specified region.
     */
    crop?: { x?: number; y?: number; w?: number; h?: number }
    /**
     * Auto cropping same color on the edges of the image
     */
    autoCrop?: boolean
    /**
     * Applies a scaling factor to the image after cropping.
     */
    scale?: number
    /**
     * Rotates the image by the specified number of degrees.
     */
    rotate?: number
    /**
     * Maximum width of the image. Applied after rotation.
     */
    maxWidth?: number
    /**
     * Maximum height of the image. Applied after rotation.
     */
    maxHeight?: number
    /**
     * Removes colour from the image using ITU Rec 709 luminance values
     */
    greyscale?: boolean
    /**
     * Flips the image horizontally and/or vertically.
     */
    flip?: { horizontal?: boolean; vertical?: boolean }
    /**
     * Selects the first N elements from the data
     */
    sliceHead?: number
    /**
     * Selects the last N elements from the data
     */
    sliceTail?: number
    /**
     * Selects the a random sample of N items in the collection.
     */
    sliceSample?: number
    /**
     * Renders all images in a single tiled image
     */
    tiled?: boolean

    /**
     * By default, throws an error if no images are passed.
     */
    ignoreEmpty?: boolean
}

type JSONSchemaTypeName =
    | "string"
    | "number"
    | "integer"
    | "boolean"
    | "object"
    | "array"
    | "null"

type JSONSchemaSimpleType =
    | JSONSchemaString
    | JSONSchemaNumber
    | JSONSchemaBoolean
    | JSONSchemaObject
    | JSONSchemaArray

type JSONSchemaType = JSONSchemaSimpleType | JSONSchemaAnyOf | null

interface JSONSchemaAnyOf {
    anyOf: JSONSchemaType[]
}

interface JSONSchemaDescripted {
    /**
     * A short description of the property
     */
    title?: string
    /**
     * A clear description of the property.
     */
    description?: string
}

interface JSONSchemaString extends JSONSchemaDescripted {
    type: "string"
    uiType?: "textarea"
    enum?: string[]
    default?: string
    pattern?: string
}

interface JSONSchemaNumber extends JSONSchemaDescripted {
    type: "number" | "integer"
    default?: number
    minimum?: number
    exclusiveMinimum?: number
    maximum?: number
    exclusiveMaximum?: number
}

interface JSONSchemaBoolean extends JSONSchemaDescripted {
    type: "boolean"
    default?: boolean
}

interface JSONSchemaObject extends JSONSchemaDescripted {
    $schema?: string
    type: "object"
    properties?: {
        [key: string]: JSONSchemaType
    }
    required?: string[]
    additionalProperties?: boolean

    default?: object
}

interface JSONSchemaArray extends JSONSchemaDescripted {
    $schema?: string
    type: "array"
    items?: JSONSchemaType

    default?: any[]
}

type JSONSchema = JSONSchemaObject | JSONSchemaArray

interface FileEditValidation {
    /**
     * JSON schema
     */
    schema?: JSONSchema
    /**
     * Error while validating the JSON schema
     */
    schemaError?: string
    /**
     * The path was validated with a file output (defFileOutput)
     */
    pathValid?: boolean
}

interface DataFrame {
    schema?: string
    data: unknown
    validation?: FileEditValidation
}

interface Logprob {
    /**
     * Token text
     */
    token: string
    /**
     * Log probably of the generated token
     */
    logprob: number
    /**
     * Logprob value converted to %
     */
    probPercent?: number
    /**
     * Normalized entropy
     */
    entropy?: number
    /**
     * Other top tokens considered by the LLM
     */
    topLogprobs?: { token: string; logprob: number }[]
}

interface RunPromptResult {
    messages: ChatCompletionMessageParam[]
    text: string
    reasoning?: string
    annotations?: Diagnostic[]
    fences?: Fenced[]
    frames?: DataFrame[]
    json?: any
    error?: SerializedError
    genVars?: Record<string, string>
    schemas?: Record<string, JSONSchema>
    finishReason:
        | "stop"
        | "length"
        | "tool_calls"
        | "content_filter"
        | "cancel"
        | "fail"
    usages?: ChatCompletionUsages
    fileEdits?: Record<string, FileUpdate>
    edits?: Edits[]
    changelogs?: ChangeLog[]
    model?: ModelType
    choices?: LogProb[]
    logprobs?: Logprob[]
    perplexity?: number
    uncertainty?: number
}

/**
 * Path manipulation functions.
 */
interface Path {
    /**
     * Returns the last portion of a path. Similar to the Unix basename command.
     * @param path
     */
    dirname(path: string): string

    /**
     * Returns the extension of the path, from the last '.' to end of string in the last portion of the path.
     * @param path
     */
    extname(path: string): string

    /**
     * Returns the last portion of a path, similar to the Unix basename command.
     */
    basename(path: string, suffix?: string): string

    /**
     * The path.join() method joins all given path segments together using the platform-specific separator as a delimiter, then normalizes the resulting path.
     * @param paths
     */
    join(...paths: string[]): string

    /**
     * The path.normalize() method normalizes the given path, resolving '..' and '.' segments.
     */
    normalize(...paths: string[]): string

    /**
     * The path.relative() method returns the relative path from from to to based on the current working directory. If from and to each resolve to the same path (after calling path.resolve() on each), a zero-length string is returned.
     */
    relative(from: string, to: string): string

    /**
     * The path.resolve() method resolves a sequence of paths or path segments into an absolute path.
     * @param pathSegments
     */
    resolve(...pathSegments: string[]): string

    /**
     * Determines whether the path is an absolute path.
     * @param path
     */
    isAbsolute(path: string): boolean
}

interface Fenced {
    label: string
    language?: string
    content: string
    args?: { schema?: string } & Record<string, string>

    validation?: FileEditValidation
}

interface XMLParseOptions {
    allowBooleanAttributes?: boolean
    ignoreAttributes?: boolean
    ignoreDeclaration?: boolean
    ignorePiTags?: boolean
    parseAttributeValue?: boolean
    removeNSPrefix?: boolean
    unpairedTags?: string[]
}

interface ParsePDFOptions {
    /**
     * Disable removing trailing spaces in text
     */
    disableCleanup?: boolean
    /**
     * Render each page as an image
     */
    renderAsImage?: boolean
    /**
     * Zoom scaling with rendering pages and figures
     */
    scale?: number
    /**
     * Disable caching with cache: false
     */
    cache?: boolean
}

interface HTMLToTextOptions {
    /**
     * After how many chars a line break should follow in `p` elements.
     *
     * Set to `null` or `false` to disable word-wrapping.
     */
    wordwrap?: number | false | null | undefined
}

interface ParseXLSXOptions {
    // specific worksheet name
    sheet?: string
    // Use specified range (A1-style bounded range string)
    range?: string
}

interface WorkbookSheet {
    name: string
    rows: object[]
}

interface ParseZipOptions {
    glob?: string
}

type TokenEncoder = (text: string) => number[]
type TokenDecoder = (lines: Iterable<number>) => string

interface Tokenizer {
    model: string
    /**
     * Number of tokens
     */
    size?: number
    encode: TokenEncoder
    decode: TokenDecoder
}

interface CSVParseOptions {
    delimiter?: string
    headers?: string[]
    repair?: boolean
}

interface TextChunk extends WorkspaceFile {
    lineStart: number
    lineEnd: number
}

interface TextChunkerConfig extends LineNumberingOptions {
    model?: ModelType
    chunkSize?: number
    chunkOverlap?: number
    docType?: OptionsOrString<
        | "cpp"
        | "python"
        | "py"
        | "java"
        | "go"
        | "c#"
        | "c"
        | "cs"
        | "ts"
        | "js"
        | "tsx"
        | "typescript"
        | "js"
        | "jsx"
        | "javascript"
        | "php"
        | "md"
        | "mdx"
        | "markdown"
        | "rst"
        | "rust"
    >
}

interface Tokenizers {
    /**
     * Estimates the number of tokens in the content. May not be accurate
     * @param model
     * @param text
     */
    count(text: string, options?: { model?: ModelType }): Promise<number>

    /**
     * Truncates the text to a given number of tokens, approximation.
     * @param model
     * @param text
     * @param maxTokens
     * @param options
     */
    truncate(
        text: string,
        maxTokens: number,
        options?: { model?: ModelType; last?: boolean }
    ): Promise<string>

    /**
     * Tries to resolve a tokenizer for a given model. Defaults to gpt-4o if not found.
     * @param model
     */
    resolve(model?: ModelType): Promise<Tokenizer>

    /**
     * Chunk the text into smaller pieces based on a token limit and chunking strategy.
     * @param text
     * @param options
     */
    chunk(
        file: Awaitable<string | WorkspaceFile>,
        options?: TextChunkerConfig
    ): Promise<TextChunk[]>
}

interface HashOptions {
    /**
     * Algorithm used for hashing
     */
    algorithm?: "sha-256"
    /**
     * Trim hash to this number of character
     */
    length?: number
    /**
     * Include genaiscript version in the hash
     */
    version?: boolean
    /**
     * Optional salting of the hash
     */
    salt?: string
    /**
     * Read the content of workspace files object into the hash
     */
    readWorkspaceFiles?: boolean
}

interface VideoProbeResult {
    streams: {
        index: number
        codec_name: string
        codec_long_name: string
        profile: string
        codec_type: string
        codec_tag_string: string
        codec_tag: string
        width?: number
        height?: number
        coded_width?: number
        coded_height?: number
        closed_captions?: number
        film_grain?: number
        has_b_frames?: number
        sample_aspect_ratio?: string
        display_aspect_ratio?: string
        pix_fmt?: string
        level?: number
        color_range?: string
        color_space?: string
        color_transfer?: string
        color_primaries?: string
        chroma_location?: string
        field_order?: string
        refs?: number
        is_avc?: string
        nal_length_size?: number
        id: string
        r_frame_rate: string
        avg_frame_rate: string
        time_base: string
        start_pts: number
        start_time: number
        duration_ts: number
        duration: number
        bit_rate: number
        max_bit_rate: string
        bits_per_raw_sample: number | string
        nb_frames: number | string
        nb_read_frames?: string
        nb_read_packets?: string
        extradata_size?: number
        tags?: {
            creation_time: string
            language?: string
            handler_name: string
            vendor_id?: string
            encoder?: string
        }
        disposition?: {
            default: number
            dub: number
            original: number
            comment: number
            lyrics: number
            karaoke: number
            forced: number
            hearing_impaired: number
            visual_impaired: number
            clean_effects: number
            attached_pic: number
            timed_thumbnails: number
            captions: number
            descriptions: number
            metadata: number
            dependent: number
            still_image: number
        }
        sample_fmt?: string
        sample_rate?: number
        channels?: number
        channel_layout?: string
        bits_per_sample?: number | string
    }[]
    format: {
        filename: string
        nb_streams: number
        nb_programs: number
        format_name: string
        format_long_name: string
        start_time: number
        duration: number
        size: number
        bit_rate: number
        probe_score: number
        tags: {
            major_brand: string
            minor_version: string
            compatible_brands: string
            creation_time: string
        }
    }
}

interface PDFPageImage extends WorkspaceFile {
    id: string
    width: number
    height: number
}

interface PDFPage {
    index: number
    content: string
    image?: string
    figures?: PDFPageImage[]
}

interface Parsers {
    /**
     * Parses text as a JSON5 payload
     */
    JSON5(
        content: string | WorkspaceFile,
        options?: { defaultValue?: any }
    ): any | undefined

    /**
     * Parses text generated by an LLM as JSON payload
     * @param content
     */
    JSONLLM(content: string): any | undefined

    /**
     * Parses text or file as a JSONL payload. Empty lines are ignore, and JSON5 is used for parsing.
     * @param content
     */
    JSONL(content: string | WorkspaceFile): any[] | undefined

    /**
     * Parses text as a YAML payload
     */
    YAML(
        content: string | WorkspaceFile,
        options?: { defaultValue?: any }
    ): any | undefined

    /**
     * Parses text as TOML payload
     * @param text text as TOML payload
     */
    TOML(
        content: string | WorkspaceFile,
        options?: { defaultValue?: any }
    ): any | undefined

    /**
     * Parses the front matter of a markdown file
     * @param content
     * @param defaultValue
     */
    frontmatter(
        content: string | WorkspaceFile,
        options?: { defaultValue?: any; format: "yaml" | "json" | "toml" }
    ): any | undefined

    /**
     * Parses a file or URL as PDF
     * @param content
     */
    PDF(
        content: string | WorkspaceFile,
        options?: ParsePDFOptions
    ): Promise<
        | {
              /**
               * Reconstructed text content from page content
               */
              file: WorkspaceFile
              /**
               * Page text content
               */
              pages: string[]
              /**
               * Rendered pages as images if `renderAsImage` is set
               */
              images?: string[]

              /**
               * Parse PDF content
               */
              data: PDFPage[]
          }
        | undefined
    >

    /**
     * Parses a .docx file
     * @param content
     */
    DOCX(
        content: string | WorkspaceFile,
        options?: { format: "markdown" | "text" | "html" }
    ): Promise<{ file: WorkspaceFile } | undefined>

    /**
     * Parses a CSV file or text
     * @param content
     */
    CSV(
        content: string | WorkspaceFile,
        options?: CSVParseOptions
    ): object[] | undefined

    /**
     * Parses a XLSX file and a given worksheet
     * @param content
     */
    XLSX(
        content: WorkspaceFile,
        options?: ParseXLSXOptions
    ): Promise<WorkbookSheet[] | undefined>

    /**
     * Parses a .env file
     * @param content
     */
    dotEnv(content: string | WorkspaceFile): Record<string, string>

    /**
     * Parses a .ini file
     * @param content
     */
    INI(
        content: string | WorkspaceFile,
        options?: INIParseOptions
    ): any | undefined

    /**
     * Parses a .xml file
     * @param content
     */
    XML(
        content: string | WorkspaceFile,
        options?: { defaultValue?: any } & XMLParseOptions
    ): any | undefined

    /**
     * Convert HTML to text
     * @param content html string or file
     * @param options
     */
    HTMLToText(
        content: string | WorkspaceFile,
        options?: HTMLToTextOptions
    ): Promise<string>

    /**
     * Convert HTML to markdown
     * @param content html string or file
     * @param options rendering options
     */
    HTMLToMarkdown(
        content: string | WorkspaceFile,
        options?: HTMLToMarkdownOptions
    ): Promise<string>

    /**
     * Extracts the contents of a zip archive file
     * @param file
     * @param options
     */
    unzip(
        file: WorkspaceFile,
        options?: ParseZipOptions
    ): Promise<WorkspaceFile[]>

    /**
     * Estimates the number of tokens in the content.
     * @param content content to tokenize
     */
    tokens(content: string | WorkspaceFile): number

    /**
     * Parses fenced code sections in a markdown text
     */
    fences(content: string | WorkspaceFile): Fenced[]

    /**
     * Parses various format of annotations (error, warning, ...)
     * @param content
     */
    annotations(content: string | WorkspaceFile): Diagnostic[]

    /**
     * Executes a tree-sitter query on a code file
     * @param file
     * @param query tree sitter query; if missing, returns the entire tree. `tags` return tags
     */
    code(
        file: WorkspaceFile,
        query?: OptionsOrString<"tags">
    ): Promise<{ captures: QueryCapture[] }>

    /**
     * Parses and evaluates a math expression
     * @param expression math expression compatible with mathjs
     * @param scope object to read/write variables
     */
    math(
        expression: string,
        scope?: object
    ): Promise<string | number | undefined>

    /**
     * Using the JSON schema, validates the content
     * @param schema JSON schema instance
     * @param content object to validate
     */
    validateJSON(schema: JSONSchema, content: any): FileEditValidation

    /**
     * Renders a mustache template
     * @param text template text
     * @param data data to render
     */
    mustache(text: string | WorkspaceFile, data: Record<string, any>): string

    /**
     * Renders a jinja template
     */
    jinja(text: string | WorkspaceFile, data: Record<string, any>): string

    /**
     * Computes a diff between two files
     */
    diff(
        left: WorkspaceFile,
        right: WorkspaceFile,
        options?: DefDiffOptions
    ): string

    /**
     * Cleans up a dataset made of rows of data
     * @param rows
     * @param options
     */
    tidyData(rows: object[], options?: DataFilter): object[]

    /**
     * Applies a GROQ query to the data
     * @param data data object to filter
     * @param query query
     * @see https://groq.dev/
     */
    GROQ(query: string, data: any): Promise<any>

    /**
     * Computes a sha1 that can be used for hashing purpose, not cryptographic.
     * @param content content to hash
     */
    hash(content: any, options?: HashOptions): Promise<string>

    /**
     * Optionally removes a code fence section around the text
     * @param text
     * @param language
     */
    unfence(text: string, language: string): string

    /**
     * Erase <think>...</think> tags
     * @param text
     */
    unthink(text: string): string
}

interface AICIGenOptions {
    /**
     * Make sure the generated text is one of the options.
     */
    options?: string[]
    /**
     * Make sure the generated text matches given regular expression.
     */
    regex?: string | RegExp
    /**
     * Make sure the generated text matches given yacc-like grammar.
     */
    yacc?: string
    /**
     * Make sure the generated text is a substring of the given string.
     */
    substring?: string
    /**
     * Used together with `substring` - treat the substring as ending the substring
     * (typically '"' or similar).
     */
    substringEnd?: string
    /**
     * Store result of the generation (as bytes) into a shared variable.
     */
    storeVar?: string
    /**
     * Stop generation when the string is generated (the result includes the string and any following bytes (from the same token)).
     */
    stopAt?: string
    /**
     * Stop generation when the given number of tokens have been generated.
     */
    maxTokens?: number
}

interface AICINode {
    type: "aici"
    name: "gen"
}

interface AICIGenNode extends AICINode {
    name: "gen"
    options: AICIGenOptions
}

interface AICI {
    /**
     * Generate a string that matches given constraints.
     * If the tokens do not map cleanly into strings, it will contain Unicode replacement characters.
     */
    gen(options: AICIGenOptions): AICIGenNode
}

interface YAML {
    /**
     * Converts an object to its YAML representation
     * @param obj
     */
    stringify(obj: any): string
    /**
     * Parses a YAML string to object
     */
    parse(text: string | WorkspaceFile): any
}

interface XML {
    /**
     * Parses an XML payload to an object
     * @param text
     */
    parse(text: string | WorkspaceFile, options?: XMLParseOptions): any
}

interface JSONSchemaUtilities {
    /**
     * Infers a JSON schema from an object
     * @param obj
     * @deprecated Use `fromParameters` instead
     */
    infer(obj: any): Promise<JSONSchema>

    /**
     * Converts a parameters schema to a JSON schema
     * @param parameters
     */
    fromParameters(parameters: PromptParametersSchema | undefined): JSONSchema
}

interface HTMLTableToJSONOptions {
    useFirstRowForHeadings?: boolean
    headers?: HeaderRows
    stripHtmlFromHeadings?: boolean
    stripHtmlFromCells?: boolean
    stripHtml?: boolean | null
    forceIndexAsNumber?: boolean
    countDuplicateHeadings?: boolean
    ignoreColumns?: number[] | null
    onlyColumns?: number[] | null
    ignoreHiddenRows?: boolean
    id?: string[] | null
    headings?: string[] | null
    containsClasses?: string[] | null
    limitrows?: number | null
}

interface HTMLToMarkdownOptions {
    disableGfm?: boolean
}

interface HTML {
    /**
     * Converts all HTML tables to JSON.
     * @param html
     * @param options
     */
    convertTablesToJSON(
        html: string,
        options?: HTMLTableToJSONOptions
    ): Promise<object[][]>
    /**
     * Converts HTML markup to plain text
     * @param html
     */
    convertToText(html: string): Promise<string>
    /**
     * Converts HTML markup to markdown
     * @param html
     */
    convertToMarkdown(
        html: string,
        options?: HTMLToMarkdownOptions
    ): Promise<string>
}

interface GitCommit {
    sha: string
    date: string
    message: string
}

interface Git {
    /**
     * Current working directory
     */
    cwd: string

    /**
     * Resolves the default branch for this repository
     */
    defaultBranch(): Promise<string>

    /**
     * Gets the last tag in the repository
     */
    lastTag(): Promise<string>

    /**
     * Gets the current branch of the repository
     */
    branch(): Promise<string>

    /**
     * Executes a git command in the repository and returns the stdout
     * @param cmd
     */
    exec(
        args: string[] | string,
        options?: {
            label?: string
        }
    ): Promise<string>

    /**
     * Lists the branches in the git repository
     */
    listBranches(): Promise<string[]>

    /**
     * Finds specific files in the git repository.
     * By default, work
     * @param options
     */
    listFiles(
        scope: "modified-base" | "staged" | "modified",
        options?: {
            base?: string
            /**
             * Ask the user to stage the changes if the diff is empty.
             */
            askStageOnEmpty?: boolean
            paths?: ElementOrArray<string>
            excludedPaths?: ElementOrArray<string>
        }
    ): Promise<WorkspaceFile[]>

    /**
     *
     * @param options
     */
    diff(options?: {
        staged?: boolean
        /**
         * Ask the user to stage the changes if the diff is empty.
         */
        askStageOnEmpty?: boolean
        base?: string
        head?: string
        paths?: ElementOrArray<string>
        excludedPaths?: ElementOrArray<string>
        unified?: number
        algorithm?: "patience" | "minimal" | "histogram" | "myers"
        ignoreSpaceChange?: boolean
        extras?: string[]
        /**
         * Modifies the diff to be in a more LLM friendly format
         */
        llmify?: boolean
    }): Promise<string>

    /**
     * Lists the commits in the git repository
     */
    log(options?: {
        base?: string
        head?: string
        count?: number
        merges?: boolean
        author?: string
        until?: string
        after?: string
        excludedGrep?: string | RegExp
        paths?: ElementOrArray<string>
        excludedPaths?: ElementOrArray<string>
    }): Promise<GitCommit[]>

    /**
     * Create a shallow git clone
     * @param repository URL of the remote repository
     * @param options various clone options
     * @returns the path to the cloned repository
     */
    shallowClone(
        repository: string,
        options?: {
            /**
             * Brnach to clone
             */
            branch?: string
        }
    ): Promise<Git>

    /**
     * Open a git client on a different directory
     * @param cwd working directory
     */
    client(cwd: string): Git
}

/**
 * A ffmpeg command builder. This instance is the 'native' fluent-ffmpeg command builder.
 */
interface FfmpegCommandBuilder {
    seekInput(startTime: number | string): FfmpegCommandBuilder
    duration(duration: number | string): FfmpegCommandBuilder
    noVideo(): FfmpegCommandBuilder
    noAudio(): FfmpegCommandBuilder
    audioCodec(codec: string): FfmpegCommandBuilder
    audioBitrate(bitrate: string | number): FfmpegCommandBuilder
    audioChannels(channels: number): FfmpegCommandBuilder
    audioFrequency(freq: number): FfmpegCommandBuilder
    audioQuality(quality: number): FfmpegCommandBuilder
    audioFilters(
        filters: string | string[] | AudioVideoFilter[]
    ): FfmpegCommandBuilder
    toFormat(format: string): FfmpegCommandBuilder

    videoCodec(codec: string): FfmpegCommandBuilder
    videoBitrate(
        bitrate: string | number,
        constant?: boolean
    ): FfmpegCommandBuilder
    videoFilters(filters: string | string[]): FfmpegCommandBuilder
    outputFps(fps: number): FfmpegCommandBuilder
    frames(frames: number): FfmpegCommandBuilder
    keepDisplayAspectRatio(): FfmpegCommandBuilder
    size(size: string): FfmpegCommandBuilder
    aspectRatio(aspect: string | number): FfmpegCommandBuilder
    autopad(pad?: boolean, color?: string): FfmpegCommandBuilder

    inputOptions(...options: string[]): FfmpegCommandBuilder
    outputOptions(...options: string[]): FfmpegCommandBuilder
}

interface FFmpegCommandOptions {
    inputOptions?: ElementOrArray<string>
    outputOptions?: ElementOrArray<string>
    cache?: boolean | string
    /**
     * For video conversion, output size as `wxh`
     */
    size?: string
}

interface VideoExtractFramesOptions extends FFmpegCommandOptions {
    /**
     * A set of seconds or timestamps (`[[hh:]mm:]ss[.xxx]`)
     */
    timestamps?: number[] | string[]
    /**
     * Number of frames to extract
     */
    count?: number
    /**
     * Extract frames on the start of each transcript segment
     */
    transcript?: TranscriptionResult | string
    /**
     * Extract Intra frames (keyframes). This is a efficient and fast decoding.
     */
    keyframes?: boolean
    /**
     * Picks frames that exceed scene threshold (between 0 and 1), typically between 0.2, and 0.5.
     * This is computationally intensive.
     */
    sceneThreshold?: number
    /**
     * Output of the extracted frames
     */
    format?: OptionsOrString<"jpeg" | "png">
}

interface VideoExtractClipOptions extends FFmpegCommandOptions {
    /**
     * Start time of the clip in seconds or timestamp (`[[hh:]mm:]ss[.xxx]`)
     */
    start: number | string
    /**
     * Duration of the clip in seconds or timestamp (`[[hh:]mm:]ss[.xxx]`).
     * You can also specify `end`.
     */
    duration?: number | string
    /**
     * End time of the clip in seconds or timestamp (`[[hh:]mm:]ss[.xxx]`).
     * You can also specify `duration`.
     */
    end?: number | string
}

interface VideoExtractAudioOptions extends FFmpegCommandOptions {
    /**
     * Optimize for speech-to-text transcription. Default is true.
     */
    transcription?: boolean

    forceConversion?: boolean
}

interface Ffmpeg {
    /**
     * Extracts metadata information from a video file using ffprobe
     * @param filename
     */
    probe(
        file: string | WorkspaceFile,
        options?: FFmpegCommandOptions
    ): Promise<VideoProbeResult>

    /**
     * Extracts frames from a video file
     * @param options
     */
    extractFrames(
        file: string | WorkspaceFile,
        options?: VideoExtractFramesOptions
    ): Promise<string[]>

    /**
     * Extracts a clip from a video. Returns the generated video file path.
     */
    extractClip(
        file: string | WorkspaceFile,
        options: VideoExtractClipOptions
    ): Promise<string>

    /**
     * Extract the audio track from a video
     * @param videoPath
     */
    extractAudio(
        file: string | WorkspaceFile,
        options?: VideoExtractAudioOptions
    ): Promise<string>

    /**
     * Runs a ffmpeg command and returns the list of generated file names
     * @param input
     * @param builder manipulates the ffmpeg command and returns the output name
     */
    run(
        input: string | WorkspaceFile,
        builder: (
            cmd: FfmpegCommandBuilder,
            options?: { input: string; dir: string }
        ) => Awaitable<string>,
        options?: FFmpegCommandOptions
    ): Promise<string[]>
}

interface GitHubOptions {
    owner: string
    repo: string
    baseUrl?: string
    auth?: string
    ref?: string
    refName?: string
    issueNumber?: number
}

type GitHubWorkflowRunStatus =
    | "completed"
    | "action_required"
    | "cancelled"
    | "failure"
    | "neutral"
    | "skipped"
    | "stale"
    | "success"
    | "timed_out"
    | "in_progress"
    | "queued"
    | "requested"
    | "waiting"
    | "pending"

interface GitHubWorkflowRun {
    id: number
    name?: string
    display_title: string
    status: string
    conclusion: string
    html_url: string
    created_at: string
    head_branch: string
    head_sha: string
}

interface GitHubWorkflowJob {
    id: number
    run_id: number
    status: string
    conclusion: string
    name: string
    html_url: string
    logs_url: string
    logs: string
    started_at: string
    completed_at: string
    content: string
}

interface GitHubIssue {
    id: number
    body?: string
    title: string
    number: number
    state: string
    state_reason?: "completed" | "reopened" | "not_planned" | null
    html_url: string
    draft?: boolean
    reactions?: GitHubReactions
    user: GitHubUser
    assignee?: GitHubUser
}

interface GitHubReactions {
    url: string
    total_count: number
    "+1": number
    "-1": number
    laugh: number
    confused: number
    heart: number
    hooray: number
    eyes: number
    rocket: number
}

interface GitHubComment {
    id: number
    body?: string
    user: GitHubUser
    created_at: string
    updated_at: string
    html_url: string
    reactions?: GitHubReactions
}

interface GitHubPullRequest extends GitHubIssue {
    head: {
        ref: string
    }
    base: {
        ref: string
    }
}

interface GitHubCodeSearchResult {
    name: string
    path: string
    sha: string
    html_url: string
    score: number
    repository: string
}

interface GitHubWorkflow {
    id: number
    name: string
    path: string
}

interface GitHubPaginationOptions {
    /**
     * Default number of items to fetch, default is 50.
     */
    count?: number
}

interface GitHubFile extends WorkspaceFile {
    type: "file" | "dir" | "submodule" | "symlink"
    size: number
}

interface GitHubUser {
    login: string
}

interface GitHubRelease {
    id: number
    tag_name: string
    name: string
    draft?: boolean
    prerelease?: boolean
    html_url: string
    published_at: string
    body?: string
}

interface GitHub {
    /**
     * Gets connection information for octokit
     */
    info(): Promise<GitHubOptions | undefined>

    /**
     * Lists workflows in a GitHub repository
     */
    listWorkflows(options?: GitHubPaginationOptions): Promise<GitHubWorkflow[]>

    /**
     * Lists workflow runs for a given workflow
     * @param workflowId
     * @param options
     */
    listWorkflowRuns(
        workflow_id: string | number,
        options?: {
            branch?: string
            event?: string
            status?: GitHubWorkflowRunStatus
        } & GitHubPaginationOptions
    ): Promise<GitHubWorkflowRun[]>

    /**
     * Downloads a GitHub Action workflow run log
     * @param runId
     */
    listWorkflowJobs(
        runId: number,
        options?: GitHubPaginationOptions
    ): Promise<GitHubWorkflowJob[]>

    /**
     * Downloads a GitHub Action workflow run log
     * @param jobId
     */
    downloadWorkflowJobLog(
        jobId: number,
        options?: { llmify?: boolean }
    ): Promise<string>

    /**
     * Diffs two GitHub Action workflow job logs
     */
    diffWorkflowJobLogs(job_id: number, other_job_id: number): Promise<string>

    /**
     * Lists issues for a given repository
     * @param options
     */
    listIssues(
        options?: {
            state?: "open" | "closed" | "all"
            labels?: string
            sort?: "created" | "updated" | "comments"
            direction?: "asc" | "desc"
            creator?: string
            assignee?: string
            since?: string
            mentioned?: string
        } & GitHubPaginationOptions
    ): Promise<GitHubIssue[]>

    /**
     * Gets the details of a GitHub issue
     * @param issueNumber issue number (not the issue id!). If undefined, reads value from GITHUB_ISSUE environment variable.
     */
    getIssue(issueNumber?: number | string): Promise<GitHubIssue>

    /**
     * Create a GitHub issue comment
     * @param issueNumber issue number (not the issue id!). If undefined, reads value from GITHUB_ISSUE environment variable.
     * @param body the body of the comment as Github Flavored markdown
     */
    createIssueComment(
        issueNumber: number | string,
        body: string
    ): Promise<GitHubComment>

    /**
     * Lists comments for a given issue
     * @param issue_number
     * @param options
     */
    listIssueComments(
        issue_number: number | string,
        options?: GitHubPaginationOptions
    ): Promise<GitHubComment[]>

    /**
     * Lists pull requests for a given repository
     * @param options
     */
    listPullRequests(
        options?: {
            state?: "open" | "closed" | "all"
            sort?: "created" | "updated" | "popularity" | "long-running"
            direction?: "asc" | "desc"
        } & GitHubPaginationOptions
    ): Promise<GitHubPullRequest[]>

    /**
     * Gets the details of a GitHub pull request
     * @param pull_number pull request number. Default resolves the pull request for the current branch.
     */
    getPullRequest(pull_number?: number | string): Promise<GitHubPullRequest>

    /**
     * Lists comments for a given pull request
     * @param pull_number
     * @param options
     */
    listPullRequestReviewComments(
        pull_number: number,
        options?: GitHubPaginationOptions
    ): Promise<GitHubComment[]>

    /**
     * Gets the content of a file from a GitHub repository
     * @param filepath
     * @param options
     */
    getFile(
        filepath: string,
        /**
         * commit sha, branch name or tag name
         */
        ref: string
    ): Promise<WorkspaceFile>

    /**
     * Searches code in a GitHub repository
     */
    searchCode(
        query: string,
        options?: GitHubPaginationOptions
    ): Promise<GitHubCodeSearchResult[]>

    /**
     * Lists branches in a GitHub repository
     */
    listBranches(options?: GitHubPaginationOptions): Promise<string[]>

    /**
     * Lists tags in a GitHub repository
     */
    listRepositoryLanguages(): Promise<Record<string, number>>

    /**
     * List latest releases in a GitHub repository
     * @param options
     */
    listReleases(options?: GitHubPaginationOptions): Promise<GitHubRelease[]>

    /**
     * Lists tags in a GitHub repository
     */
    getRepositoryContent(
        path?: string,
        options?: {
            ref?: string
            glob?: string
            downloadContent?: boolean
            maxDownloadSize?: number
            type?: (typeof GitHubFile)["type"]
        }
    ): Promise<GitHubFile[]>

    /**
     * Gets the underlying Octokit client
     */
    api(): Promise<any>

    /**
     * Opens a client to a different repository
     * @param owner
     * @param repo
     */
    client(owner: string, repo: string): GitHub
}

interface MD {
    /**
     * Parses front matter from markdown
     * @param text
     */
    frontmatter(
        text: string | WorkspaceFile,
        format?: "yaml" | "json" | "toml" | "text"
    ): any

    /**
     * Removes the front matter from the markdown text
     */
    content(text: string | WorkspaceFile): string

    /**
     * Merges frontmatter with the existing text
     * @param text
     * @param frontmatter
     * @param format
     */
    updateFrontmatter(
        text: string,
        frontmatter: any,
        format?: "yaml" | "json"
    ): string

    /**
     * Attempts to chunk markdown in text section in a way that does not splitting the heading structure.
     * @param text
     * @param options
     */
    chunk(
        text: string | WorkspaceFile,
        options?: { maxTokens?: number; model?: string }
    ): Promise<TextChunk[]>
}

interface JSONL {
    /**
     * Parses a JSONL string to an array of objects
     * @param text
     */
    parse(text: string | WorkspaceFile): any[]
    /**
     * Converts objects to JSONL format
     * @param objs
     */
    stringify(objs: any[]): string
}

interface INI {
    /**
     * Parses a .ini file
     * @param text
     */
    parse(text: string | WorkspaceFile): any

    /**
     * Converts an object to.ini string
     * @param value
     */
    stringify(value: any): string
}

interface JSON5 {
    /**
     * Parses a JSON/YAML/XML string to an object
     * @param text
     */
    parse(text: string | WorkspaceFile): any

    /**
     * Renders an object to a JSON5-LLM friendly string
     * @param value
     */
    stringify(value: any): string
}

interface CSVStringifyOptions {
    delimiter?: string
    header?: boolean
}

/**
 * Interface representing CSV operations.
 */
interface CSV {
    /**
     * Parses a CSV string to an array of objects.
     *
     * @param text - The CSV string to parse.
     * @param options - Optional settings for parsing.
     * @param options.delimiter - The delimiter used in the CSV string. Defaults to ','.
     * @param options.headers - An array of headers to use. If not provided, headers will be inferred from the first row.
     * @returns An array of objects representing the parsed CSV data.
     */
    parse(text: string | WorkspaceFile, options?: CSVParseOptions): object[]

    /**
     * Converts an array of objects to a CSV string.
     *
     * @param csv - The array of objects to convert.
     * @param options - Optional settings for stringifying.
     * @param options.headers - An array of headers to use. If not provided, headers will be inferred from the object keys.
     * @returns A CSV string representing the data.
     */
    stringify(csv: object[], options?: CSVStringifyOptions): string

    /**
     * Converts an array of objects that represents a data table to a markdown table.
     *
     * @param csv - The array of objects to convert.
     * @param options - Optional settings for markdown conversion.
     * @param options.headers - An array of headers to use. If not provided, headers will be inferred from the object keys.
     * @returns A markdown string representing the data table.
     */
    markdownify(csv: object[], options?: { headers?: string[] }): string

    /**
     * Splits the original array into chunks of the specified size.
     * @param csv
     * @param rows
     */
    chunk(
        csv: object[],
        size: number
    ): { chunkStartIndex: number; rows: object[] }[]
}

/**
 * Provide service for responsible.
 */
interface ContentSafety {
    /**
     * Scans text for the risk of a User input attack on a Large Language Model.
     * If not supported, the method is not defined.
     */
    detectPromptInjection?(
        content: Awaitable<
            ElementOrArray<string> | ElementOrArray<WorkspaceFile>
        >
    ): Promise<{ attackDetected: boolean; filename?: string; chunk?: string }>
    /**
     * Analyzes text for harmful content.
     * If not supported, the method is not defined.
     * @param content
     */
    detectHarmfulContent?(
        content: Awaitable<
            ElementOrArray<string> | ElementOrArray<WorkspaceFile>
        >
    ): Promise<{
        harmfulContentDetected: boolean
        filename?: string
        chunk?: string
    }>
}

interface HighlightOptions {
    maxLength?: number
}

interface VectorSearchOptions extends EmbeddingsModelOptions {
    /**
     * Maximum number of embeddings to use
     */
    topK?: number
    /**
     * Minimum similarity score
     */
    minScore?: number
}

interface FuzzSearchOptions {
    /**
     * Controls whether to perform prefix search. It can be a simple boolean, or a
     * function.
     *
     * If a boolean is passed, prefix search is performed if true.
     *
     * If a function is passed, it is called upon search with a search term, the
     * positional index of that search term in the tokenized search query, and the
     * tokenized search query.
     */
    prefix?: boolean
    /**
     * Controls whether to perform fuzzy search. It can be a simple boolean, or a
     * number, or a function.
     *
     * If a boolean is given, fuzzy search with a default fuzziness parameter is
     * performed if true.
     *
     * If a number higher or equal to 1 is given, fuzzy search is performed, with
     * a maximum edit distance (Levenshtein) equal to the number.
     *
     * If a number between 0 and 1 is given, fuzzy search is performed within a
     * maximum edit distance corresponding to that fraction of the term length,
     * approximated to the nearest integer. For example, 0.2 would mean an edit
     * distance of 20% of the term length, so 1 character in a 5-characters term.
     * The calculated fuzziness value is limited by the `maxFuzzy` option, to
     * prevent slowdown for very long queries.
     */
    fuzzy?: boolean | number
    /**
     * Controls the maximum fuzziness when using a fractional fuzzy value. This is
     * set to 6 by default. Very high edit distances usually don't produce
     * meaningful results, but can excessively impact search performance.
     */
    maxFuzzy?: number
    /**
     * Maximum number of results to return
     */
    topK?: number
}

interface Retrieval {
    /**
     * Executers a web search with Tavily or Bing Search.
     * @param query
     */
    webSearch(
        query: string,
        options?: {
            count?: number
            provider?: "tavily" | "bing"
            /**
             * Return undefined when no web search providers are present
             */
            ignoreMissingProvider?: boolean
        }
    ): Promise<WorkspaceFile[]>

    /**
     * Search using similarity distance on embeddings
     */
    vectorSearch(
        query: string,
        files: (string | WorkspaceFile) | (string | WorkspaceFile)[],
        options?: VectorSearchOptions
    ): Promise<WorkspaceFile[]>

    /**
     * Performs a fuzzy search over the files
     * @param query keywords to search
     * @param files list of files
     * @param options fuzzing configuration
     */
    fuzzSearch(
        query: string,
        files: WorkspaceFile | WorkspaceFile[],
        options?: FuzzSearchOptions
    ): Promise<WorkspaceFile[]>
}

interface ArrayFilter {
    /**
     * Selects the first N elements from the data
     */
    sliceHead?: number
    /**
     * Selects the last N elements from the data
     */
    sliceTail?: number
    /**
     * Selects the a random sample of N items in the collection.
     */
    sliceSample?: number
}

interface DataFilter extends ArrayFilter {
    /**
     * The keys to select from the object.
     * If a key is prefixed with -, it will be removed from the object.
     */
    headers?: ElementOrArray<string>
    /**
     * Removes items with duplicate values for the specified keys.
     */
    distinct?: ElementOrArray<string>
    /**
     * Sorts the data by the specified key(s)
     */
    sort?: ElementOrArray<string>
}

interface DefDataOptions
    extends Omit<ContextExpansionOptions, "maxTokens">,
        FenceFormatOptions,
        DataFilter,
        ContentSafetyOptions {
    /**
     * Output format in the prompt. Defaults to Markdown table rendering.
     */
    format?: "json" | "yaml" | "csv"

    /**
     * GROQ query to filter the data
     * @see https://groq.dev/
     */
    query?: string
}

interface DefSchemaOptions {
    /**
     * Output format in the prompt.
     */
    format?: "typescript" | "json" | "yaml"
}

type ChatFunctionArgs = { context: ToolCallContext } & Record<string, any>
type ChatFunctionHandler = (args: ChatFunctionArgs) => Awaitable<ToolCallOutput>
type ChatMessageRole = "user" | "assistant" | "system"

interface HistoryMessageUser {
    role: "user"
    content: string
}

interface HistoryMessageAssistant {
    role: "assistant"
    name?: string
    content: string
}

interface WriteTextOptions extends ContextExpansionOptions {
    /**
     * Append text to the assistant response. This feature is not supported by all models.
     * @deprecated
     */
    assistant?: boolean
    /**
     * Specifies the message role. Default is user
     */
    role?: ChatMessageRole
}

type PromptGenerator = (ctx: ChatGenerationContext) => Awaitable<unknown>

interface PromptGeneratorOptions
    extends ModelOptions,
        PromptSystemOptions,
        ContentSafetyOptions {
    /**
     * Label for trace
     */
    label?: string

    /**
     * Write file edits to the file system
     */
    applyEdits?: boolean

    /**
     * Throws if the generation is not successful
     */
    throwOnError?: boolean
}

interface FileOutputOptions {
    /**
     * Schema identifier to validate the generated file
     */
    schema?: string
}

interface FileOutput {
    pattern: string[]
    description?: string
    options?: FileOutputOptions
}

interface ImportTemplateOptions {
    /**
     * Ignore unknown arguments
     */
    allowExtraArguments?: boolean
}

type PromptCacheControlType = "ephemeral"

interface PromptTemplateString {
    /**
     * Set a priority similar to CSS z-index
     * to control the trimming of the prompt when the context is full
     * @param priority
     */
    priority(value: number): PromptTemplateString
    /**
     * Sets the context layout flex weight
     */
    flex(value: number): PromptTemplateString
    /**
     * Applies jinja template to the string lazily
     * @param data jinja data
     */
    jinja(data: Record<string, any>): PromptTemplateString
    /**
     * Applies mustache template to the string lazily
     * @param data mustache data
     */
    mustache(data: Record<string, any>): PromptTemplateString
    /**
     * Sets the max tokens for this string
     * @param tokens
     */
    maxTokens(tokens: number): PromptTemplateString

    /**
     * Updates the role of the message
     */
    role(role: ChatMessageRole): PromptTemplateString

    /**
     * Configure the cacheability of the prompt.
     * @param value cache control type
     */
    cacheControl(value: PromptCacheControlType): PromptTemplateString
}

type ImportTemplateArgumentType =
    | Awaitable<string | number | boolean>
    | (() => Awaitable<string | number | boolean>)

interface ChatTurnGenerationContext {
    importTemplate(
        files: string | string[],
        arguments?: Record<string, ImportTemplateArgumentType>,
        options?: ImportTemplateOptions
    ): void
    writeText(body: Awaitable<string>, options?: WriteTextOptions): void
    assistant(
        text: Awaitable<string>,
        options?: Omit<WriteTextOptions, "assistant">
    ): void
    $(strings: TemplateStringsArray, ...args: any[]): PromptTemplateString
    fence(body: StringLike, options?: FenceOptions): void
    def(
        name: string,
        body:
            | string
            | WorkspaceFile
            | WorkspaceFile[]
            | ShellOutput
            | Fenced
            | RunPromptResult,
        options?: DefOptions
    ): string
    defData(
        name: string,
        data: Awaitable<object[] | object>,
        options?: DefDataOptions
    ): string
    defDiff<T extends string | WorkspaceFile>(
        name: string,
        left: T,
        right: T,
        options?: DefDiffOptions
    ): string
    console: PromptGenerationConsole
}

interface FileUpdate {
    before: string
    after: string
    validation?: FileEditValidation
}

interface RunPromptResultPromiseWithOptions extends Promise<RunPromptResult> {
    options(values?: PromptGeneratorOptions): RunPromptResultPromiseWithOptions
}

interface DefToolOptions {
    /**
     * Maximum number of tokens per tool content response
     */
    maxTokens?: number
}

interface DefAgentOptions extends Omit<PromptGeneratorOptions, "label"> {
    /**
     * Excludes agent conversation from agent memory
     */
    disableMemory?: boolean

    /**
     * Disable memory query on each query (let the agent call the tool)
     */
    disableMemoryQuery?: boolean
}

type ChatAgentHandler = (
    ctx: ChatGenerationContext,
    args: ChatFunctionArgs
) => Awaitable<unknown>

interface McpServerConfig {
    command: string
    args: string[]
    params?: string[]
    version?: string

    id: string
    options?: DefToolOptions
}

type McpServersConfig = Record<string, Omit<McpServerConfig, "id" | "options">>

type ZodTypeLike = { _def: any; safeParse: any; refine: any }

type BufferLike =
    | string
    | WorkspaceFile
    | Buffer
    | Blob
    | ArrayBuffer
    | Uint8Array
    | ReadableStream

type TranscriptionModelType = OptionsOrString<"openai:whisper-1">

interface TranscriptionOptions {
    /**
     * Model to use for transcription. By default uses the `transcribe` alias.
     */
    model?: TranscriptionModelType

    /**
     * Translate to English.
     */
    translate?: boolean

    /**
     * Input language in iso-639-1 format.
     * @see https://en.wikipedia.org/wiki/List_of_ISO_639_language_codes
     */
    language?: string

    /**
     * The sampling temperature, between 0 and 1.
     * Higher values like 0.8 will make the output more random, while lower values like 0.2 will make it more focused and deterministic.
     */
    temperature?: number

    /**
     * If true, the transcription will be cached.
     */
    cache?: boolean | string
}

interface TranscriptionResult {
    /**
     * Complete transcription text
     */
    text: string
    /**
     * Error if any
     */
    error?: SerializedError

    /**
     * SubRip subtitle string from segments
     */
    srt?: string

    /**
     * WebVTT subtitle string from segments
     */
    vtt?: string

    /**
     * Individual segments
     */
    segments?: {
        /**
         * The start time of the segment
         */
        start: number
        /**
         * The transcribed text.
         */
        text: string
        /**
         * Seek offset of the segment
         */
        seek?: number
        /**
         * End time in seconds
         */
        end?: number
        /**
         * Temperature used for the generation of the segment
         */
        temperature?: number
    }[]
}

type SpeechModelType = OptionsOrString<"openai:tts-1-hd" | "openai:tts-1">

type SpeechVoiceType = OptionsOrString<
    "alloy",
    "ash",
    "coral",
    "echo",
    "fable",
    "onyx",
    "nova",
    "sage",
    "shimmer"
>

interface SpeechOptions {
    /**
     * Speech to text model
     */
    model?: SpeechModelType
    /**
     * Voice to use (model-specific)
     */
    voice?: SpeechVoiceType
    /**
     * If true, the transcription will be cached.
     */
    cache?: boolean | string
}

interface SpeechResult {
    /**
     * Generate audio-buffer file
     */
    filename?: string
    /**
     * Error if any
     */
    error?: SerializedError
}

interface ChatGenerationContext extends ChatTurnGenerationContext {
    defSchema(
        name: string,
        schema: JSONSchema | ZodTypeLike,
        options?: DefSchemaOptions
    ): string
    defImages(
        files: ElementOrArray<BufferLike>,
        options?: DefImagesOptions
    ): void
    defTool(
        tool:
            | ToolCallback
            | AgenticToolCallback
            | AgenticToolProviderCallback
            | McpServersConfig,
        options?: DefToolOptions
    ): void
    defTool(
        name: string,
        description: string,
        parameters: PromptParametersSchema | JSONSchema,
        fn: ChatFunctionHandler,
        options?: DefToolOptions
    ): void
    defAgent(
        name: string,
        description: string,
        fn: string | ChatAgentHandler,
        options?: DefAgentOptions
    ): void
    defChatParticipant(
        participant: ChatParticipantHandler,
        options?: ChatParticipantOptions
    ): void
    defFileOutput(
        pattern: ElementOrArray<string | WorkspaceFile>,
        description: string,
        options?: FileOutputOptions
    ): void
    runPrompt(
        generator: string | PromptGenerator,
        options?: PromptGeneratorOptions
    ): Promise<RunPromptResult>
    prompt(
        strings: TemplateStringsArray,
        ...args: any[]
    ): RunPromptResultPromiseWithOptions
    defFileMerge(fn: FileMergeHandler): void
    defOutputProcessor(fn: PromptOutputProcessorHandler): void
    transcribe(
        audio: string | WorkspaceFile,
        options?: TranscriptionOptions
    ): Promise<TranscriptionResult>
    speak(text: string, options?: SpeechOptions): Promise<SpeechResult>
}

interface GenerationOutput {
    /**
     * full chat history
     */
    messages: ChatCompletionMessageParam[]

    /**
     * LLM output.
     */
    text: string

    /**
     * Reasoning produced by model
     */
    reasoning?: string

    /**
     * Parsed fence sections
     */
    fences: Fenced[]

    /**
     * Parsed data sections
     */
    frames: DataFrame[]

    /**
     * A map of file updates
     */
    fileEdits: Record<string, FileUpdate>

    /**
     * Generated variables, typically from AICI.gen
     */
    genVars: Record<string, string>

    /**
     * Generated annotations
     */
    annotations: Diagnostic[]

    /**
     * Schema definition used in the generation
     */
    schemas: Record<string, JSONSchema>

    /**
     * Output as JSON if parsable
     */
    json?: any
}

type Point = {
    row: number
    column: number
}

interface SyntaxNode {
    id: number
    typeId: number
    grammarId: number
    type: string
    grammarType: string
    isNamed: boolean
    isMissing: boolean
    isExtra: boolean
    hasChanges: boolean
    hasError: boolean
    isError: boolean
    text: string
    parseState: number
    nextParseState: number
    startPosition: Point
    endPosition: Point
    startIndex: number
    endIndex: number
    parent: SyntaxNode | null
    children: Array<SyntaxNode>
    namedChildren: Array<SyntaxNode>
    childCount: number
    namedChildCount: number
    firstChild: SyntaxNode | null
    firstNamedChild: SyntaxNode | null
    lastChild: SyntaxNode | null
    lastNamedChild: SyntaxNode | null
    nextSibling: SyntaxNode | null
    nextNamedSibling: SyntaxNode | null
    previousSibling: SyntaxNode | null
    previousNamedSibling: SyntaxNode | null
    descendantCount: number

    equals(other: SyntaxNode): boolean
    toString(): string
    child(index: number): SyntaxNode | null
    namedChild(index: number): SyntaxNode | null
    childForFieldName(fieldName: string): SyntaxNode | null
    childForFieldId(fieldId: number): SyntaxNode | null
    fieldNameForChild(childIndex: number): string | null
    childrenForFieldName(
        fieldName: string,
        cursor: TreeCursor
    ): Array<SyntaxNode>
    childrenForFieldId(fieldId: number, cursor: TreeCursor): Array<SyntaxNode>
    firstChildForIndex(index: number): SyntaxNode | null
    firstNamedChildForIndex(index: number): SyntaxNode | null

    descendantForIndex(index: number): SyntaxNode
    descendantForIndex(startIndex: number, endIndex: number): SyntaxNode
    namedDescendantForIndex(index: number): SyntaxNode
    namedDescendantForIndex(startIndex: number, endIndex: number): SyntaxNode
    descendantForPosition(position: Point): SyntaxNode
    descendantForPosition(startPosition: Point, endPosition: Point): SyntaxNode
    namedDescendantForPosition(position: Point): SyntaxNode
    namedDescendantForPosition(
        startPosition: Point,
        endPosition: Point
    ): SyntaxNode
    descendantsOfType(
        types: String | Array<String>,
        startPosition?: Point,
        endPosition?: Point
    ): Array<SyntaxNode>

    walk(): TreeCursor
}

interface TreeCursor {
    nodeType: string
    nodeTypeId: number
    nodeStateId: number
    nodeText: string
    nodeId: number
    nodeIsNamed: boolean
    nodeIsMissing: boolean
    startPosition: Point
    endPosition: Point
    startIndex: number
    endIndex: number
    readonly currentNode: SyntaxNode
    readonly currentFieldName: string
    readonly currentFieldId: number
    readonly currentDepth: number
    readonly currentDescendantIndex: number

    reset(node: SyntaxNode): void
    resetTo(cursor: TreeCursor): void
    gotoParent(): boolean
    gotoFirstChild(): boolean
    gotoLastChild(): boolean
    gotoFirstChildForIndex(goalIndex: number): boolean
    gotoFirstChildForPosition(goalPosition: Point): boolean
    gotoNextSibling(): boolean
    gotoPreviousSibling(): boolean
    gotoDescendant(goalDescendantIndex: number): void
}

interface QueryCapture {
    name: string
    node: SyntaxNode
}

interface ShellOptions {
    cwd?: string
    stdin?: string
    /**
     * Process timeout in  milliseconds, default is 60s
     */
    timeout?: number
    /**
     * trace label
     */
    label?: string
}

interface ShellOutput {
    stdout?: string
    stderr?: string
    exitCode: number
    failed: boolean
}

interface BrowserOptions {
    /**
     * Browser engine for this page. Defaults to chromium
     *
     */
    browser?: "chromium" | "firefox" | "webkit"

    /**
     * If specified, accepted downloads are downloaded into this directory. Otherwise, temporary directory is created and is deleted when browser is closed. In either case, the downloads are deleted when the browser context they were created in is closed.
     */
    downloadsPath?: string

    /**
     * Whether to run browser in headless mode. More details for Chromium and Firefox. Defaults to true unless the devtools option is true.
     */
    headless?: boolean

    /**
     * Specify environment variables that will be visible to the browser. Defaults to process.env.
     */
    env?: Record<string, string>
}

interface BrowseSessionOptions extends BrowserOptions, TimeoutOptions {
    /**
     * Creates a new context for the browser session
     */
    incognito?: boolean

    /**
     * Base url to use for relative urls
     * @link https://playwright.dev/docs/api/class-browser#browser-new-context-option-base-url
     */
    baseUrl?: string

    /**
     * Toggles bypassing page's Content-Security-Policy. Defaults to false.
     * @link https://playwright.dev/docs/api/class-browser#browser-new-context-option-bypass-csp
     */
    bypassCSP?: boolean

    /**
     * Whether to ignore HTTPS errors when sending network requests. Defaults to false.
     * @link https://playwright.dev/docs/api/class-browser#browser-new-context-option-ignore-https-errors
     */
    ignoreHTTPSErrors?: boolean

    /**
     * Whether or not to enable JavaScript in the context. Defaults to true.
     * @link https://playwright.dev/docs/api/class-browser#browser-new-context-option-java-script-enabled
     */
    javaScriptEnabled?: boolean

    /**
     * Enable recording video for all pages. Implies incognito mode.
     */
    recordVideo?:
        | boolean
        | {
              width: number
              height: number
          }
}

interface TimeoutOptions {
    /**
     * Maximum time in milliseconds. Default to no timeout
     */
    timeout?: number
}

interface ScreenshotOptions extends TimeoutOptions {
    quality?: number
    scale?: "css" | "device"
    type?: "png" | "jpeg"
    style?: string
}

interface PageScreenshotOptions extends ScreenshotOptions {
    fullPage?: boolean
    omitBackground?: boolean
    clip?: {
        x: number
        y: number
        width: number
        height: number
    }
}

interface BrowserLocatorSelector {
    /**
     * Allows locating elements by their ARIA role, ARIA attributes and accessible name.
     * @param role
     * @param options
     */
    getByRole(
        role:
            | "alert"
            | "alertdialog"
            | "application"
            | "article"
            | "banner"
            | "blockquote"
            | "button"
            | "caption"
            | "cell"
            | "checkbox"
            | "code"
            | "columnheader"
            | "combobox"
            | "complementary"
            | "contentinfo"
            | "definition"
            | "deletion"
            | "dialog"
            | "directory"
            | "document"
            | "emphasis"
            | "feed"
            | "figure"
            | "form"
            | "generic"
            | "grid"
            | "gridcell"
            | "group"
            | "heading"
            | "img"
            | "insertion"
            | "link"
            | "list"
            | "listbox"
            | "listitem"
            | "log"
            | "main"
            | "marquee"
            | "math"
            | "meter"
            | "menu"
            | "menubar"
            | "menuitem"
            | "menuitemcheckbox"
            | "menuitemradio"
            | "navigation"
            | "none"
            | "note"
            | "option"
            | "paragraph"
            | "presentation"
            | "progressbar"
            | "radio"
            | "radiogroup"
            | "region"
            | "row"
            | "rowgroup"
            | "rowheader"
            | "scrollbar"
            | "search"
            | "searchbox"
            | "separator"
            | "slider"
            | "spinbutton"
            | "status"
            | "strong"
            | "subscript"
            | "superscript"
            | "switch"
            | "tab"
            | "table"
            | "tablist"
            | "tabpanel"
            | "term"
            | "textbox"
            | "time"
            | "timer"
            | "toolbar"
            | "tooltip"
            | "tree"
            | "treegrid"
            | "treeitem",
        options?: {
            checked?: boolean
            disabled?: boolean
            exact?: boolean
            expanded?: boolean
            name?: string
            selected?: boolean
        } & TimeoutOptions
    ): Locator

    /**
     * Allows locating input elements by the text of the associated <label> or aria-labelledby element, or by the aria-label attribute.
     * @param name
     * @param options
     */
    getByLabel(
        name: string,
        options?: { exact?: boolean } & TimeoutOptions
    ): Locator

    /**
     * Allows locating elements that contain given text.
     * @param text
     * @param options
     */
    getByText(
        text: string,
        options?: { exact?: boolean } & TimeoutOptions
    ): Locator

    /** Locate element by the test id. */
    getByTestId(testId: string, options?: TimeoutOptions): Locator
}

/**
 * A Locator instance
 * @link https://playwright.dev/docs/api/class-locator
 */
interface BrowserLocator extends BrowserLocatorSelector {
    /**
     * When the locator points to a list of elements, this returns an array of locators, pointing to their respective elements.
     * locator.all() does not wait for elements to match the locator, and instead immediately returns whatever is present in the page.
     */
    all(): Promise<BrowserLocator[]>
    /**
     * Click an element
     * @link https://playwright.dev/docs/api/class-locator#locator-click
     */
    click(
        options?: { button: "left" | "right" | "middle" } & TimeoutOptions
    ): Promise<void>

    /**
     * Returns when element specified by locator satisfies the state option.
     * @link https://playwright.dev/docs/api/class-locator#locator-wait-for
     */
    waitFor(
        options?: {
            state: "attached" | "detached" | "visible" | "hidden"
        } & TimeoutOptions
    ): Promise<void>

    /**
     * Set a value to the input field.
     * @param value
     * @link https://playwright.dev/docs/api/class-locator#locator-fill
     */
    fill(value: string, options?: TimeoutOptions): Promise<void>

    /**
     * Returns the element.innerText.
     * @link https://playwright.dev/docs/api/class-locator#locator-inner-text
     */
    innerText(options?: TimeoutOptions): Promise<string>

    /**
     * Returns the element.innerHTML
     * @link https://playwright.dev/docs/api/class-locator#locator-inner-html
     */
    innerHTML(options?: TimeoutOptions): Promise<string>

    /**
     * Returns the element.textContent
     * @link https://playwright.dev/docs/api/class-locator#locator-text-content
     * @param options
     */
    textContent(options?: TimeoutOptions): Promise<string>

    /**
     * Returns the value for the matching <input> or <textarea> or <select> element.
     * @link https://playwright.dev/docs/api/class-locator#locator-input-value
     */
    inputValue(options?: TimeoutOptions): Promise<string>

    /**
     * Get the attribute value
     * @param name
     * @param options
     * @link https://playwright.dev/docs/api/class-locator#locator-get-attribute
     */
    getAttribute(name: string, options?: TimeoutOptions): Promise<null | string>

    /**
     * Clears the input field.
     * @link https://playwright.dev/docs/api/class-locator#locator-clear
     */
    clear(options?: TimeoutOptions): Promise<void>

    /**
     * Take a screenshot of the element matching the locator.
     * @link https://playwright.dev/docs/api/class-locator#locator-screenshot
     */
    screenshot(options?: ScreenshotOptions): Promise<Buffer>

    /**
     * This method waits for actionability checks, then tries to scroll element into view, unless it is completely visible as defined by IntersectionObserver's ratio.
     * @link https://playwright.dev/docs/api/class-locator#locator-scroll-into-view-if-needed
     */
    scrollIntoViewIfNeeded(options?: TimeoutOptions): Promise<void>

    /**
     * This method narrows existing locator according to the options, for example filters by text. It can be chained to filter multiple times.
     * @param options
     */
    filter(
        options: {
            has?: BrowserLocator
            hasNot?: BrowserLocator
            hasNotText?: string | RegExp
            hasText?: string | RegExp
        } & TimeoutOptions
    ): Locator
}

/**
 * Playwright Response instance
 * @link https://playwright.dev/docs/api/class-response
 */
interface BrowseResponse {
    /**
     * Contains a boolean stating whether the response was successful (status in the range 200-299) or not.
     * @link https://playwright.dev/docs/api/class-response#response-ok
     */
    ok(): boolean
    /**
     * Contains the status code of the response (e.g., 200 for a success).
     * @link https://playwright.dev/docs/api/class-response#response-status
     */
    status(): number
    /**
     * Contains the status text of the response (e.g. usually an "OK" for a success).
     * @link https://playwright.dev/docs/api/class-response#response-status-text
     */
    statusText(): string

    /**
     * Contains the URL of the response.
     * @link https://playwright.dev/docs/api/class-response#response-url
     */
    url(): string
}

interface BrowserJSHandle {}

interface BrowserVideo {
    /**
     * Returns the video path once the page is closed.
     */
    path(): Promise<string>
}

/**
 * A playwright Page instance
 * @link https://playwright.dev/docs/api/class-page
 */
interface BrowserPage extends BrowserLocatorSelector {
    /**
     * Returns the page's title.
     * @link https://playwright.dev/docs/api/class-page#page-title
     */
    title(): Promise<string>
    /**
     * Current page url
     * @link https://playwright.dev/docs/api/class-page#page-url
     */
    url(): string

    /**
     * Returns the main resource response. In case of multiple redirects, the navigation will resolve with the first non-redirect response.
     * @link https://playwright.dev/docs/api/class-page#page-goto
     * @param url
     * @param options
     */
    goto(
        url: string,
        options?: {
            waitUntil?: "load" | "domcontentloaded" | "networkidle" | "commit"
        } & TimeoutOptions
    ): Promise<null | BrowseResponse>

    /**
     * Returns the buffer of the captured screenshot
     * @link https://playwright.dev/docs/api/class-page#page-screenshot
     */
    screenshot(options?: PageScreenshotOptions): Promise<Buffer>

    /**
     * Gets the full HTML contents of the page, including the doctype.
     * @link https://playwright.dev/docs/api/class-page#page-content
     */
    content(): Promise<string>

    /**
     * The method returns an element locator that can be used to perform actions on this page / frame.
     * @param selector A selector to use when resolving DOM element.
     * @link https://playwright.dev/docs/locators
     */
    locator(selector: string): BrowserLocator

    /**
     * Closes the browser page, context and other resources.
     * If video recording is enabled, the video will be saved at this time.
     */
    close(): Promise<void>

    /**
     * Returns the value of the pageFunction evaluation.
     * @param fn
     * @param args serializable object
     * @link https://playwright.dev/docs/api/class-page#page-evaluate
     */
    evaluate<T = any>(pageFunction: Function | string, arg?: any): Promise<T>

    /**
     * Returns the value of the pageFunction evaluation as a JSHandle.
     * @param fn
     * @param args serializable object
     * @link https://playwright.dev/docs/api/class-page#page-evaluate-handle
     */
    evaluateHandle<T = any>(
        selector: string,
        arg?: any
    ): Promise<BrowserJSHandle>

    /**
     * Video object associated with this page, if `recordVideo` option is enabled.
     */
    video(): BrowserVideo | null
}

interface ShellSelectOptions {}

interface ShellSelectChoice {
    name?: string
    value: string
    description?: string
}

interface ShellInputOptions {
    required?: boolean
}

interface ShellConfirmOptions {
    default?: boolean
}

interface ShellHost {
    /**
     * Executes a shell command
     * @param command
     * @param args
     * @param options
     */
    exec(commandWithArgs: string, options?: ShellOptions): Promise<ShellOutput>
    exec(
        command: string,
        args: string[],
        options?: ShellOptions
    ): Promise<ShellOutput>
}

interface UserInterfaceHost {
    /**
     * Starts a headless browser and navigates to the page.
     * Requires to [install playwright and dependencies](https://microsoft.github.io/genaiscript/reference/scripts/browser).
     * @link https://microsoft.github.io/genaiscript/reference/scripts/browser
     * @param url
     * @param options
     */
    browse(url: string, options?: BrowseSessionOptions): Promise<BrowserPage>

    /**
     * Asks the user to select between options
     * @param message question to ask
     * @param options options to select from
     */
    select(
        message: string,
        options: (string | ShellSelectChoice)[],
        options?: ShellSelectOptions
    ): Promise<string>

    /**
     * Asks the user to input a text
     * @param message message to ask
     */
    input(message: string, options?: ShellInputOptions): Promise<string>

    /**
     * Asks the user to confirm a message
     * @param message message to ask
     */
    confirm(message: string, options?: ShellConfirmOptions): Promise<boolean>
}

interface ContainerPortBinding {
    containerPort: OptionsOrString<"8000/tcp">
    hostPort: string | number
}

interface ContainerOptions {
    /**
     * Container image names.
     * @example python:alpine python:slim python
     * @see https://hub.docker.com/_/python/
     */
    image?: OptionsOrString<
        "python:alpine" | "python:slim" | "python" | "node" | "gcc"
    >

    /**
     * Enable networking in container (disabled by default)
     */
    networkEnabled?: boolean

    /**
     * Environment variables in container. A null/undefined variable is removed from the environment.
     */
    env?: Record<string, string>

    /**
     * Assign the specified name to the container. Must match [a-zA-Z0-9_-]+.
     */
    name?: string

    /**
     * Disable automatic purge of container and volume directory and potentially reuse with same name, configuration.
     */
    persistent?: boolean

    /**
     * List of exposed TCP ports
     */
    ports?: ElementOrArray<ContainerPortBinding>

    /**
     * Commands to executes after the container is created
     */
    postCreateCommands?: ElementOrArray<string>
}

interface PromiseQueue {
    /**
     * Adds a new promise to the queue
     * @param fn
     */
    add<Arguments extends unknown[], ReturnType>(
        function_: (...arguments_: Arguments) => Awaitable<ReturnType>,
        ...arguments_: Arguments
    ): Promise<ReturnType>

    /**
     * Runs all the functions in the queue with limited concurrency
     * @param fns
     */
    all<T = any>(fns: (() => Awaitable<T>)[]): Promise<T[]>

    /**
     * Applies a function to all the values in the queue with limited concurrency
     * @param values
     * @param fn
     */
    mapAll<T extends unknown, Arguments extends unknown[], ReturnType>(
        values: T[],
        fn: (value: T, ...arguments_: Arguments) => Awaitable<ReturnType>,
        ...arguments_: Arguments
    ): Promise<ReturnType[]>
}

interface LanguageModelReference {
    provider: string
    model: string
}

interface LanguageModelHost {
    /**
     * Resolve a language model alias to a provider and model based on the current configuration
     * @param modelId
     */
    resolveLanguageModel(modelId?: string): Promise<LanguageModelReference>
}

type ContentSafetyProvider = "azure"

interface ContentSafetyHost {
    /**
     * Resolve a content safety client
     * @param id safety detection project
     */
    contentSafety(id?: ContentSafetyProvider): Promise<ContentSafety>
}

type FetchOptions = RequestInit & {
    retryOn?: number[] // HTTP status codes to retry on
    retries?: number // Number of retry attempts
    retryDelay?: number // Initial delay between retries
    maxDelay?: number // Maximum delay between retries
}

type FetchTextOptions = Omit<FetchOptions, "body" | "signal" | "window">

interface PythonRuntimeOptions {
    cache?: string
}

interface PythonRuntime {
    /**
     * Runs python code and returns the result
     * @param code python code
     */
    run(code: string): Promise<any>

    /**
     * Imports a package using micropip
     * @param pkg name and version
     */
    import(pkg: string): Promise<void>

    /**
     * Access to python global variables
     */
    globals: PythonProxy
}

interface PythonProxy {
    /**
     * Reads a value from the python object
     * @param name
     */
    get<T>(name: string): T
    /**
     * Copyies a value into the python object
     * @param name
     * @param value
     */
    set<T>(name: string, value: T): void
}

interface PromptHost
    extends ShellHost,
        UserInterfaceHost,
        LanguageModelHost,
        ContentSafetyHost {
    /**
     * A fetch wrapper with proxy, retry and timeout handling.
     */
    fetch(
        input: string | URL | globalThis.Request,
        init?: FetchOptions
    ): Promise<Response>

    /**
     * A function that fetches text from a URL or a file
     * @param url
     * @param options
     */
    fetchText(
        url: string | WorkspaceFile,
        options?: FetchTextOptions
    ): Promise<{
        ok: boolean
        status: number
        text?: string
        file?: WorkspaceFile
    }>

    /**
     * Opens a in-memory key-value cache for the given cache name. Entries are dropped when the cache grows too large.
     * @param cacheName
     */
    cache<K = any, V = any>(
        cacheName: string
    ): Promise<WorkspaceFileCache<K, V>>

    /**
     * Starts a container
     * @param options container creation options
     */
    container(options?: ContainerOptions): Promise<ContainerHost>

    /**
     * Create a new promise queue to run async functions with limited concurrency
     */
    promiseQueue(concurrency: number): PromiseQueue

    /**
     * Instantiates a python evaluation environment powered by pyodide (https://pyodide.org/)
     */
    python(options?: PythonRuntimeOptions): Promise<PythonRuntime>

    /**
     * Gets a client to a Microsoft Teams channel from a share link URL;
     * uses `GENAISCRIPT_TEAMS_CHANNEL_URL` environment variable if `shareUrl` is not provided.
     * Uses Azure CLI login for authentication.
     * @param url
     */
    teamsChannel(shareUrl?: string): Promise<MessageChannelClient>
}

interface WorkspaceFileWithDescription extends WorkspaceFile {
    /**
     * File description used for videos.
     */
    description?: string
}

/**
 * A client to a messaging channel
 */
interface MessageChannelClient {
    /**
     * Posts a message with attachments to the channel
     * @param message
     * @param options
     */
    postMessage(
        message: string,
        options?: {
            /**
             * File attachments that will be added in the channel folder
             */
            files?: (string | WorkspaceFileWithDescription)[]
            /**
             * Sets to false to remove AI generated disclaimer
             */
            disclaimer?: boolean | string
        }
    ): Promise<string>
}

interface ContainerHost extends ShellHost {
    /**
     * Container unique identifier in provider
     */
    id: string

    /**
     * Name assigned to the container. For persistent containers, also contains the sha of the options
     */
    name: string

    /**
     * Disable automatic purge of container and volume directory
     */
    persistent: boolean

    /**
     * Path to the volume mounted in the host
     */
    hostPath: string

    /**
     * Writes a file as text to the container file system
     * @param path
     * @param content
     */
    writeText(path: string, content: string): Promise<void>

    /**
     * Reads a file as text from the container mounted volume
     * @param path
     */
    readText(path: string): Promise<string>

    /**
     * Copies a set of files into the container
     * @param fromHost glob matching files
     * @param toContainer directory in the container
     */
    copyTo(fromHost: string | string[], toContainer: string): Promise<string[]>

    /**
     * List files in a directory in the container
     * @param dir
     */
    listFiles(dir: string): Promise<string[]>

    /**
     * Stops and cleans out the container
     */
    stop(): Promise<void>

    /**
     * Pause container
     */
    pause(): Promise<void>

    /**
     * Resume execution of the container
     */
    resume(): Promise<void>

    /**
     * Force disconnect network
     */
    disconnect(): Promise<void>

    /**
     * A promise queue of concurrency 1 to run serialized functions against the container
     */
    scheduler: PromiseQueue
}

interface PromptContext extends ChatGenerationContext {
    script(options: PromptArgs): void
    system(options: PromptSystemArgs): void
    env: ExpansionVariables
    path: Path
    parsers: Parsers
    retrieval: Retrieval
    /**
     * @deprecated Use `workspace` instead
     */
    fs: WorkspaceFileSystem
    workspace: WorkspaceFileSystem
    host: PromptHost
}

// keep in sync with PromptContext!

/**
 * Console functions
 */
declare var console: PromptGenerationConsole

/**
 * Setup prompt title and other parameters.
 * Exactly one call should be present on top of .genai.js file.
 */
declare function script(options: PromptArgs): void

/**
 * Equivalent of script() for system prompts.
 */
declare function system(options: PromptSystemArgs): void

/**
 * Imports template prompt file and expands arguments in it.
 * @param files
 * @param arguments
 */
declare function importTemplate(
    files: string | string[],
    arguments?: Record<string, ImportTemplateArgumentType>,
    options?: ImportTemplateOptions
): void

/**
 * Append given string to the prompt. It automatically appends "\n".
 * Typically best to use `` $`...` ``-templates instead.
 */
declare function writeText(
    body: Awaitable<string>,
    options?: WriteTextOptions
): void

/**
 * Append given string to the prompt as an assistant message.
 */
declare function assistant(
    text: Awaitable<string>,
    options?: Omit<WriteTextOptions, "assistant">
): void

/**
 * Append given string to the prompt. It automatically appends "\n".
 * `` $`foo` `` is the same as `text("foo")`.
 */
declare function $(
    strings: TemplateStringsArray,
    ...args: any[]
): PromptTemplateString

/**
 * Appends given (often multi-line) string to the prompt, surrounded in fences.
 * Similar to `text(env.fence); text(body); text(env.fence)`
 *
 * @param body string to be fenced
 */
declare function fence(body: StringLike, options?: FenceOptions): void

/**
 * Defines `name` to be the (often multi-line) string `body`.
 * Similar to `text(name + ":"); fence(body, language)`
 *
 * @param name name of defined entity, eg. "NOTE" or "This is text before NOTE"
 * @param body string to be fenced/defined
 * @returns variable name
 */
declare function def(
    name: string,
    body:
        | string
        | WorkspaceFile
        | WorkspaceFile[]
        | ShellOutput
        | Fenced
        | RunPromptResult,
    options?: DefOptions
): string

/**
 * Declares a file that is expected to be generated by the LLM
 * @param pattern file name or glob-like path
 * @param options expectations about the generated file content
 */
declare function defFileOutput(
    pattern: ElementOrArray<string | WorkspaceFile>,
    description?: string,
    options?: FileOutputOptions
): void

/**
 * Declares a tool that can be called from the prompt.
 * @param tool Agentic tool function.
 * @param name The name of the tool to be called. Must be a-z, A-Z, 0-9, or contain underscores and dashes, with a maximum length of 64.
 * @param description A description of what the function does, used by the model to choose when and how to call the function.
 * @param parameters The parameters the tool accepts, described as a JSON Schema object.
 * @param fn callback invoked when the LLM requests to run this function
 */
declare function defTool(
    tool:
        | ToolCallback
        | AgenticToolCallback
        | AgenticToolProviderCallback
        | McpServersConfig,
    options?: DefToolOptions
): void
declare function defTool(
    name: string,
    description: string,
    parameters: PromptParametersSchema | JSONSchema,
    fn: ChatFunctionHandler,
    options?: DefToolOptions
): void

/**
 * Declares a LLM agent tool that can be called from the prompt.
 * @param name name of the agent, do not prefix with agent
 * @param description description of the agent, used by the model to choose when and how to call the agent
 * @param fn prompt generation context
 * @param options additional options for the agent LLM
 */
declare function defAgent(
    name: string,
    description: string,
    fn: string | ChatAgentHandler,
    options?: DefAgentOptions
): void

/**
 * Registers a callback to be called when a file is being merged
 * @param fn
 */
declare function defFileMerge(fn: FileMergeHandler): void

/**
 * Variables coming from the fragment on which the prompt is operating.
 */
declare var env: ExpansionVariables

/**
 * Path manipulation functions.
 */
declare var path: Path

/**
 * A set of parsers for well-known file formats
 */
declare var parsers: Parsers

/**
 * Retrieval Augmented Generation services
 */
declare var retrieval: Retrieval

/**
 * Access to the workspace file system.
 */
declare var workspace: WorkspaceFileSystem

/**
 * YAML parsing and stringifying functions.
 */
declare var YAML: YAML

/**
 * INI parsing and stringifying.
 */
declare var INI: INI

/**
 * CSV parsing and stringifying.
 */
declare var CSV: CSV

/**
 * XML parsing and stringifying.
 */
declare var XML: XML

/**
 * HTML parsing
 */
declare var HTML: HTML

/**
 * Markdown and frontmatter parsing.
 */
declare var MD: MD

/**
 * JSONL parsing and stringifying.
 */
declare var JSONL: JSONL

/**
 * JSON5 parsing
 */
declare var JSON5: JSON5

/**
 * JSON Schema utilities
 */
declare var JSONSchema: JSONSchemaUtilities

/**
 * AICI operations
 */
declare var AICI: AICI

/**
 * Access to current LLM chat session information
 */
declare var host: PromptHost

/**
 * Access to GitHub queries for the current repository
 */
declare var github: GitHub

/**
 * Access to Git operations for the current repository
 */
declare var git: Git

/**
 * Access to ffmpeg operations
 */
declare var ffmpeg: Ffmpeg

/**
 * Computation around tokens
 */
declare var tokenizers: Tokenizers

/**
 * @deprecated use `host.fetchText` instead
 */
declare function fetchText(
    url: string | WorkspaceFile,
    options?: FetchTextOptions
): Promise<{ ok: boolean; status: number; text?: string; file?: WorkspaceFile }>

/**
 * Declares a JSON schema variable.
 * @param name name of the variable
 * @param schema JSON schema instance
 * @returns variable name
 */
declare function defSchema(
    name: string,
    schema: JSONSchema | ZodTypeLike,
    options?: DefSchemaOptions
): string

/**
 * Adds images to the prompt
 * @param files
 * @param options
 */
declare function defImages(
    files: ElementOrArray<BufferLike>,
    options?: DefImagesOptions
): void

/**
 * Renders a table or object in the prompt
 * @param name
 * @param data
 * @param options
 * @returns variable name
 */
declare function defData(
    name: string,
    data: Awaitable<object[] | object>,
    options?: DefDataOptions
): string

/**
 * Renders a diff of the two given values
 * @param left
 * @param right
 * @param options
 */
declare function defDiff<T extends string | WorkspaceFile>(
    name: string,
    left: T,
    right: T,
    options?: DefDiffOptions
): string

/**
 * Cancels the current prompt generation/execution with the given reason.
 * @param reason
 */
declare function cancel(reason?: string): void

/**
 * Expands and executes prompt
 * @param generator
 */
declare function runPrompt(
    generator: string | PromptGenerator,
    options?: PromptGeneratorOptions
): Promise<RunPromptResult>

/**
 * Expands and executes the prompt
 */
declare function prompt(
    strings: TemplateStringsArray,
    ...args: any[]
): RunPromptResultPromiseWithOptions

/**
 * Registers a callback to process the LLM output
 * @param fn
 */
declare function defOutputProcessor(fn: PromptOutputProcessorHandler): void

/**
 * Registers a chat participant
 * @param participant
 */
declare function defChatParticipant(
    participant: ChatParticipantHandler,
    options?: ChatParticipantOptions
): void

/**
 * Transcribes audio to text.
 * @param audio An audio file to transcribe.
 * @param options
 */
declare function transcribe(
    audio: string | WorkspaceFile,
    options?: TranscriptionOptions
): Promise<TranscriptionResult>

/**
 * Converts text to speech.
 * @param text
 * @param options
 */
declare function speak(
    text: string,
    options?: SpeechOptions
): Promise<SpeechResult>
