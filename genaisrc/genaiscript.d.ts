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
}

interface PromptLike extends PromptDefinition {
    /**
     * File where the prompt comes from (if any).
     */
    filename?: string

    /**
     * The text of the prompt JS source code.
     */
    jsSource: string

    /**
     * The actual text of the prompt template.
     * Only used for system prompts.
     */
    text?: string
}

type SystemPromptId = OptionsOrString<
    | "system"
    | "system.annotations"
    | "system.changelog"
    | "system.diagrams"
    | "system.diff"
    | "system.explanations"
    | "system.files"
    | "system.files_schema"
    | "system.fs_find_files"
    | "system.fs_read_file"
    | "system.math"
    | "system.md_frontmatter"
    | "system.python"
    | "system.python_code_interpreter"
    | "system.retrieval_fuzz_search"
    | "system.retrieval_vector_search"
    | "system.retrieval_web_search"
    | "system.schema"
    | "system.tasks"
    | "system.technical"
    | "system.tools"
    | "system.typescript"
    | "system.zero_shot_cot"
>

type SystemToolId = OptionsOrString<
    | "fs_find_files"
    | "fs_read_file"
    | "math_eval"
    | "md_read_frontmatter"
    | "python_code_interpreter"
    | "retrieval_fuzz_search"
    | "retrieval_vector_search"
    | "retrieval_web_search"
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

type PromptTemplateResponseType = "json_object" | "json_schema" | undefined

interface ModelConnectionOptions {
    /**
     * Which LLM model to use.
     *
     * @default gpt-4
     * @example gpt-4
     */
    model?: OptionsOrString<
        | "openai:gpt-4o"
        | "openai:gpt-4o-mini"
        | "openai:gpt-4"
        | "openai:gpt-4-turbo"
        | "openai:gpt-3.5-turbo"
        | "ollama:phi3"
        | "ollama:llama3"
        | "ollama:mixtral"
    >
}

interface ModelOptions extends ModelConnectionOptions {
    /**
     * Temperature to use. Higher temperature means more hallucination/creativity.
     * Range 0.0-2.0.
     *
     * @default 0.2
     */
    temperature?: number

    /**
     * Specifies the type of output. Default is plain text.
     * - `json_object` enables JSON mode
     * - `json_schema` enables structured outputs
     * Use `responseSchema` to specify an output schema.
     */
    responseType?: PromptTemplateResponseType

    /**
     * JSON object schema for the output. Enables the `JSON` output mode by default.
     */
    responseSchema?: PromptParametersSchema | JSONSchemaObject

    /**
     * “Top_p” or nucleus sampling is a setting that decides how many possible words to consider.
     * A high “top_p” value means the model looks at more possible words, even the less likely ones,
     * which makes the generated text more diverse.
     */
    topP?: number

    /**
     * When to stop producing output.
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
     * Custom cache name. If not set, the default cache is used.
     * @deprecated Use `cache` instead with a string
     */
    cacheName?: string

    /**
     * Budget of tokens to apply the prompt flex renderer.
     */
    flexTokens?: number
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
    system?: SystemPromptId | SystemPromptId[]

    /**
     * List of tools used by the prompt.
     */
    tools?: SystemToolId | SystemToolId[]
}

interface ScriptRuntimeOptions {
    /**
     * Secrets required by the prompt
     */
    secrets?: string[]

    /**
     * Default value for emitting line numbers in fenced code blocks.
     */
    lineNumbers?: boolean
}

type PromptParameterType =
    | string
    | number
    | boolean
    | object
    | JSONSchemaNumber
    | JSONSchemaString
    | JSONSchemaBoolean
type PromptParametersSchema = Record<
    string,
    PromptParameterType | PromptParameterType[]
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
}

interface PromptScript
    extends PromptLike,
        ModelOptions,
        PromptSystemOptions,
        EmbeddingsModelOptions,
        ScriptRuntimeOptions {
    /**
     * Groups template in UI
     */
    group?: string

    /**
     * Additional template parameters that will populate `env.vars`
     */
    parameters?: PromptParametersSchema

    /**
     * A file path or list of file paths or globs.
     * The content of these files will be by the files selected in the UI by the user or the cli arguments.
     */
    files?: string | string[]

    /**
     * Extra variable values that can be used to configure system prompts.
     */
    vars?: Record<string, string>

    /**
     * Tests to validate this script.
     */
    tests?: PromptTest | PromptTest[]

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
     * Content of the file.
     */
    content?: string
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

interface ToolCallTrace {
    log(message: string): void
    item(message: string): void
    tip(message: string): void
    fence(message: string, contentType?: string): void
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

interface WorkspaceFileSystem {
    /**
     * Searches for files using the glob pattern and returns a list of files.
     * Ignore `.env` files and apply `.gitignore` if present.
     * @param glob
     */
    findFiles(
        glob: string,
        options?: {
            /**
             * Set to false to skip read text content. True by default
             */
            readText?: boolean
        }
    ): Promise<WorkspaceFile[]>

    /**
     * Performs a grep search over the files in the workspace
     * @param query
     * @param globs
     */
    grep(
        query: string | RegExp,
        globs: string | string[],
        options?: {
            /**
             * Set to false to skip read text content. True by default
             */
            readText?: boolean
        }
    ): Promise<{ files: WorkspaceFile[] }>

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
     * Reads the content of a file and parses to XML, using the XML parser.
     */
    readXML(path: string | Awaitable<WorkspaceFile>): Promise<any>

    /**
     * Writes a file as text to the file system
     * @param path
     * @param content
     */
    writeText(path: string, content: string): Promise<void>

    /**
     * Opens a key-value cache for the given cache name.
     * The cache is persisted across runs of the script. Entries are dropped when the cache grows too large.
     * @param cacheName
     */
    cache<K = any, V = any>(
        cacheName: string
    ): Promise<WorkspaceFileCache<K, V>>
}

interface ToolCallContext {
    trace: ToolCallTrace
}

interface ToolCallback {
    spec: ToolDefinition
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
) => Awaitable<void>

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
     * List of linked files parsed in context
     */
    files: WorkspaceFile[]

    /**
     * current prompt template
     */
    template: PromptDefinition

    /**
     * User defined variables
     */
    vars?: Record<string, string | boolean | number | object | any>

    /**
     * List of secrets used by the prompt, must be registered in `genaiscript`.
     */
    secrets?: Record<string, string>

    /**
     * Root prompt generation context
     */
    generator: ChatGenerationContext
}

type MakeOptional<T, P extends keyof T> = Partial<Pick<T, P>> & Omit<T, P>

type PromptArgs = Omit<PromptScript, "text" | "id" | "jsSource" | "activation">

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
>

type StringLike = string | WorkspaceFile | WorkspaceFile[]

interface FenceOptions {
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
     * Prepend each line with a line numbers. Helps with generating diffs.
     */
    lineNumbers?: boolean

    /**
     * JSON schema identifier
     */
    schema?: string
}

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
}

interface DefOptions extends FenceOptions, ContextExpansionOptions, DataFilter {
    /**
     * Filename filter based on file suffix. Case insensitive.
     */
    endsWith?: string

    /**
     * Filename filter using glob syntax.
     */
    glob?: string

    /**
     * By default, throws an error if the value in def is empty.
     */
    ignoreEmpty?: boolean
}

interface DefImagesOptions {
    detail?: "high" | "low"
    /**
     * Maximum width of the image
     */
    maxWidth?: number
    /**
     * Maximum height of the image
     */
    maxHeight?: number
    /**
     * Auto cropping same color on the edges of the image
     */
    autoCrop?: boolean
}

interface ChatTaskOptions {
    command: string
    cwd?: string
    env?: Record<string, string>
    args?: string[]
}

type JSONSchemaTypeName =
    | "string"
    | "number"
    | "integer"
    | "boolean"
    | "object"
    | "array"
    | "null"

type JSONSchemaType =
    | JSONSchemaString
    | JSONSchemaNumber
    | JSONSchemaBoolean
    | JSONSchemaObject
    | JSONSchemaArray
    | null

interface JSONSchemaString {
    type: "string"
    description?: string
    default?: string
}

interface JSONSchemaNumber {
    type: "number" | "integer"
    description?: string
    default?: number
    minimum?: number
    exclusiveMinimum?: number
    maximum?: number
    exclusiveMaximum?: number
}

interface JSONSchemaBoolean {
    type: "boolean"
    description?: string
    default?: boolean
}

interface JSONSchemaObject {
    $schema?: string
    type: "object"
    description?: string
    properties?: {
        [key: string]: JSONSchemaType
    }
    required?: string[]
    additionalProperties?: boolean
}

interface JSONSchemaArray {
    $schema?: string
    type: "array"
    description?: string
    items?: JSONSchemaType
}

type JSONSchema = JSONSchemaObject | JSONSchemaArray

interface JSONSchemaValidation {
    schema?: JSONSchema
    valid: boolean
    error?: string
}

interface DataFrame {
    schema?: string
    data: unknown
    validation?: JSONSchemaValidation
}

interface RunPromptResult {
    text: string
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

    validation?: JSONSchemaValidation
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
    filter?: (pageIndex: number, text?: string) => boolean
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

interface Parsers {
    /**
     * Parses text as a JSON5 payload
     */
    JSON5(
        content: string | WorkspaceFile,
        options?: { defaultValue?: any }
    ): any | undefined

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
    ): Promise<{ file: WorkspaceFile; pages: string[] } | undefined>

    /**
     * Parses a .docx file
     * @param content
     */
    DOCX(
        content: string | WorkspaceFile
    ): Promise<{ file: WorkspaceFile } | undefined>

    /**
     * Parses a CSV file or text
     * @param content
     */
    CSV(
        content: string | WorkspaceFile,
        options?: { delimiter?: string; headers?: string[] }
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
        options?: { defaultValue?: any }
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
    ): string

    /**
     * Convert HTML to markdown
     * @param content html string or file
     * @param options
     */
    HTMLToMarkdown(content: string | WorkspaceFile): string

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
     * @param query tree sitter query; if missing, returns the entire tree
     */
    code(file: WorkspaceFile, query?: string): Promise<QueryCapture[]>

    /**
     * Parses and evaluates a math expression
     * @param expression math expression compatible with mathjs
     */
    math(expression: string): Promise<string | number | undefined>

    /**
     * Using the JSON schema, validates the content
     * @param schema JSON schema instance
     * @param content object to validate
     */
    validateJSON(schema: JSONSchema, content: any): JSONSchemaValidation

    /**
     * Renders a mustache template
     * @param text template text
     * @param data data to render
     */
    mustache(text: string | WorkspaceFile, data: Record<string, any>): str
    /**
     * Renders a jinja template
     */
    jinja(text: string | WorkspaceFile, data: Record<string, any>): string
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
    parse(text: string): any
}

interface XML {
    /**
     * Parses an XML payload to an object
     * @param text
     */
    parse(text: string, options?: XMLParseOptions): any
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

interface HTML {
    /**
     * Converts all HTML tables to JSON.
     * @param html
     * @param options
     */
    convertTablesToJSON(
        html: string,
        options?: HTMLTableToJSONOptions
    ): object[][]
    /**
     * Converts HTML markup to plain text
     * @param html
     */
    convertToText(html: string): string
    /**
     * Converts HTML markup to markdown
     * @param html
     */
    convertToMarkdown(html: string): string
}

interface MD {
    /**
     * Parses front matter from markdown
     * @param text
     */
    frontmatter(text: string, format?: "yaml" | "json" | "toml" | "text"): any

    /**
     * Removes the front matter from the markdown text
     */
    content(text: string): string

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
}

interface JSONL {
    /**
     * Parses a JSONL string to an array of objects
     * @param text
     */
    parse(text: string): any[]
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
    parse(text: string): any

    /**
     * Converts an object to.ini string
     * @param value
     */
    stringify(value: any): string
}

interface CSV {
    /**
     * Parses a CSV string to an array of objects
     * @param text
     * @param options
     */
    parse(
        text: string,
        options?: {
            delimiter?: string
            headers?: string[]
        }
    ): object[]

    /**
     * Converts an array of object that represents a data table to a markdown table
     * @param csv
     * @param options
     */
    markdownify(csv: object[], options?: { headers?: string[] }): string
}

interface HighlightOptions {
    maxLength?: number
}

interface WebSearchResult {
    webPages: WorkspaceFile[]
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
     * Executers a Bing web search. Requires to configure the BING_SEARCH_API_KEY secret.
     * @param query
     */
    webSearch(query: string): Promise<WorkspaceFile[]>

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

type FetchTextOptions = Omit<RequestInit, "body" | "signal" | "window">

interface DataFilter {
    /**
     * The keys to select from the object.
     * If a key is prefixed with -, it will be removed from the object.
     */
    headers?: string[]
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
     * Removes items with duplicate values for the specified keys.
     */
    distinct?: string[]
}

interface DefDataOptions
    extends Omit<ContextExpansionOptions, "maxTokens">,
        DataFilter {
    /**
     * Output format in the prompt. Defaults to Markdown table rendering.
     */
    format?: "json" | "yaml" | "csv"
}

interface DefSchemaOptions {
    /**
     * Output format in the prompt.
     */
    format?: "typescript" | "json" | "yaml"
}

type ChatFunctionHandler = (
    args: { context: ToolCallContext } & Record<string, any>
) => Awaitable<ToolCallOutput>

interface WriteTextOptions extends ContextExpansionOptions {
    /**
     * Append text to the assistant response
     */
    assistant?: boolean
}

type PromptGenerator = (ctx: ChatGenerationContext) => Awaitable<unknown>

interface PromptGeneratorOptions extends ModelOptions, PromptSystemOptions {
    /**
     * Label for trace
     */
    label?: string
}

interface FileOutputOptions {
    /**
     * Schema identifier to validate the generated file
     */
    schema?: string
}

interface FileOutput {
    pattern: string
    description?: string
    options?: FileOutputOptions
}

interface ImportTemplateOptions {}

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
}

interface ChatTurnGenerationContext {
    importTemplate(
        files: string | string[],
        arguments?: Record<
            string | number | boolean | (() => string | number | boolean)
        >,
        options?: ImportTemplateOptions
    ): void
    writeText(body: Awaitable<string>, options?: WriteTextOptions): void
    $(strings: TemplateStringsArray, ...args: any[]): PromptTemplateString
    fence(body: StringLike, options?: FenceOptions): void
    def(
        name: string,
        body: string | WorkspaceFile | WorkspaceFile[] | ShellOutput | Fenced,
        options?: DefOptions
    ): string
    defData(
        name: string,
        data: object[] | object,
        options?: DefDataOptions
    ): string
    console: PromptGenerationConsole
}

interface FileUpdate {
    before: string
    after: string
    validation?: JSONSchemaValidation
}

interface RunPromptResultPromiseWithOptions extends Promise<RunPromptResult> {
    options(values?: PromptGeneratorOptions): RunPromptResultPromiseWithOptions
}

interface ChatGenerationContext extends ChatTurnGenerationContext {
    defSchema(
        name: string,
        schema: JSONSchema,
        options?: DefSchemaOptions
    ): string
    defImages(
        files: ElementOrArray<string | WorkspaceFile | Buffer | Blob>,
        options?: DefImagesOptions
    ): void
    defTool(
        tool: ToolCallback | AgenticToolCallback | AgenticToolProviderCallback
    ): void
    defTool(
        name: string,
        description: string,
        parameters: PromptParametersSchema | JSONSchema,
        fn: ChatFunctionHandler
    ): void
    defChatParticipant(
        participant: ChatParticipantHandler,
        options?: ChatParticipantOptions
    ): void
    defFileOutput(
        pattern: string,
        description?: string,
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
}

interface GenerationOutput {
    /**
     * LLM output.
     */
    text: string

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
     * Closes the browser page, context and other resources
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
    containerPort: OptionsOrString<"80/tcp">
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
     * Assign the specified name to the container. Must match [a-zA-Z0-9_-]+
     */
    name?: string

    /**
     * Disable automatic purge of container and volume directory
     */
    disablePurge?: boolean

    /**
     * List of exposed TCP ports
     */
    ports?: ElementOrArray<ContainerPortBinding>
}

interface PromptHost extends ShellHost {
    /**
     * Starts a container
     * @param options container creation options
     */
    container(options?: ContainerOptions): Promise<ContainerHost>
}

interface ContainerHost extends ShellHost {
    /**
     * Container unique identifier in provider
     */
    id: string

    /**
     * Disable automatic purge of container and volume directory
     */
    disablePurge: boolean

    /**
     * Path to the volume mounted in the host
     */
    hostPath: string

    /**
     * Path to the volume mounted in the container
     */
    containerPath: string

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
    copyTo(fromHost: string | string[], toContainer: string): Promise<void>

    /**
     * Stops and cleans out the container
     */
    stop(): Promise<void>

    /**
     * Force disconnect network
     */
    disconnect(): Promise<void>
}

interface PromptContext extends ChatGenerationContext {
    script(options: PromptArgs): void
    system(options: PromptSystemArgs): void
    defFileMerge(fn: FileMergeHandler): void
    defOutputProcessor(fn: PromptOutputProcessorHandler): void
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
    arguments?: Record<
        string | number | boolean | (() => string | number | boolean)
    >,
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
    body: string | WorkspaceFile | WorkspaceFile[] | ShellOutput | Fenced,
    options?: DefOptions
): string

/**
 * Declares a file that is expected to be generated by the LLM
 * @param pattern file name or glob-like path
 * @param options expectations about the generated file content
 */
declare function defFileOutput(
    pattern: string,
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
    tool: ToolCallback | AgenticToolCallback | AgenticToolProviderCallback
): void
declare function defTool(
    name: string,
    description: string,
    parameters: PromptParametersSchema | JSONSchema,
    fn: ChatFunctionHandler
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
 * AICI operations
 */
declare var AICI: AICI

/**
 * Access to current LLM chat session information
 */
declare var host: PromptHost

/**
 * Fetches a given URL and returns the response.
 * @param url
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
    schema: JSONSchema,
    options?: DefSchemaOptions
): string

/**
 * Adds images to the prompt
 * @param files
 * @param options
 */
declare function defImages(
    files: ElementOrArray<string | WorkspaceFile | Buffer | Blob>,
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
    data: object[] | object,
    options?: DefDataOptions
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
