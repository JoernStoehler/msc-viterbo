# AntiGravity Claude Agents Reference

This document describes **AntiGravity agents powered by Claude Sonnet 4.5**. It serves as a reference for anyone (human or agent) who needs to understand how Claude agents work, how to spawn them, what tools they have, and what quirks to be aware of.

## Invocation

### Starting a Claude Agent

Claude agents are **native to the AntiGravity VS Code fork**. They are started through the IDE interface:

1. Open the AntiGravity IDE
2. Use the Agent Manager or sidebar to start a new agent
3. Select "Claude Sonnet 4.5" as the model
4. Provide a prompt/task description

**No CLI invocation**: Unlike Codex agents, Claude agents cannot be spawned via command line. They are IDE-native.

### Configuration

- **Model**: Claude Sonnet 4.5
- **Context Window**: ~200k tokens
- **Working Directory**: Inherits from the IDE workspace
- **Permissions**: Configured via IDE (terminal access, file editing, browser control)

## Tools & Functions

Claude agents have access to the following tools. Each tool is described with its signature, effect, output, and any quirks.

### Code Understanding & Navigation

#### `codebase_search`
- **Signature**: `codebase_search(Query: string, TargetDirectories: string[])`
- **Effect**: Performs semantic/fuzzy search across the codebase for code snippets related to the query
- **Output**: Ranked list of relevant code snippets with file paths and line numbers. Top results show full code, others show signatures only.
- **Quirks**: 
  - Best for conceptual queries ("authentication logic", "database connection")
  - Not suitable for high-recall queries (finding all occurrences)
  - May miss exact matches if query is too specific

#### `grep_search`
- **Signature**: `grep_search(SearchPath: string, Query: string, IsRegex: bool, CaseInsensitive: bool, MatchPerLine: bool, Includes: string[])`
- **Effect**: Exact pattern matching using ripgrep
- **Output**: List of matches with file path, line number, and line content (if `MatchPerLine=true`)
- **Quirks**:
  - `IsRegex=false` treats query as literal string (safer default)
  - `IsRegex=true` enables regex but special chars must be escaped
  - Results capped at 50 matches
  - Use `Includes` glob patterns to filter by file type

#### `find_by_name`
- **Signature**: `find_by_name(SearchDirectory: string, Pattern: string, Extensions: string[], Type: "file"|"directory"|"any", MaxDepth: int)`
- **Effect**: Find files/directories by name pattern using fd
- **Output**: List of matches with type, size, modification time, relative path
- **Quirks**:
  - Pattern uses glob format (e.g., `*.py`, `test_*`)
  - Results capped at 50 matches
  - Smart case by default, ignores gitignored files

#### `view_file`
- **Signature**: `view_file(AbsolutePath: string, StartLine?: int, EndLine?: int)`
- **Effect**: Read file contents (text and some binary formats like images/videos)
- **Output**: File contents with line numbers. For binary files, returns the file for viewing.
- **Quirks**:
  - First read of a new file enforces 800-line limit for context
  - Subsequent reads can specify ranges (max 800 lines per call)
  - Line numbers are 1-indexed, inclusive ranges

#### `view_file_outline`
- **Signature**: `view_file_outline(AbsolutePath: string, ItemOffset?: int)`
- **Effect**: Get structural overview of a code file (functions, classes, etc.)
- **Output**: List of code items with signatures, line ranges, and total file info
- **Quirks**:
  - **Preferred first step** for exploring files
  - Only works on files, not directories
  - May paginate for large files (use `ItemOffset`)

#### `view_code_item`
- **Signature**: `view_code_item(File: string, NodePaths: string[])`
- **Effect**: View specific functions/classes by qualified name
- **Output**: Code contents for each requested node
- **Quirks**:
  - Use fully qualified names (e.g., `Foo.bar` for method `bar` in class `Foo`)
  - Can request up to 5 nodes per call

#### `search_in_file`
- **Signature**: `search_in_file(AbsolutePath: string, Query: string)`
- **Effect**: Semantic search within a specific file
- **Output**: Relevant code snippets from that file
- **Quirks**: Similar to `codebase_search` but scoped to one file

#### `list_dir`
- **Signature**: `list_dir(DirectoryPath: string)`
- **Effect**: List directory contents
- **Output**: Files and subdirectories with metadata (size, type, child count)
- **Quirks**: Must be an absolute path to a directory

### Code Modification

#### `write_to_file`
- **Signature**: `write_to_file(TargetFile: string, CodeContent: string, Overwrite: bool, EmptyFile: bool, Description: string, Complexity: int)`
- **Effect**: Create a new file (or overwrite existing if `Overwrite=true`)
- **Output**: Confirmation of file creation
- **Quirks**:
  - **Errors if file exists** unless `Overwrite=true`
  - Creates parent directories automatically
  - Set `EmptyFile=true` to create empty file (omit `CodeContent`)
  - `Complexity` (1-10) indicates importance for user review

#### `replace_file_content`
- **Signature**: `replace_file_content(TargetFile: string, TargetContent: string, ReplacementContent: string, StartLine: int, EndLine: int, AllowMultiple: bool, ...)`
- **Effect**: Edit a **single contiguous block** in a file
- **Output**: Diff showing changes made
- **Quirks**:
  - **`TargetContent` must match EXACTLY** (character-for-character, including whitespace)
  - `StartLine`/`EndLine` define search range (1-indexed, inclusive)
  - `AllowMultiple=false` errors if multiple matches found
  - **Use `multi_replace_file_content` for non-contiguous edits**

#### `multi_replace_file_content`
- **Signature**: `multi_replace_file_content(TargetFile: string, ReplacementChunks: [{TargetContent, ReplacementContent, StartLine, EndLine, AllowMultiple}], ...)`
- **Effect**: Edit **multiple non-contiguous blocks** in a file
- **Output**: Diff showing all changes
- **Quirks**:
  - Same `TargetContent` exact-match requirement as `replace_file_content`
  - Each chunk is independent
  - **Never call both replace tools in parallel for the same file**

### Command Execution

#### `run_command`
- **Signature**: `run_command(CommandLine: string, Cwd: string, SafeToAutoRun: bool, WaitMsBeforeAsync: int)`
- **Effect**: Execute a shell command (bash)
- **Output**: Command output (if completes synchronously) or background command ID
- **Quirks**:
  - **`SafeToAutoRun=true`**: Command runs immediately without user approval
    - **ONLY for read-only commands** (ls, cat, git status, etc.)
    - Never auto-run destructive commands (rm, install, mutating operations)
  - **`WaitMsBeforeAsync`**: How long to wait before backgrounding
    - Small (500ms): For quick commands or to catch early failures
    - Large (5000-10000ms): For commands expected to complete synchronously
    - Max 10000ms
  - **No `cd` command**: Use `Cwd` parameter instead
  - Environment: `PAGER=cat` is set automatically

#### `send_command_input`
- **Signature**: `send_command_input(CommandId: string, Input?: string, Terminate?: bool)`
- **Effect**: Send input to a running command or terminate it
- **Output**: Confirmation
- **Quirks**:
  - Exactly one of `Input` or `Terminate` must be specified
  - Include newline characters in `Input` to submit commands to REPLs

#### `command_status`
- **Signature**: `command_status(CommandId: string, WaitDurationSeconds: int, OutputCharacterCount?: int)`
- **Effect**: Check status of a background command
- **Output**: Status (running/done), output, exit code
- **Quirks**:
  - `WaitDurationSeconds`: Waits up to N seconds for completion (returns early if done)
  - Set to 60 if just waiting for completion
  - Set to 0 for immediate status check

#### `read_terminal`
- **Signature**: `read_terminal(ProcessID: string, Name: string)`
- **Effect**: Read terminal output
- **Output**: Terminal contents
- **Quirks**: Requires process ID and terminal name

### Web & Research

#### `search_web`
- **Signature**: `search_web(query: string)`
- **Effect**: Perform a web search
- **Output**: Summary of relevant information with URL citations
- **Quirks**: Returns synthesized summary, not raw search results

#### `read_url_content`
- **Signature**: `read_url_content(Url: string)`
- **Effect**: Fetch and read web page content via HTTP
- **Output**: Page content converted to markdown
- **Quirks**:
  - **No JavaScript execution** (static content only)
  - **No authentication** (public pages only)
  - For pages requiring login/JS, use `browser_subagent` instead

#### `browser_subagent`
- **Signature**: `browser_subagent(TaskName: string, Task: string, RecordingName: string)`
- **Effect**: Start a browser subagent to perform interactive browser tasks
- **Output**: Subagent completion status
- **Quirks**:
  - **All browser interactions are automatically recorded as WebP videos**
  - Videos saved to artifacts directory
  - `Task` should include clear completion condition
  - Subagent has separate tools for clicking, typing, navigation, etc.

### Asset Generation

#### `generate_image`
- **Signature**: `generate_image(Prompt: string, ImageName: string, ImagePaths?: string[])`
- **Effect**: Generate or edit images from text prompts
- **Output**: Image saved to artifacts directory
- **Quirks**:
  - Can pass up to 3 existing images in `ImagePaths` for editing/combining
  - `ImageName` should be lowercase_with_underscores, max 3 words
  - Useful for UI mockups, assets, diagrams

### Resources

#### `list_resources`
- **Signature**: `list_resources(ServerName: string)`
- **Effect**: List available resources from an MCP server
- **Output**: List of resource URIs
- **Quirks**: Requires MCP server to be configured

#### `read_resource`
- **Signature**: `read_resource(ServerName: string, Uri: string)`
- **Effect**: Read a specific MCP resource
- **Output**: Resource contents
- **Quirks**: URI must be from `list_resources` output

## Lifecycle

### Startup
1. User starts Claude agent via AntiGravity IDE
2. Agent loads workspace context
3. Agent reads `AGENTS.md` and `GEMINI.md`/`AGENTS.md` files automatically
4. Agent begins executing task

### Execution
- Agent has direct access to editor, terminal, and browser
- All tool calls are recorded and visible in IDE
- Agent generates "Artifacts" (task lists, implementation plans, screenshots, recordings)

### Shutdown
- Agent completes task and reports status
- All artifacts remain in artifacts directory
- Terminal/browser sessions may persist

## Quirks & Best Practices

### File Editing
- **Exact matching**: `TargetContent` must match character-for-character (including whitespace)
  - **Workaround**: Copy exact content from `view_file` output
- **Tool selection**: 
  - Single edit → `replace_file_content`
  - Multiple non-contiguous edits → `multi_replace_file_content`
  - Never call both in parallel for same file

### Command Execution
- **Auto-run safety**: Only set `SafeToAutoRun=true` for truly read-only commands
- **Async timing**: Set `WaitMsBeforeAsync` appropriately to avoid premature backgrounding

### Search Strategy
1. `codebase_search` for semantic queries
2. `grep_search` for exact patterns
3. `view_file_outline` before editing files
4. `find_by_name` for file discovery

### Collaboration
- Can spawn Codex sub-agents via `agentctl` (see Codex reference doc)
- Cannot directly spawn other Claude/Gemini agents (IDE-only)

## Comparison with Other Agents

| Feature | Claude (this) | Codex | Gemini |
|---------|---------------|-------|--------|
| Invocation | IDE-native | `agentctl` CLI | IDE-native |
| File Editing | `replace_file_content` | `functions.apply_patch` | Similar to Claude |
| Command Execution | `run_command` (no escaping) | `functions.exec_command` (bash escaping required) | Similar to Claude |
| Context Window | ~200k tokens | Varies by GPT-5 model | 1M tokens |
| Multimodal | Limited | No | Advanced |

## Further Reading

- [`/workspaces/msc-viterbo/AGENTS.md`](../../../AGENTS.md): Root onboarding
- [`codex-gpt-agents.md`](./codex-gpt-agents.md): Codex agent reference
- [`antigravity-gemini-agents.md`](./antigravity-gemini-agents.md): Gemini agent reference
