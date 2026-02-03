# Claude Code LSP Investigation

Collected 2026-01-31.

## Conclusion

**LSP is broken. Do not use. Use Grep and Glob for code navigation.**

Most LSP operations return empty/useless results. The cause is unknown and not worth investigating. Anthropic's documentation claims capabilities that do not work.

---

## Our Observations

### Interactive CLI test (2026-01-31, Codespace, v2.1.27)

**Setup:**
- `ENABLE_LSP_TOOL=true` in `.claude/settings.json`
- Plugins installed: `rust-analyzer-lsp@claude-plugins-official`, `pyright-lsp@claude-plugins-official`
- Binaries: `rust-analyzer` and `pyright-langserver` in PATH (verified)

**Observation:** LSP operations `documentSymbol`, `hover`, `findReferences`, `goToDefinition` were available and could be invoked.

**Test file:** `/packages/rust_viterbo/geom/src/tolerances.rs`

| Operation | Output |
|-----------|--------|
| `documentSymbol` | Returned symbols: EPS, EPS_UNIT, tests, functions |
| `hover` | "No hover information available" |
| `findReferences` | "No references found" (EPS is used elsewhere in the codebase) |
| `goToDefinition` | "No definition found" |

**Edit tool diagnostics test:**
1. Changed `pub const EPS: f64 = 1e-10;` to `pub const EPS: f64 = "broken";` (type error)
2. Edit tool response: "The file has been updated successfully."
3. No type error or LSP diagnostic surfaced

### Headless CLI test (2026-01-31, Codespace)

**Command:** `claude -p --output-format stream-json --verbose`

**Observation:**
- Plugins list included pyright-lsp and rust-analyzer-lsp
- Tools list did not include any LSP-related tool

---

## GitHub Issues (from anthropics/claude-code repo)

**Caveat:** User reports may be inaccurate, environments differ.

### Issue #21713 (2026-01-29, OPEN, high-priority label)
- **Reporter claim:** rust-analyzer crashes when Claude Code shows diff views
- **Reporter diagnosis:** Invalid URI scheme `_claude_vscode_fs_right:` leaks into `workspace/didChangeWatchedFiles`

### Issue #21655 (2026-01-29, OPEN)
- **Reporter claim:** Multiple LSP operations violate spec
- **Specifics:**
  - `workspaceSymbol` requires `filePath/line/character` but spec says only `query: string`
  - `incomingCalls`/`outgoingCalls` wrong parameter type
  - `documentSymbol` forces unnecessary position parameters
  - `findReferences` missing `context.includeDeclaration` parameter

### Issue #17149 (2026-01-09, OPEN)
- **Reporter claim:** `workspaceSymbol` sends empty query `{"query": ""}`
- **Claimed impact:** Workspace-wide symbol search completely broken

### Issue #17312 (2026-01-10, OPEN, Windows)
- **Reporter claim:** Two issues:
  1. ENOENT - Node.js spawn() can't find .cmd files
  2. Document-level ops (`hover`, `findReferences`, `goToDefinition`, `documentSymbol`) return empty even when LSP responds correctly
- **Note:** Only `workspaceSymbol` works for this reporter

### Issue #22028 (2026-01-30, OPEN)
- **Reporter claim:** clangd fails with "non-added document" error
- **Reporter diagnosis:** Missing `textDocument/didOpen` notification
- **Relevance to us:** Our symptoms differ (we get "No X found", not "non-added document")

### Issue #17856 (2026-01-13, OPEN)
- **Reporter claim:** All LSP ops fail with "Cannot send notification to LSP server: server is error"
- **Reporter speculation:** Possibly related to spaces in paths

### Issue #21374 (2026-01-28, OPEN)
- **Reporter claim:** LSP plugin works in CLI but not in VSCode extension

### Issue #17198 (2026-01-09, OPEN)
- **Reporter claim:** LSP plugin installed but Claude falls back to Grep
- **Workarounds mentioned:**
  - `ENABLE_LSP_TOOL=1` env var
  - Install `typescript-language-server` (not `@vtsls/language-server`)

### Issue #21899 (2026-01-30, OPEN)
- **Reporter claim:** Same plugin appears twice - one failed, one enabled

**Pattern across issues:** No Anthropic staff responses on any LSP issues.

---

## Official Documentation Claims

**Source:** code.claude.com/docs, anthropics/claude-plugins-official

**Claimed capabilities:**
- Instant diagnostics after each edit
- Go to definition, find references, hover information
- Type information and documentation

**Configuration requirements:**
- `command` - LSP binary (must be in PATH)
- `extensionToLanguage` - maps extensions to language IDs

**Explicit caveat from docs:**
> "You must install the language server binary separately. LSP plugins configure how Claude Code connects to a language server, but they don't include the server itself."

**What docs do NOT cover:**
- Which specific LSP protocol methods are supported
- Whether all LSP features work
- Performance limitations
- Error handling behavior

---

## Community Sources (least reliable)

**Sources:** Medium articles, Hacker News, community GitHub repos

### Who Claims It Works

**1. Hacker News (Dec 2025, ~v2.0.76)**
- One user: "working very well" on Rust project
- Others: "half-baked", "under-resourced"
- Go LSP auto-install prompt reported
- **Version:** 2.0.76 (before removal)

**2. zircote blog (Dec 24, 2025)**
- Claims goToDefinition, findReferences, hover work
- **Recommends v2.0.67 specifically** due to "bug in latest"
- Uses custom marketplace (not Anthropic's)

**3. AIFreeAPI guide (Dec 30, 2025)**
- Claims all operations work
- **Version:** 2.0.74
- No empirical proof provided

### Community Plugin Marketplaces

**boostvolt/claude-code-lsps** (93 stars, active Jan 2026)
- 23 languages including Rust, Python, TypeScript
- Claims works on v2.1.0+
- Installation: `/plugin marketplace add boostvolt/claude-code-lsps`
- Requires manual LSP binary installation

**Piebald-AI/claude-code-lsps** (209 stars, active Jan 2026)
- 17+ languages
- Warns: "pretty raw still, bugs in different LSP operations"
- May need `npx tweakcc --apply` patch
- Most stars = most users have tried

**anthropics/claude-plugins-official** (5.7k stars)
- **Known issue:** Plugins only contain README.md, no actual code
- `lspServers` config from marketplace.json not processed
- Referenced in issues #15359, #15148, #16219

### What Diagnostics-Only Means (third-party claim)

Per issue #16722 (unverified):
- LSP servers start and register diagnostics handlers
- Diagnostics are **pushed** by server (works)
- Navigation features require **pull** requests (broken/removed)

**Note:** This claim contradicts our observation that `documentSymbol` (a pull request) works.

---

## Experiment: Custom Local Plugin (2026-01-31)

**Plugin cache inspection:**
```
~/.claude/plugins/cache/claude-plugins-official/
├── pyright-lsp/1.0.0/README.md      # ONLY file
└── rust-analyzer-lsp/1.0.0/README.md # ONLY file
```
No `.lsp.json`, no `plugin.json`. The `lspServers` config from marketplace.json is never extracted.

**Created test plugin** `/tmp/rust-lsp-test/`:
```
.claude-plugin/plugin.json  # manifest
.lsp.json                   # LSP config for rust-analyzer
```

**Test:** `claude -p --plugin-dir /tmp/rust-lsp-test --output-format stream-json --verbose`

**Result:** Plugin loads (appears in init plugins list), but NO LSP tool exposed in tools list.

**Note:** This test used headless mode (`-p`). We now know LSP tool only appears in interactive mode.
