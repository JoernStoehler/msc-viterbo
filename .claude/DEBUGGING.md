# CC Crash Debugging - Disabled Features

**Status**: All SessionStart hook features DISABLED to isolate crash cause

## What Was Disabled

### 1. Environment Variables (settings.json)
**Disabled**: ALL environment variables including ENABLE_LSP_TOOL
- **Original**: 
  - `ENABLE_LSP_TOOL: "true"` - **CAN BE FATAL!**
  - `GIT_TERMINAL_PROMPT: "0"`
  - `GIT_SSH_COMMAND: "ssh -oBatchMode=yes"`
  - `GIT_ASKPASS: "/bin/true"`
  - `GCM_INTERACTIVE: "Never"`
  - `GIT_PAGER: "cat"`
  - `GIT_EDITOR: "true"`
- **Now**: Empty env object `{}`
- **Impact**: LSP tools disabled, git may prompt for passwords
- **To re-enable**: Add back one at a time to identify culprit

### 2. SessionStart Hook (settings.json)
**Disabled**: Entire hook removed from configuration
- **Original**: Hook executed `.claude/hooks/session-start.sh` on startup
- **Now**: Empty hooks object `{}`
- **To test**: Re-add hook definition to settings.json

### 2. File Index (session-start.sh)
**Disabled**: File index generation and printing
- **Original**: Ran `file-index.py` to print compressed repo structure
- **Impact**: Agents won't have automatic file awareness at startup
- **To re-enable**: See git history for `file-index.py` invocation

### 3. gh CLI Installation (session-start.sh)
**Disabled**: Automatic gh CLI installation for CC Web
- **Original**: Downloaded and installed gh CLI tarball on CC Web startup
- **Impact**: gh commands won't work until manual install
- **To re-enable**: See git history for wget/tar installation logic

### 4. Environment Detection (session-start.sh)
**Disabled**: All environment-specific logic
- **Original**: Detected CC Web, Codespaces via environment variables
- **To re-enable**: See git history for environment detection

### 5. jq Parsing (session-start.sh)
**Disabled**: Hook input JSON parsing
- **Original**: Used jq to parse hook input for source type
- **To re-enable**: See git history for jq invocation

## Current State

**settings.json**: Minimal config with empty hooks
**session-start.sh**: No-op script that consumes stdin and exits 0

## Gradual Re-enabling Strategy

Test CC startup after each step:

1. **Test with everything disabled** (current state)
   - If CC works: crash was in hooks or env vars
   - If CC crashes: crash is elsewhere (permissions, plugins, or CC itself)

2. **Re-enable safe environment variables only**
   - Add back git-related vars (GIT_PAGER, GIT_EDITOR, etc.)
   - Keep ENABLE_LSP_TOOL disabled
   - If crashes: git env vars cause crash

3. **Test ENABLE_LSP_TOOL separately**
   - Add ONLY `"ENABLE_LSP_TOOL": "true"`
   - If crashes: LSP is the culprit (likely!)

4. **Re-enable hook but keep script minimal** 
   - Add hook back to settings.json
   - Keep session-start.sh as no-op
   - If crashes: hook invocation itself causes crash

5. **Add file index only**
   - Re-enable file-index.py call in session-start.sh
   - If crashes: file-index.py is the culprit

6. **Add environment detection**
   - Re-enable environment variable checks in session-start.sh
   - If crashes: environment logic causes crash

7. **Add gh CLI installation**
   - Re-enable wget/tar operations in session-start.sh
   - If crashes: gh installation causes crash

## How to Restore Original Functionality

```bash
# View what was removed:
git show HEAD~1:.claude/settings.json
git show HEAD~1:.claude/hooks/session-start.sh

# Or restore from git:
git checkout HEAD~1 -- .claude/settings.json
git checkout HEAD~1 -- .claude/hooks/session-start.sh
```

## Related Files

- `.claude/settings.json` - Claude Code project settings
- `.claude/hooks/session-start.sh` - SessionStart hook script
- `.claude/hooks/file-index.py` - File index generator (still present, not deleted)
- `.devcontainer/ccweb/README.md` - CC Web environment documentation
